/*  4 bytes version
 *	Description:
 *		Configuring LoRa concentrator, send packets to remote transmitter on settable
 *		frequency, configure remote transmitter, record packets (accelerometer data)
 *		recived from transmitter to CSV file.
 */


/* -------------------------------------------------------------------------- */
/* --- DEPENDANCIES --------------------------------------------------------- */

/* fix an issue between POSIX and C99 */
#if __STDC_VERSION__ >= 199901L
#define _XOPEN_SOURCE 600
#else
#define _XOPEN_SOURCE 500
#endif

#include <stdint.h>     /* C99 types */
#include <stdbool.h>    /* bool type */
#include <stdio.h>      /* printf fprintf sprintf fopen fputs */

#include <string.h>     /* memset */
#include <signal.h>     /* sigaction */
#include <time.h>       /* time clock_gettime strftime gmtime clock_nanosleep*/
#include <unistd.h>     /* getopt access */
#include <stdlib.h>     /* exit codes */
#include <getopt.h>     /* getopt_long */

#include "parson.h"
#include "loragw_hal.h"
#include "loragw_reg.h"
#include "loragw_aux.h"


/* CRC */
#define WIDTH (8*4)
#define TOPBIT (1 << (WIDTH-1))
#define POLYNOMIAL (0x104C11DB7)

uint32_t crc_table(uint8_t n) {
	uint32_t c = ((uint32_t)n) << (WIDTH - 8);
	for(int i=8; i > 0; i--) {
		if(c & TOPBIT)
			c = (c<<1) ^ POLYNOMIAL;
		else
			c=c<<1;
	}
	return c;
}

uint32_t crc32(const uint8_t *buffer, uint32_t length) {
	uint32_t crc = 0xFFFFFFFF;
	for(uint32_t i = 0; i < length ; i++) {
		crc = crc_table(buffer[i] ^ ((crc >> 24) & 0xFF))^(crc << 8);
	}
	return crc ^ 0xFFFFFFFF;
}

/* -------------------------------------------------------------------------- */
/* --- PRIVATE MACROS ------------------------------------------------------- */

#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))
#define MSG(args...) fprintf(stderr, args) /* message that is destined to the user */

/* -------------------------------------------------------------------------- */
/* --- PRIVATE CONSTANTS ---------------------------------------------------- */

#define TX_RF_CHAIN                 0 /* TX only supported on radio A */
#define DEFAULT_RSSI_OFFSET         -166.0
#define DEFAULT_MODULATION          "LORA"
#define DEFAULT_BR_KBPS             50
#define DEFAULT_FDEV_KHZ            25
#define DEFAULT_NOTCH_FREQ          129000U /* 129 kHz */
#define DEFAULT_SX127X_RSSI_OFFSET  -4 /* dB */

#define PROG_BUF_SIZE 121
#define MAX_FILE_SIZE 70000

/* -------------------------------------------------------------------------- */
/* --- PRIVATE VARIABLES (GLOBAL) ------------------------------------------- */

/* signal handling variables */
struct sigaction sigact; /* SIGQUIT&SIGINT&SIGTERM signal handling */
static int exit_sig = 0; /* 1 -> application terminates cleanly (shut down hardware, close open files, etc) */
static int quit_sig = 0; /* 1 -> application terminates without shutting down the hardware */

/* configuration variables needed by the application  */
uint64_t lgwm = 123456789U; /* LoRa gateway MAC address */
char lgwm_str[17];
int sf = 8; /* SF8 by default */
int bw = 125; /* 125kHz bandwidth by default */
uint32_t f_target = 869120000U; /* transmitter control frequency */
uint32_t fprog_target = 869400000U; /* transmitter programming frequency */
uint32_t f_receiver = 864500000U; /* receiver frequency */
int chan_if[8] = {0}; //receiving channels frequency
uint16_t send_duration_ms = 0;
uint16_t receive_duration_ms = 0;
uint8_t transmitter_numbers = 0;	//each bit corresponding transmitter number

/* clock and log file management */
time_t now_time;
time_t log_start_time;
FILE * log_file[80] = {NULL};
bool is_logFileOpen = false;
char log_file_name[64];

/* TX gain LUT table */
static struct lgw_tx_gain_lut_s txgain_lut = {
	.size = 5,
	.lut[0] = {
		.dig_gain = 0,
		.pa_gain = 0,
		.dac_gain = 3,
		.mix_gain = 12,
		.rf_power = 0
	},
	.lut[1] = {
		.dig_gain = 0,
		.pa_gain = 1,
		.dac_gain = 3,
		.mix_gain = 12,
		.rf_power = 10
	},
	.lut[2] = {
		.dig_gain = 0,
		.pa_gain = 2,
		.dac_gain = 3,
		.mix_gain = 10,
		.rf_power = 14
	},
	.lut[3] = {
		.dig_gain = 0,
		.pa_gain = 3,
		.dac_gain = 3,
		.mix_gain = 9,
		.rf_power = 20
	},
	.lut[4] = {
		.dig_gain = 0,
		.pa_gain = 3,
		.dac_gain = 3,
		.mix_gain = 14,
		.rf_power = 27
	}
};


	/* RF configuration (TX fail if RF chain is not enabled) */
	enum lgw_radio_type_e radio_type = LGW_RADIO_TYPE_SX1257;
	uint8_t clocksource = 1; /* Radio B is source by default */
	struct lgw_conf_board_s boardconf;
	struct lgw_conf_lbt_s lbtconf;
	struct lgw_conf_rxrf_s rfconf;
	struct lgw_conf_rxif_s ifconf;

	/* allocate memory for packet sending */
	struct lgw_pkt_tx_s txpkt; /* array containing 1 outbound packet + metadata */

	/* allocate memory for packet fetching and processing */
	struct lgw_pkt_rx_s rxpkt[16]; /* array containing up to 16 inbound packets metadata */
	struct lgw_pkt_rx_s *p; /* pointer on a RX packet */
	int nb_pkt;

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS DECLARATION ---------------------------------------- */

static void sig_handler(int sigio);

void usage (void);

uint16_t time_interval_ms (struct timespec *time_point);

int parse_configuration(const char * conf_file);

void open_csv_log(void);

uint8_t wait_mess(uint8_t command, uint8_t tx_number);

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS DEFINITION ----------------------------------------- */

static void sig_handler(int sigio) {
	if (sigio == SIGQUIT) {
		quit_sig = 1;;
	} else if ((sigio == SIGINT) || (sigio == SIGTERM)) {
		exit_sig = 1;
	}
}

/* describe command line options */
void usage(void) {
	//int i;

	printf("LoRa library information: \n%s\n\n", lgw_version_info());
	printf("Usage example:\n");
	printf(" -Enable transmitters with numbers 1 to 5: util_acc_looger -e -n 1,2,3,4,5\n");
	printf(" -All enabled transmitters start transmitting: util_acc_looger -t\n");
	printf(" -Disable transmitters with numbers 1 to 5: util_acc_looger -d -n 1,2,3,4,5\n");
	printf("Available options:\n");
	printf(" -h                 print this help\n");
	printf(" -e                 enable transmitter and set it to ready mode\n");
	printf(" -t                 set all enabled transmitters to transmit data mode\n");
	printf(" -d                 disable transmitter and set it to standby mode\n");
	printf(" -с                 checking if the transmitter is in range of the hub\n");
	printf(" -n         <uint>  transmitter numbers are entered comma-separated 1,2,3,4,5,6,7,8]\n");
	printf(" -p                 program transmitter\n");
	/*printf(" -k         <uint>  concentrator clock source (0:Radio A, 1:Radio B)\n");
	printf(" -m         <str>   modulation type ['LORA', 'FSK']\n");
	printf(" -b         <uint>  LoRa bandwidth in kHz [125, 250, 500]\n");
	printf(" -s         <uint>  LoRa Spreading Factor [7-12]\n");
	printf(" -c         <uint>  LoRa Coding Rate [1-4]\n");
	printf(" -d         <uint>  FSK frequency deviation in kHz [1:250]\n");
	printf(" -q         <float> FSK bitrate in kbps [0.5:250]\n");
	printf(" -p         <int>   RF power (dBm) [ ");
	for (i = 0; i < txgain_lut.size; i++) {
	    printf("%ddBm ", txgain_lut.lut[i].rf_power);
	}
	printf("]\n");
	printf(" -l         <uint>  LoRa preamble length (symbols)\n");
	printf(" -z         <uint>  payload size (bytes, <256)\n");
	printf(" -i                 send packet using inverted modulation polarity\n");
	printf(" -t         <uint>  pause between packets (ms)\n");
	printf(" -x         <int>   nb of times the sequence is repeated (-1 loop until stopped)\n");
	printf(" --lbt-freq         <float> lbt first channel frequency in MHz\n");
	printf(" --lbt-nbch         <uint>  lbt number of channels [1..8]\n");
	printf(" --lbt-sctm         <uint>  lbt scan time in usec to be applied to all channels [128, 5000]\n");
	printf(" --lbt-rssi         <int>   lbt rssi target in dBm [-128..0]\n");
	printf(" --lbt-rssi-offset  <int>   rssi offset in dB to be applied to SX127x RSSI [-128..127]\n");*/
}

/* how many milli seconds last from start_point*/
uint16_t time_interval_ms (struct timespec *start_point) {
	struct timespec now_point;
	clock_gettime(CLOCK_REALTIME, &now_point);
	return (now_point.tv_sec - start_point->tv_sec) * 1000 + (now_point.tv_nsec - start_point->tv_nsec) / 1000000;
	//return 1;
}

int parse_configuration(const char * conf_file) {
	//int i;
	const char conf_obj[] = "concentrator_conf";
	//char param_name[32]; /* used to generate variable parameter names */
	//const char *str; /* used to store string value from JSON object */
	JSON_Value *root_val;
	JSON_Object *root = NULL;
	JSON_Object *conf = NULL;
	JSON_Value *val;

	/* try to parse JSON */
	root_val = json_parse_file_with_comments(conf_file);
	root = json_value_get_object(root_val);
	if (root == NULL) {
		MSG("ERROR: %s is not a valid JSON file\n", conf_file);
		exit(EXIT_FAILURE);
	}
	conf = json_object_get_object(root, conf_obj);
	if (conf == NULL) {
		MSG("INFO: %s does not contain a JSON object named %s\n", conf_file, conf_obj);
		return -1;
	} else {
		MSG("INFO: found JSON object named %s, parsing parameters\n", conf_obj);
	}

	/* set configuration bandwidth */
	val = json_object_get_value(conf, "bandwidth"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		bw = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for bandwidth seems wrong, please check\n");
	}
	/* set configuration SF */
	val = json_object_get_value(conf, "spread_factor"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		sf = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for spred factor seems wrong, please check\n");
	}
	/* set configuration control frequency */
	val = json_object_get_value(conf, "control_frequency"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		f_target = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for control_frequency seems wrong, please check\n");
	}
  /* set configuration programming frequency */
	val = json_object_get_value(conf, "programming_frequency"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		fprog_target = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for programming_frequency seems wrong, please check\n");
	}
	/* set configuration receiver frequency */
	val = json_object_get_value(conf, "receiver_frequency"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		f_receiver = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_0 receiver frequency */
	val = json_object_get_value(conf, "chan_0"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[0] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_0 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_1 receiver frequency */
	val = json_object_get_value(conf, "chan_1"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[1] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_1 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_2 receiver frequency */
	val = json_object_get_value(conf, "chan_2"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[2] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_2 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_3 receiver frequency */
	val = json_object_get_value(conf, "chan_3"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[3] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_3 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_4 receiver frequency */
	val = json_object_get_value(conf, "chan_4"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[4] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_4 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_5 receiver frequency */
	val = json_object_get_value(conf, "chan_5"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[5] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_5 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_6 receiver frequency */
	val = json_object_get_value(conf, "chan_6"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[6] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_6 receiver_frequency seems wrong, please check\n");
	}
	/* set configuration chan_7 receiver frequency */
	val = json_object_get_value(conf, "chan_7"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		chan_if[7] = (int)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for chan_7 receiver_frequency seems wrong, please check\n");
	}

	/* set send duration */
	val = json_object_get_value(conf, "cmd01_send_duration"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		send_duration_ms = (uint16_t)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for cmd01_send_duration seems wrong, please check\n");
	}

	/* set receive duration */
	val = json_object_get_value(conf, "cmd01_receive_duration"); /* fetch value (if possible) */
	if (json_value_get_type(val) == JSONNumber) {
		receive_duration_ms = (uint16_t)json_value_get_number(val);
	} else {
		MSG("WARNING: Data type for cmd01_receive_duration seems wrong, please check\n");
	}

	/*MSG("INFO: lorawan_public %d, clksrc %d\n", boardconf.lorawan_public, boardconf.clksrc);
	if (lgw_board_setconf(boardconf) != LGW_HAL_SUCCESS) {
	    MSG("ERROR: Failed to configure board\n");
	    return -1;
	}

	val = json_object_dotget_value(conf, param_name);
	    if (json_value_get_type(val) == JSONBoolean) {
	        rfconf.enable = (bool)json_value_get_boolean(val);
	    } else {
	        rfconf.enable = false;
	    }
	    if (rfconf.enable == false) {
	        MSG("INFO: radio %i disabled\n", i);
	    } else  {
	        snprintf(param_name, sizeof param_name, "radio_%i.freq", i);
	        rfconf.freq_hz = (uint32_t)json_object_dotget_number(conf, param_name);
	        snprintf(param_name, sizeof param_name, "radio_%i.rssi_offset", i);
	        rfconf.rssi_offset = (float)json_object_dotget_number(conf, param_name);
	        snprintf(param_name, sizeof param_name, "radio_%i.type", i);
	        str = json_object_dotget_string(conf, param_name);
	        if (!strncmp(str, "SX1255", 6)) {
	            rfconf.type = LGW_RADIO_TYPE_SX1255;
	        } else if (!strncmp(str, "SX1257", 6)) {
	            rfconf.type = LGW_RADIO_TYPE_SX1257;
	        } else {
	            MSG("WARNING: invalid radio type: %s (should be SX1255 or SX1257)\n", str);
	        }
	        snprintf(param_name, sizeof param_name, "radio_%i.tx_enable", i);
	        val = json_object_dotget_value(conf, param_name);
	        if (json_value_get_type(val) == JSONBoolean) {
	            rfconf.tx_enable = (bool)json_value_get_boolean(val);
	            if (rfconf.tx_enable == true) {

	                snprintf(param_name, sizeof param_name, "radio_%i.tx_notch_freq", i);
	                rfconf.tx_notch_freq = (uint32_t)json_object_dotget_number(conf, param_name);
	            }
	        } else {
	            rfconf.tx_enable = false;
	        }
	        MSG("INFO: radio %i enabled (type %s), center frequency %u, RSSI offset %f, tx enabled %d, tx_notch_freq %u\n", i, str, rfconf.freq_hz, rfconf.rssi_offset, rfconf.tx_enable, rfconf.tx_notch_freq);
	    }

	    if (lgw_rxrf_setconf(i, rfconf) != LGW_HAL_SUCCESS) {
	        MSG("ERROR: invalid configuration for radio %i\n", i);
	        return -1;
	    }*/

	json_value_free(root_val);
	return 0;
}

void open_csv_log(void) {
	//int i;
	int j;
	char iso_date[20];

	strftime(iso_date,ARRAY_SIZE(iso_date),"%Y-%m-%d_%H:%M:%S",gmtime(&now_time)); /* format yyyymmddThhmmssZ */
	log_start_time = now_time; /* keep track of when the log was started, for log rotation */

	for (j = 0; j < 8; ++j) {
		if ((transmitter_numbers & (1 << j)) == 1 << j) {
			printf("Open csv and log files for transmitter number %d\n", j + 1);
			sprintf(log_file_name, "%i_1_%s.csv", j + 1, iso_date);
			log_file[j * 4] = fopen(log_file_name, "a"); /* create csv file, append if file already exist */
			sprintf(log_file_name, "%i_1_%s.log", j + 1, iso_date);
			log_file[j * 4 + 1] = fopen(log_file_name, "a"); /* create log file, append if file already exist */
			sprintf(log_file_name, "%i_2_%s.csv", j + 1, iso_date);
			log_file[j * 4 + 2] = fopen(log_file_name, "a"); /* create csv file, append if file already exist */
			sprintf(log_file_name, "%i_2_%s.log", j + 1, iso_date);
			log_file[j * 4 + 3] = fopen(log_file_name, "a"); /* create log file, append if file already exist */
			//sprintf(log_file_name, "%i_Z_%s.csv", j + 1, iso_date);
			//log_file[j * 10 + 4] = fopen(log_file_name, "a"); /* create csv file, append if file already exist */
			//sprintf(log_file_name, "%i_Z_%s.log", j + 1, iso_date);
			//log_file[j * 10 + 5] = fopen(log_file_name, "a"); /* create log file, append if file already exist */
			//sprintf(log_file_name, "%i_t1_%s.csv", j + 1, iso_date);
			//log_file[j * 10 + 6] = fopen(log_file_name, "a"); /* create csv file, append if file already exist */
			//sprintf(log_file_name, "%i_t1_%s.log", j + 1, iso_date);
			//log_file[j * 10 + 7] = fopen(log_file_name, "a"); /* create log file, append if file already exist */
			//sprintf(log_file_name, "%i_t2_%s.csv", j + 1, iso_date);
			//log_file[j * 10 + 8] = fopen(log_file_name, "a"); /* create csv file, append if file already exist */
			//sprintf(log_file_name, "%i_t2_%s.log", j + 1, iso_date);
			//log_file[j * 10 + 9] = fopen(log_file_name, "a"); /* create log file, append if file already exist */
		}
	}
	/*sprintf(log_file_name, "pktlog_%s_%s.csv", lgwm_str, iso_date);
	log_file = fopen(log_file_name, "a");
	if (log_file == NULL) {
	    MSG("ERROR: impossible to create log file %s\n", log_file_name);
	    exit(EXIT_FAILURE);
	}

	i = fprintf(log_file, "\"gateway ID\",\"node MAC\",\"UTC timestamp\",\"us count\",\"frequency\",\"RF chain\",\"RX chain\",\"status\",\"size\",\"modulation\",\"bandwidth\",\"datarate\",\"coderate\",\"RSSI\",\"SNR\",\"payload\"\n");

	if (i < 0) {
	    MSG("ERROR: impossible to write to log file %s\n", log_file_name);
	    exit(EXIT_FAILURE);
	}*/
	is_logFileOpen = true;
	MSG("INFO: Now writing to csv and log files\n");
	return;
}

void close_csv_log(void) {
	int j;
	for (j = 0; j < 8; ++j) {
		if ((transmitter_numbers & (1 << j)) == 1 << j) {
			fclose(log_file[j * 4]);
			fclose(log_file[j * 4 + 1]);
			fclose(log_file[j * 4 + 2]);
			fclose(log_file[j * 4 + 3]);
			/*fclose(log_file[j * 10 + 4]);
			fclose(log_file[j * 10 + 5]);
			fclose(log_file[j * 10 + 6]);
			fclose(log_file[j * 10 + 7]);
			fclose(log_file[j * 10 + 8]);
			fclose(log_file[j * 10 + 9]);*/
		}
	}
	printf("Closing csv, log files\n");
	return;
}

uint8_t parse_bitaddres_to_number(uint8_t n) { //return number of transmitter by it's bit address (for address 00001000 return 4)
  for (uint8_t i = 0; i < 8; ++i) {
    if (n == (1 << i)) {
      return i + 1;
    }
  }
  return 0;
}
/************************************************************************
 * 
 * return 1 - received command from tx_number
 * 		  0  - otherwise
 * 		  2  - error
 * **********************************************************************/
uint8_t wait_mess(uint8_t command, uint8_t tx_number)
{
	bool flag;
	time_t time_point;
	/* to do: waiting command message*/
    time(&time_point);
    struct timespec sleep_time = {0, 3000000}; /* 3 ms */
    /* receive packet */
    flag = false;
   // received = 0;
    while (time(NULL) - time_point < 2 && (flag != true)) {
      //++cycle_count;

      /* fetch packets */
      nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
      if (nb_pkt == LGW_HAL_ERROR) {
        MSG("ERROR: failed packet fetch, exiting\n");
        return 2; //exit failure
      } else if (nb_pkt == 0) {
        clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
      } else {
        for (int i=0; i < nb_pkt; ++i) {
          p = &rxpkt[i];

          if (p->status != STAT_CRC_OK) {
            puts("\"CRC_ERROR\" ");
          }

          if (p->status == STAT_CRC_OK) {


            if (p->payload[0] == command) {
              if ((1 << (p->payload[1] - 1)) == tx_number) {
                
                flag = true;
                break;
              }
              //printf("rceived 0x0B");
            }
            puts("\"\n");
          }
        }
      }
    }
    if(flag != true)return 0;
    else return 1;
}

/* -------------------------------------------------------------------------- */
/* --- MAIN FUNCTION -------------------------------------------------------- */

int main(int argc, char **argv) {
	int i, j;
	uint8_t status_var;
	FILE *bfp; /*pointer to binary file*/
	size_t bfSize = 0;
	size_t bfSizeReal = 0;
	uint8_t bfBuff[MAX_FILE_SIZE];
	uint32_t bfCrc = 0;

	/* configuration file related */
	const char conf_file_name[] = "conf.json"; /* configuration file */

	struct timespec sleep_time = {0, 3000000}; /* 3 ms */

	/* user entry parameters */
	int xi = 0;
	//unsigned int xu = 0;
	//double xd = 0.0;
	//float xf = 0.0;
	//char arg_s[64];

	/* application parameters */
	char mod[64] = DEFAULT_MODULATION;
	int cr = 1; /* CR1 aka 4/5 by default */
	int pow = 8; /* 14 dBm by default */
	int preamb = 8; /* 8 symbol preamble by default */
	int pl_size = 3; /* 3 bytes payload by default */
	int delay = 1; /* 1ms second between packets by default */
	//int repeat = 1; /* by default, repeat until stopped */
	bool invert = false;
	float br_kbps = DEFAULT_BR_KBPS;
	uint8_t fdev_khz = DEFAULT_FDEV_KHZ;
	bool lbt_enable = false;
	uint32_t lbt_f_target = 0;
	uint32_t lbt_sc_time = 5000;
	int8_t lbt_rssi_target_dBm = -80;
	int8_t lbt_rssi_offset_dB = DEFAULT_SX127X_RSSI_OFFSET;
	uint8_t  lbt_nb_channel = 1;
	//uint32_t sx1301_count_us;
	uint32_t tx_notch_freq = DEFAULT_NOTCH_FREQ;
	char action_flag = '0'; //action (enable, transmit or disable) corresponding to user argv
	uint8_t transmitter_numbers_reply = 0; //transmitter numbers that are reply for received command
	//int16_t received_value_x = 0;
	//int16_t received_value_y = 0;
	//int16_t received_value_z = 0;


	/* local timestamp variables until we get accurate GPS time */
	struct timespec fetch_time;
	struct timespec log_time_point[8];  //time point to check if write to log needed
	char fetch_timestamp[36];
	struct tm * x;

	/* loop variables (also use as counters in the packet payload) */
	uint32_t cycle_count = 0;
	uint32_t pkt_count = 0;

	/* Parameter parsing */
	//int option_index = 0;

	//test block
	/*puts("begin");
	clock_gettime(CLOCK_REALTIME, &fetch_time);
	while (time_interval_ms(&fetch_time) < 500) {

	}
	puts("end");*/

	/* parse command line options */
	if (argc < 2) {
		MSG("ERROR: argument parsing\n\n");
		usage();
		return EXIT_FAILURE;
	}

	while ((i = getopt (argc, argv, "hetdcpn:")) != -1) {
		char *p_ch;
		switch (i) {
		case 'h':
			usage();
			return EXIT_FAILURE;
			break;

		case 'e':
			action_flag = 'e';
			break;

		case 't':
			action_flag = 't';
			break;

		case 'd':
			action_flag = 'd';
			break;

		case 'c':
			action_flag = 'c';
			break;

		case 'p':
			action_flag = 'p';
			bfp = fopen("program.bin", "rb");
			if (bfp == NULL) {
				MSG("ERROR: not found program.bin\n");
				return EXIT_FAILURE;
			}
			//get file size
			fseek(bfp, 0, SEEK_END);
			bfSizeReal = ftell(bfp);
			if(bfSizeReal%(PROG_BUF_SIZE-1))bfSize = (bfSizeReal/(PROG_BUF_SIZE-1) + 1)*(PROG_BUF_SIZE-1);  //make multiple of (PROG_BUF_SIZE-1)
			else bfSize = bfSizeReal;
			rewind(bfp);
			MSG("file size - %d\n",bfSizeReal);
			MSG("sending buffer size - %d\n",bfSize);
			
			if (bfSize > MAX_FILE_SIZE) {
				MSG("ERROR: can't allocate memory for program.bin file\n");
				return EXIT_FAILURE;
			}

			if (fread(bfBuff, 1, bfSizeReal, bfp) != bfSizeReal) {
				MSG("ERROR: file reading error");
				return EXIT_FAILURE;
			}

			fclose(bfp);
			
/*********************fill buffer with 1 for debugging           **/
			//bfSize = (PROG_BUF_SIZE - 1)*10;
			//j = 0;
			//for(i = 0; i < bfSize; i++)
			//{
				//bfBuff[i] = j;
				//if(++j == PROG_BUF_SIZE - 1)j = 0;
			//}
/*******************************end debug section              ****/
			bfCrc = crc32(bfBuff, bfSize);
			/*bfSize = 258;
			uint8_t b1 = (uint8_t) bfSize;
			uint8_t b2 = (uint8_t) (bfSize >> 8);
			printf("bfs=%u b1=%u, b2=%u", bfSize, b1, b2);*/
			break;

		case 'n': /* <uint> transmitter numbers space-separated */
			p_ch = strtok(optarg, ",");
			while (p_ch != NULL /*i = sscanf(optarg, "%i", &xi) != -1*/) {
				i = sscanf(p_ch, "%i", &xi);
				if ((i != 1) || ((xi < 1) || (xi > 8))) {
					MSG("ERROR: invalid transmitter number\n");
					usage();
					return EXIT_FAILURE;
				} else {
					//printf("p_ch=%s\n", pch);
					p_ch = strtok('\0', ", ");
					transmitter_numbers |= 1 << (xi - 1);
					//printf("t_n=%d", transmitter_numbers);
					//MSG("\n");
				}
			}
			break;

		default:
			MSG("ERROR: argument parsing\n");
			usage();
			return EXIT_FAILURE;
		}
	}

	/* parse configuration file */
	if (access(conf_file_name, R_OK) == 0) {
		MSG("INFO: found configuration file %s\n", conf_file_name);
		parse_configuration(conf_file_name);
	} else {
		MSG("ERROR: failed to find configuration file named %s\n", conf_file_name);
		return EXIT_FAILURE;
	}

	/* check parameter sanity */
	if (f_target == 0) {
		MSG("ERROR: frequency parameter not set, please use -f option to specify it.\n");
		return EXIT_FAILURE;
	}
	if (radio_type == LGW_RADIO_TYPE_NONE) {
		MSG("ERROR: radio type parameter not properly set, please use -r option to specify it.\n");
		return EXIT_FAILURE;
	}

	/* Summary of packet parameters */
	printf("Configuration parameters: TX frequency %u Hz, Bandwidth %i kHz, SF %i\n", f_target, bw, sf);
	printf("Programming frequency %u\n", fprog_target);

	/* configure signal handling */
	sigemptyset(&sigact.sa_mask);
	sigact.sa_flags = 0;
	sigact.sa_handler = sig_handler;
	sigaction(SIGQUIT, &sigact, NULL);
	sigaction(SIGINT, &sigact, NULL);
	sigaction(SIGTERM, &sigact, NULL);

	/* starting the concentrator */
	/* board config */
	memset(&boardconf, 0, sizeof(boardconf));
	boardconf.lorawan_public = true;
	boardconf.clksrc = clocksource;
	lgw_board_setconf(boardconf);

	/* LBT config */
	if (lbt_enable) {
		memset(&lbtconf, 0, sizeof(lbtconf));
		lbtconf.enable = true;
		lbtconf.nb_channel = lbt_nb_channel;
		lbtconf.rssi_target = lbt_rssi_target_dBm;
		lbtconf.rssi_offset = lbt_rssi_offset_dB;
		lbtconf.channels[0].freq_hz = lbt_f_target;
		lbtconf.channels[0].scan_time_us = lbt_sc_time;
		for (i=1; i<lbt_nb_channel; i++) {
			lbtconf.channels[i].freq_hz = lbtconf.channels[i-1].freq_hz + 200E3; /* 200kHz offset for all channels */
			lbtconf.channels[i].scan_time_us = lbt_sc_time;
		}
		lgw_lbt_setconf(lbtconf);
	}

	/* RF config */
	memset(&rfconf, 0, sizeof(rfconf));
	rfconf.enable = true;
	//rfconf.freq_hz = f_target;
	rfconf.rssi_offset = DEFAULT_RSSI_OFFSET;
	rfconf.type = radio_type;
	for (i = 0; i < LGW_RF_CHAIN_NB; i++) {
		if (i == TX_RF_CHAIN) {
			rfconf.tx_enable = true;
			rfconf.tx_notch_freq = tx_notch_freq;
			rfconf.freq_hz = f_target;
		} else {
			rfconf.tx_enable = false;
			rfconf.freq_hz = f_receiver;
		}
		lgw_rxrf_setconf(i, rfconf);
	}

	/* TX gain config */
	lgw_txgain_setconf(&txgain_lut);

	/* set configuration for LoRa multi-SF channels (bandwidth cannot be set) */
	for (i = 0; i < LGW_MULTI_NB; ++i) {
		memset(&ifconf, 0, sizeof(ifconf)); /* initialize configuration structure */
		if (true) {
			ifconf.enable = true;
			ifconf.rf_chain = 1;
			switch (i) {
			case 0:
				ifconf.freq_hz = chan_if[0]; //-400000;
				break;
			case 1:
				ifconf.freq_hz = chan_if[1]; //-200000;
				break;
			case 2:
				ifconf.freq_hz = chan_if[2]; //0;
				break;
			case 3:
				ifconf.freq_hz = chan_if[3]; //140000;
				break;
			case 4:
				ifconf.freq_hz = chan_if[4]; //280000;
				break;
			case 5:
				ifconf.freq_hz = chan_if[5]; //320000;
				break;
			case 6:
				ifconf.freq_hz = chan_if[6]; //350000;
				break;
			case 7:
				ifconf.freq_hz = chan_if[7]; //400000;
				break;
			}

		} else {
			//sprintf(param_name, "chan_multiSF_%i", i); /* compose parameter path inside JSON structure */
			//val = json_object_get_value(conf, param_name); /* fetch value (if possible) */
			//if (json_value_get_type(val) != JSONObject) {
			//    MSG("INFO: no configuration for LoRa multi-SF channel %i\n", i);
			//    continue;
			//}
			/* there is an object to configure that LoRa multi-SF channel, let's parse it */
			//sprintf(param_name, "chan_multiSF_%i.enable", i);
			//val = json_object_dotget_value(conf, param_name);
			//if (json_value_get_type(val) == JSONBoolean) {
			//    ifconf.enable = (bool)json_value_get_boolean(val);
			//} else {
			//    ifconf.enable = false;
			//}
			//if (ifconf.enable == false) { /* LoRa multi-SF channel disabled, nothing else to parse */
			//    MSG("INFO: LoRa multi-SF channel %i disabled\n", i);
			//} else  { /* LoRa multi-SF channel enabled, will parse the other parameters */
			//    sprintf(param_name, "chan_multiSF_%i.radio", i);
			//    ifconf.rf_chain = (uint32_t)json_object_dotget_number(conf, param_name);
			//    sprintf(param_name, "chan_multiSF_%i.if", i);
			//    ifconf.freq_hz = (int32_t)json_object_dotget_number(conf, param_name);
			//    // TODO: handle individual SF enabling and disabling (spread_factor)
			//    MSG("INFO: LoRa multi-SF channel %i enabled, radio %i selected, IF %i Hz, 125 kHz bandwidth, SF 7 to 12\n", i, ifconf.rf_chain, ifconf.freq_hz);
			//}
		}

		/* all parameters parsed, submitting configuration to the HAL */
		if (lgw_rxif_setconf(i, ifconf) != LGW_HAL_SUCCESS) {
			MSG("ERROR: invalid configuration for Lora multi-SF channel %i\n", i);
			return -1;
		}
	}

	/* set configuration for LoRa standard channel */
	memset(&ifconf, 0, sizeof(ifconf)); /* initialize configuration structure */
	ifconf.enable = true;
	ifconf.rf_chain = 0;
	ifconf.freq_hz = 280000;
	ifconf.bandwidth = BW_250KHZ;
	//ifconf.bandwidth = BW_UNDEFINED;
	ifconf.datarate = DR_LORA_SF7;
	//ifconf.datarate = DR_UNDEFINED;
	if (lgw_rxif_setconf(8, ifconf) != LGW_HAL_SUCCESS) {
		MSG("ERROR: invalid configuration for Lora standard channel\n");
		return -1;
	}

	/* set configuration for FSK channel */
	memset(&ifconf, 0, sizeof(ifconf)); /* initialize configuration structure */
	ifconf.enable = false;
	//ifconf.rf_chain = 1;
	//ifconf.freq_hz = 500000;
	//ifconf.bandwidth = BW_125KHZ;
	//ifconf.bandwidth = BW_UNDEFINED;
	//ifconf.datarate = 50000;
	if (lgw_rxif_setconf(9, ifconf) != LGW_HAL_SUCCESS) {
		MSG("ERROR: invalid configuration for FSK channel\n");
		return -1;
	}

	/* Start concentrator */
	cycle_count = 0;
	wait_ms(250);
	while (lgw_start() != LGW_HAL_SUCCESS) {
		cycle_count++;
		wait_ms(300); /*RF set config error if no delay)*/
		if (cycle_count == 10) {
			MSG("ERROR: failed to start the concentrator\n");
			return EXIT_FAILURE;
		}
		//i = lgw_start();
		/*if (i == LGW_HAL_SUCCESS) {
		  MSG("INFO: concentrator started, packet can be sent\n");
		} else {
		  MSG("ERROR: failed to start the concentrator\n");
		  return EXIT_FAILURE;
		}*/
	}

	/* fill-up payload and parameters */
	memset(&txpkt, 0, sizeof(txpkt));
	txpkt.freq_hz = f_target;
	if (lbt_enable == true) {
		txpkt.tx_mode = TIMESTAMPED;
	} else {
		txpkt.tx_mode = IMMEDIATE;
	}
	txpkt.rf_chain = TX_RF_CHAIN;
	txpkt.rf_power = pow;
	if( strcmp( mod, "FSK" ) == 0 ) {
		txpkt.modulation = MOD_FSK;
		txpkt.datarate = br_kbps * 1e3;
		txpkt.f_dev = fdev_khz;
	} else {
		txpkt.modulation = MOD_LORA;
		switch (bw) {
		case 125:
			txpkt.bandwidth = BW_125KHZ;
			break;
		case 250:
			txpkt.bandwidth = BW_250KHZ;
			break;
		case 500:
			txpkt.bandwidth = BW_500KHZ;
			break;
		default:
			MSG("ERROR: invalid 'bw' variable\n");
			return EXIT_FAILURE;
		}
		switch (sf) {
		case  7:
			txpkt.datarate = DR_LORA_SF7;
			break;
		case  8:
			txpkt.datarate = DR_LORA_SF8;
			break;
		case  9:
			txpkt.datarate = DR_LORA_SF9;
			break;
		case 10:
			txpkt.datarate = DR_LORA_SF10;
			break;
		case 11:
			txpkt.datarate = DR_LORA_SF11;
			break;
		case 12:
			txpkt.datarate = DR_LORA_SF12;
			break;
		default:
			MSG("ERROR: invalid 'sf' variable\n");
			return EXIT_FAILURE;
		}
		switch (cr) {
		case 1:
			txpkt.coderate = CR_LORA_4_5;
			break;
		case 2:
			txpkt.coderate = CR_LORA_4_6;
			break;
		case 3:
			txpkt.coderate = CR_LORA_4_7;
			break;
		case 4:
			txpkt.coderate = CR_LORA_4_8;
			break;
		default:
			MSG("ERROR: invalid 'cr' variable\n");
			return EXIT_FAILURE;
		}
	}
	txpkt.invert_pol = invert;
	txpkt.preamble = preamb;
	txpkt.size = pl_size;

	/* set payload to send command packet */
	switch (action_flag) {
	case 'e':
		txpkt.payload[0] = 0x01;
		txpkt.payload[1] = transmitter_numbers;
		break;
	case 't':
		txpkt.payload[0] = 0x03;
		txpkt.payload[1] = transmitter_numbers;
		break;
	case 'd':
		txpkt.payload[0] = 0x04;
		txpkt.payload[1] = transmitter_numbers;
		break;
	case 'c':
		txpkt.payload[0] = 0x06;
		txpkt.payload[1] = transmitter_numbers;
		break;
	case 'p':
		txpkt.payload[0] = 0x08;
		txpkt.payload[1] = transmitter_numbers;
		break;
	}

	/* main loop */
	cycle_count = 0;
	time_t time_point;

	if (action_flag == 'e') {
		/* continuous transmitting enable command for 2000 msec*/
		printf("Sending enable command to selected transmitters for %d msec\n", send_duration_ms);
		clock_gettime(CLOCK_REALTIME, &fetch_time);
		while (time_interval_ms(&fetch_time) < send_duration_ms) {
			/* send packet */
			i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
			if (i == LGW_HAL_ERROR) {
				printf("ERROR\n");
				return EXIT_FAILURE;
			} else {
				/* wait for packet to finish sending */
				do {
					wait_ms(5);
					lgw_status(TX_STATUS, &status_var); /* get TX status */
				} while (status_var != TX_FREE);
				/*printf("OK\n");*/
			}
			/* wait inter-packet delay */
			wait_ms(delay);
		}

		//time(&time_point);
		/* receive packet */
		clock_gettime(CLOCK_REALTIME, &fetch_time);
		while (time_interval_ms(&fetch_time) < receive_duration_ms) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				/* local timestamp generation until we get accurate GPS time */
				//clock_gettime(CLOCK_REALTIME, &fetch_time);
				//x = gmtime(&(fetch_time.tv_sec));
				//sprintf(fetch_timestamp,"%04i-%02i-%02i %02i:%02i:%02i.%04liZ",(x->tm_year)+1900,(x->tm_mon)+1,x->tm_mday,x->tm_hour,x->tm_min,x->tm_sec, ((fetch_time.tv_nsec)/1000000)); /* ISO 8601 format */
			}

			for (i=0; i < nb_pkt; ++i) {
				p = &rxpkt[i];
				if (p->status == STAT_CRC_OK) {

					/* writing UTC timestamp*/
					printf("\"%s\",", fetch_timestamp);
					// TODO: replace with GPS time when available

					/* writing RX frequency */
					printf("%10u,", p->freq_hz);

					/* writing RF chain */
					printf("%u,", p->rf_chain);

					/* writing RX modem/IF chain */
					printf("%2d,", p->if_chain);

					/* writing status */
					switch(p->status) {
					case STAT_CRC_OK:
						puts("\"CRC_OK\" ,");
						break;
					case STAT_CRC_BAD:
						puts("\"CRC_BAD\",");
						break;
					case STAT_NO_CRC:
						puts("\"NO_CRC\" ,");
						break;
					case STAT_UNDEFINED:
						puts("\"UNDEF\"  ,");
						break;
					default:
						puts("\"ERR\"    ,");
					}

					/* writing packet RSSI */
					printf("%+.0f,", p->rssi);

					/* writing packet average SNR */
					//fprintf(log_file, "%+5.1f,", p->snr);

					/* writing hex-encoded payload (bundled in 32-bit words) */
					puts(" ");
					for (j = 0; j < p->size; ++j) {
						if ((j > 0) && (j%5 == 0))
							puts("-");
						printf("%02X", p->payload[j]);
					}
					if (p->payload[0] == 2) {
						transmitter_numbers_reply |= p->payload[1];
					}

					/* end of log file line */
					puts("\n");
					//fflush(log_file);
					//++pkt_in_log;
				}
			}
		}

		/* parse transmitter numbers reply */
		for (j = 0; j < 8; ++j) {
			if ((transmitter_numbers_reply & (1 << j)) == 1 << j) {
				printf("Transmitter number %d accept command\n", j + 1);
			}
		}

	} else if (action_flag == 't') {
		/* single send transmit-data command*/
		/* send packet */
		printf("Sending set transmit mode command to selected transmitters ...");
		i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
		if (i == LGW_HAL_ERROR) {
			printf("ERROR\n");
			return EXIT_FAILURE;
		} else {
			/* wait for packet to finish sending */
			do {
				wait_ms(5);
				lgw_status(TX_STATUS, &status_var); /* get TX status */
			} while (status_var != TX_FREE);
			printf("OK\n");
		}
		/* wait inter-packet delay */
		wait_ms(delay);

		time(&time_point);
		/* receive packet */
		printf("Waiting reply from all transmitters..\n");
		//while (time(NULL) - time_point < 3) {
		while ((quit_sig != 1) && (exit_sig != 1)) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
				//check if 5sec past from last packet receive
				for (int k = 0; k < 8; ++k) {
					if ((transmitter_numbers & (1 << k)) == 1 << k) {
						if (time_interval_ms(&log_time_point[k]) > 5000) {
							if (is_logFileOpen) {
								clock_gettime(CLOCK_REALTIME, &fetch_time);
								x = gmtime(&(fetch_time.tv_sec));
								sprintf(fetch_timestamp,"%04i-%02i-%02i %02i:%02i:%02i",(x->tm_year)+1900,(x->tm_mon)+1,x->tm_mday,x->tm_hour,x->tm_min,x->tm_sec); /* ISO 8601 format */
								fprintf(log_file[4 * k + 1], "%s ", fetch_timestamp);
								fputs("no data\n", log_file[4 * k + 1]);
								fprintf(log_file[4 * k + 3], "%s ", fetch_timestamp);
								fputs("no data\n", log_file[4 * k + 3]);
								/*fprintf(log_file[10 * k + 5], "%s ", fetch_timestamp);
								fputs("no data\n", log_file[10 * k + 5]);*/
								//update log timer to wait 5sec again if no packets received
								clock_gettime(CLOCK_REALTIME, &log_time_point[k]);
							}
						}
					}
					//time_interval_ms(&fetch_time) <
				}
			} else {
				/* local timestamp generation until we get accurate GPS time */
				clock_gettime(CLOCK_REALTIME, &fetch_time);
				x = gmtime(&(fetch_time.tv_sec));
				sprintf(fetch_timestamp,"%04i-%02i-%02i %02i:%02i:%02i.%04liZ",(x->tm_year)+1900,(x->tm_mon)+1,x->tm_mday,x->tm_hour,x->tm_min,x->tm_sec, ((fetch_time.tv_nsec)/1000000)); /* ISO 8601 format */
			}

			for (i=0; i < nb_pkt; ++i) {
				p = &rxpkt[i];
				if (transmitter_numbers_reply != transmitter_numbers) { //check if all transmitters reply
					if ((p->status == STAT_CRC_OK) && ((transmitter_numbers & (1 << p->if_chain)) == 1 << p->if_chain)) {
						transmitter_numbers_reply |= 1 << p->if_chain;
						printf("Waiting reply from all transmitters..\n");
					}
				} else { //all transmitters reply and we are ready to log csv files
					if (!is_logFileOpen) {
						time(&now_time);
						open_csv_log();
						for (int k = 0; k < 8; ++k) {
							clock_gettime(CLOCK_REALTIME, &log_time_point[k]);
						}
					}
					if ((transmitter_numbers & (1 << p->if_chain)) == 1 << p->if_chain) { //if received packed from requested transmitters, and not from any other
						//uint8_t llv[40];
						//uint8_t ii = 0;
						//uint8_t ii_t = 0;
						uint8_t bv = 0;
						//bool isTempPresent = false;

						if (p->status == STAT_CRC_OK) {
							++pkt_count;
							int16_t val_t1 = 0;
							int16_t val_t2 = 0;
							//update log timer if packet from transmitter received
							clock_gettime(CLOCK_REALTIME, &log_time_point[p->if_chain]);
							// parse bits from received values
							for (j = 0; j < p->size; ++j) {
								bv = p->payload[j];
								switch (j) {
								case 0:
									val_t1 = bv;
									break;
								case 1:
									val_t1 |= bv << 8;
									break;
								case 2:
									val_t2 = bv;
									break;
								case 3:
									val_t2 |= bv << 8;
									break;

								}

								//printf("x=%d, y=%d, z=%d\n", received_value_x, received_value_y, received_value_z);
								//printf("llv[%i]=%i ", k, llv[k]);

								//fprintf(log_file[10 * p->if_chain + 4], "%i,", received_value_z);
								//ii = 0;

								//puts("-");

							}
							fprintf(log_file[4 * p->if_chain], "%i,", val_t1);
							fprintf(log_file[4 * p->if_chain + 2], "%i,", val_t2);

						}

						/* writing packet RSSI */
						//printf("RSSI %+.0f,", p->rssi);

						/* writing packet average SNR */
						//fprintf(log_file, "%+5.1f,", p->snr);

						/* writing hex-encoded payload (bundled in 32-bit words) */
						printf("Receive packet number %d\n", pkt_count);
						/*for (j = 0; j < p->size; ++j) {
						    if ((j > 0) && (j%5 == 0)) puts("-");
						    printf("%02X", p->payload[j]);
						}*/
						/*if (p->payload[0] == 2) {
						  transmitter_numbers_reply |= p->payload[1];
						}*/

						/* end of log file line */
						//puts("\"\n");
						//fflush(log_file);
						//++pkt_in_log;
					}
				}
			}
		}
		if (is_logFileOpen) {
			close_csv_log();
		}

		/* parse transmitter numbers reply */
		/*for (j = 0; j < 8; ++j) {
		  if ((transmitter_numbers_reply & (1 << j)) == 1 << j) {
		    printf("Transmitter number %d accept command\n", j);
		  }
		}*/


	} else if (action_flag == 'd') {
		/* single send transmit-data command*/
		/* send packet */
		printf("Sending disable transmit mode command and set selected transmitters in to standby mode");
		i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
		if (i == LGW_HAL_ERROR) {
			printf("ERROR\n");
			return EXIT_FAILURE;
		} else {
			/* wait for packet to finish sending */
			do {
				wait_ms(5);
				lgw_status(TX_STATUS, &status_var); /* get TX status */
			} while (status_var != TX_FREE);
			printf("OK\n");
		}
		/* wait inter-packet delay */
		wait_ms(delay);

		time(&time_point);
		/* receive packet */
		while (time(NULL) - time_point < 2) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				/* local timestamp generation until we get accurate GPS time */
				clock_gettime(CLOCK_REALTIME, &fetch_time);
				x = gmtime(&(fetch_time.tv_sec));
				sprintf(fetch_timestamp,"%04i-%02i-%02i %02i:%02i:%02i.%04liZ",(x->tm_year)+1900,(x->tm_mon)+1,x->tm_mday,x->tm_hour,x->tm_min,x->tm_sec, ((fetch_time.tv_nsec)/1000000)); /* ISO 8601 format */
			}

			for (i=0; i < nb_pkt; ++i) {
				p = &rxpkt[i];

				if (p->status != STAT_CRC_OK) {
					puts("\"CRC_ERROR\" ");
				}

				if (p->status == STAT_CRC_OK) {

					/* writing packet RSSI */
					printf("%+.0f,", p->rssi);

					/* writing packet average SNR */
					//fprintf(log_file, "%+5.1f,", p->snr);

					/* writing hex-encoded payload (bundled in 32-bit words) */
					puts("\"");
					for (j = 0; j < p->size; ++j) {
						if ((j > 0) && (j%5 == 0))
							puts("-");
						printf("%02X", p->payload[j]);
					}

					if (p->payload[0] == 5) {
						transmitter_numbers_reply |= p->payload[1];
					}

					/* end of log file line */
					puts("\"\n");
					//fflush(log_file);
					//++pkt_in_log;
				}
			}
		}

		/* parse transmitter numbers reply */
		for (j = 0; j < 8; ++j) {
			if ((transmitter_numbers_reply & (1 << j)) == 1 << j) {
				printf("Transmitter number %d accept command\n", j + 1);
			}
		}

	} else if (action_flag == 'c') {
		/* single send check in range command*/
		/* send packet */
		printf("Sending check in range command");
		clock_gettime(CLOCK_REALTIME, &fetch_time);
		while (time_interval_ms(&fetch_time) < send_duration_ms) {
			/* send packet */
			i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
			if (i == LGW_HAL_ERROR) {
				printf("ERROR\n");
				return EXIT_FAILURE;
			} else {
				/* wait for packet to finish sending */
				do {
					wait_ms(5);
					lgw_status(TX_STATUS, &status_var); /* get TX status */
				} while (status_var != TX_FREE);
				/*printf("OK\n");*/
			}
			/* wait inter-packet delay */
			wait_ms(delay);
		}
		printf("OK\n");

		/* wait inter-packet delay */
		wait_ms(delay);

		time(&time_point);
		/* receive packet */
		while (time(NULL) - time_point < 2) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				/* local timestamp generation until we get accurate GPS time */
				clock_gettime(CLOCK_REALTIME, &fetch_time);
				x = gmtime(&(fetch_time.tv_sec));
				sprintf(fetch_timestamp,"%04i-%02i-%02i %02i:%02i:%02i.%04liZ",(x->tm_year)+1900,(x->tm_mon)+1,x->tm_mday,x->tm_hour,x->tm_min,x->tm_sec, ((fetch_time.tv_nsec)/1000000)); /* ISO 8601 format */
			}

			for (i=0; i < nb_pkt; ++i) {
				p = &rxpkt[i];

				if (p->status != STAT_CRC_OK) {
					puts("\"CRC_ERROR\" ");
				}

				if (p->status == STAT_CRC_OK) {

					/* writing packet RSSI */
					printf("%+.0f,", p->rssi);

					/* writing packet average SNR */
					//fprintf(log_file, "%+5.1f,", p->snr);

					/* writing hex-encoded payload (bundled in 32-bit words) */
					puts("\"");
					for (j = 0; j < p->size; ++j) {
						if ((j > 0) && (j%5 == 0))
							puts("-");
						printf("%02X", p->payload[j]);
					}

					if (p->payload[0] == 7) {
						transmitter_numbers_reply |= p->payload[1];
					}
					puts("\"\n");
				}
			}
		}

		/* parse transmitter numbers reply */
		for (j = 0; j < 8; ++j) {
			if ((transmitter_numbers_reply & (1 << j)) == 1 << j) {
				printf("Transmitter number %d accept command\n", j + 1);
			}
		}
	} else if (action_flag == 'p') { //programming device
		/* waiting 15sec for any message from selected transmitter */
		/* receive packet */
		time(&time_point);
		printf("waiting any packet from selected transmitter..\n");
		bool flag_received_reply = false;
		while (/*(time(NULL) - time_point < 15) && */(flag_received_reply != true)) {
			//++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				for (i=0; i < nb_pkt; ++i) {
					p = &rxpkt[i];
					if (p->status == STAT_CRC_OK) {
						/* writing UTC timestamp*/
						printf("\"%s\",", fetch_timestamp);
						// TODO: replace with GPS time when available

						/* writing RX frequency */
						printf("%10u,", p->freq_hz);

						/* writing RF chain */
						printf("%u,", p->rf_chain);

						/* writing RX modem/IF chain */
						printf("%2d,", p->if_chain); /* num of receiving interface from 0, i.e. if_chain+1 = num_of_transmitter*/

						/* writing packet RSSI */
						printf("%+.0f,", p->rssi);

						if (transmitter_numbers == 1 << p->if_chain) {
							puts("\n.. received reply from selected transmitter\n");
							flag_received_reply = true;
							break;
						}
						puts("\n");
					}
				}
			}
		}

		if (flag_received_reply != true) {
			MSG("ERROR: not received any packet from selected transmitter, exiting\n");
			return EXIT_FAILURE;
		}
		//lgw_stop();
		//printf("Exiting program\n");
		//return EXIT_SUCCESS;

		/* single send request programming command 0x08*/
		/* send packet */
		printf("\nSending 0x08 command to selected transmitter ...\n\n");
		i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
		if (i == LGW_HAL_ERROR) {
			printf("ERROR\n");
			return EXIT_FAILURE;
		} else {
			/* wait for packet to finish sending */
			do {
				wait_ms(2);
				lgw_status(TX_STATUS, &status_var); /* get TX status */
			} while (status_var != TX_FREE);
			printf("OK\n");
		}
		/* wait inter-packet delay */
		//wait_ms(delay);

		/* wait for reply command 0x09*/
		time(&time_point);
		/* receive packet */
		flag_received_reply = false;
		uint8_t received_reply_from = 0;
		while (time(NULL) - time_point < 2 && (flag_received_reply != true)) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				for (i=0; i < nb_pkt; ++i) {
					p = &rxpkt[i];

					if (p->status != STAT_CRC_OK) {
						puts("\"CRC_ERROR\" ");
					}

					if (p->status == STAT_CRC_OK) {

						/* writing packet RSSI */
						//printf("%+.0f\n", p->rssi);

						//if ((p->payload[0] == 9) && (p->payload[1] == parse_bitaddres_to_number(transmitter_numbers))) {
						if ((p->payload[0] == 9) && (transmitter_numbers == (1 << (p->payload[1] - 1)))) {
							transmitter_numbers_reply = p->payload[1];
							flag_received_reply = true;
							received_reply_from = p->if_chain + 1;
							break;
						}
						puts("\"\n");
					}
				}
			}
		}

		if (flag_received_reply != true) {
			//MSG("ERROR: not received 0x09 command from selected transmitter, exiting\n");
			MSG("no answer\n");
			return EXIT_FAILURE;
		}
		/* parse transmitter numbers reply */
		if (transmitter_numbers_reply != 0) {
			printf("N%d ready\n", transmitter_numbers_reply /*received_reply_from*/);
		} else {
			MSG("ERROR: received 0x09 command but selected more than one transmitter, exiting\n");
			return EXIT_FAILURE;
		}


		//change freq to 869.4MHz (programming)
		lgw_stop();

		memset(&rfconf, 0, sizeof(rfconf));
		rfconf.enable = true;
		rfconf.freq_hz = fprog_target;
		rfconf.rssi_offset = DEFAULT_RSSI_OFFSET;
		rfconf.type = radio_type;
		rfconf.tx_enable = true;
		rfconf.tx_notch_freq = tx_notch_freq;
		lgw_rxrf_setconf(0, rfconf);

		/* Start concentrator */
		cycle_count = 0;
		while (lgw_start() != LGW_HAL_SUCCESS) {
			cycle_count++;
			wait_ms(300); /*RF set config error if no delay)*/
			if (cycle_count == 10) {
				MSG("ERROR: failed to start the concentrator\n");
				return EXIT_FAILURE;
			}
		}
		MSG("INFO: concentrator started, packet can be sent\n");

		/* fill-up payload and parameters */
		memset(&txpkt, 0, sizeof(txpkt));
		txpkt.freq_hz = fprog_target; //869400000U;
		txpkt.tx_mode = IMMEDIATE;
		txpkt.rf_chain = TX_RF_CHAIN;
		txpkt.rf_power = pow;
		txpkt.modulation = MOD_LORA;
		txpkt.bandwidth = BW_250KHZ;
		txpkt.datarate = DR_LORA_SF7;
		txpkt.coderate = CR_LORA_4_5;
		txpkt.invert_pol = invert;
		txpkt.preamble = preamb;
		txpkt.size = PROG_BUF_SIZE + 4;//+crc

		txpkt.payload[0] = 0x0A;
		txpkt.payload[1] = transmitter_numbers;
		txpkt.payload[2] = (uint8_t) bfSize;
		txpkt.payload[3] = (uint8_t) (bfSize >> 8);
		txpkt.payload[4] = (uint8_t) bfCrc;
		txpkt.payload[5] = (uint8_t) (bfCrc >> 8);
		txpkt.payload[6] = (uint8_t) (bfCrc >> 16);
		txpkt.payload[7] = (uint8_t) (bfCrc >> 24);

		/* single send start programming command 0x0A*/
		/* send packet */
		printf("\nSending 0x0A command to selected transmitter ...\n\n");
		i = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
		if (i == LGW_HAL_ERROR) {
			printf("ERROR\n");
			return EXIT_FAILURE;
		} else {
			/* wait for packet to finish sending */
			do {
				wait_ms(5);
				lgw_status(TX_STATUS, &status_var); /* get TX status */
			} while (status_var != TX_FREE);
			printf("OK\n");
		}
		/* wait inter-packet delay */
		wait_ms(delay);

		/* wait for reply command 0x0B*/
		time(&time_point);
		/* receive packet */
		flag_received_reply = false;
		received_reply_from = 0;
		while (time(NULL) - time_point < 2 && (flag_received_reply != true)) {
			++cycle_count;

			/* fetch packets */
			nb_pkt = lgw_receive(ARRAY_SIZE(rxpkt), rxpkt);
			if (nb_pkt == LGW_HAL_ERROR) {
				MSG("ERROR: failed packet fetch, exiting\n");
				return EXIT_FAILURE;
			} else if (nb_pkt == 0) {
				clock_nanosleep(CLOCK_MONOTONIC, 0, &sleep_time, NULL); /* wait a short time if no packets */
			} else {
				for (i=0; i < nb_pkt; ++i) {
					p = &rxpkt[i];

					if (p->status != STAT_CRC_OK) {
						puts("\"CRC_ERROR\" ");
					}

					if (p->status == STAT_CRC_OK) {

						/* writing packet RSSI */
						//printf("rssi=%+.0f, %lu\n", p->rssi, sizeof(p->rssi));

						if (p->payload[0] == 0x0B) {
							printf("0x0B received, byte[2]=%d\n", p->payload[1]);
							if ((1 << (p->payload[1] - 1)) == transmitter_numbers) {
								//printf("%x, - %x\n", p->payload[2], p->payload[3]);
								flag_received_reply = true;
								break;
							}
							//printf("rceived 0x0B");
						}
						puts("\"\n");
					}
				}
			}
		}

		if (flag_received_reply != true) {
			MSG("no answer\n");
			return EXIT_FAILURE;
		}
		if (p->payload[4] == 0) {
			int16_t rssi = p->payload[2];
			rssi |= (p->payload[3] << 8);
			//printf("rssi[3]=%d, rssi[4]=%d, RSSI=%d\n", p->payload[2], p->payload[3], rssi);
			//printf("RSSI=%d\n", rssi);
			/*if (rssi < 0) {
				MSG("signal too weak");
				return EXIT_FAILURE;
			}*/
				//MSG("start programming ");
				printf("start programming, RSSI=%d\n", rssi);

		} else {
			MSG("too big file");
			return EXIT_FAILURE;
		}

		/* start file sending */
		i = 0;
		j = 0;
		int r = 0;
		uint8_t sendBuffer[PROG_BUF_SIZE + 4];  //
		uint32_t buffCRC;
		while (j < bfSize) {
			wait_ms(10);//some delay between packets
			sendBuffer[0] = j/(PROG_BUF_SIZE - 1);
			for(i = 0;i< PROG_BUF_SIZE - 1;i++){
				sendBuffer[i + 1] = bfBuff[j+i];
			}
			buffCRC = crc32(sendBuffer, PROG_BUF_SIZE);
			memcpy(&sendBuffer[PROG_BUF_SIZE],&buffCRC,4);
			memcpy(txpkt.payload,sendBuffer,PROG_BUF_SIZE + 4);
			r = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
			if (r == LGW_HAL_ERROR) {
				printf("ERROR\n");
				return EXIT_FAILURE;
			} else {
				/* wait for packet to finish sending */
				do {
					wait_ms(2);
					lgw_status(TX_STATUS, &status_var); /* get TX status */
				} while (status_var != TX_FREE);
				printf("Packet %d send OK\n", sendBuffer[0]);
				j += PROG_BUF_SIZE - 1;
				
			}
		}	
			
    /* to do: waiting 0x0C message*/
   
    if (wait_mess(0x0C,transmitter_numbers) != true) {
        MSG("no answer\n");
        lgw_stop();
        return EXIT_FAILURE;
    }
    if (p->payload[2] == 0) {
        MSG("reprogramming is finished\n");
    } else {
		MSG("transmission error\n");
		MSG("error headers - %d\n",p->payload[3]);
		MSG("error packets - %d\n",p->payload[4]);
        if(p->size == 7){
			uint16_t messageErr = (uint16_t)(p->payload[6] << 8) + p->payload[5];
			MSG("Resend packet N - %d\n", messageErr);
			//****repeating errorneous packet***//
			wait_ms(100);//some delay 
			sendBuffer[0] = messageErr;
			j = messageErr*(PROG_BUF_SIZE - 1);
			for(i = 0;i < PROG_BUF_SIZE - 1;i++){
				sendBuffer[i + 1] = bfBuff[j+i];
			}
			buffCRC = crc32(sendBuffer, PROG_BUF_SIZE);
			memcpy(&sendBuffer[PROG_BUF_SIZE],&buffCRC,4);  //write crc
			memcpy(txpkt.payload,sendBuffer,PROG_BUF_SIZE + 4);
			r = lgw_send(txpkt); /* non-blocking scheduling of TX packet */
			if (r == LGW_HAL_ERROR) {
				printf("ERROR\n");
				
				return EXIT_FAILURE;
			} else {
				/* wait for packet to finish sending */
				do {
					wait_ms(2);
					lgw_status(TX_STATUS, &status_var); /* get TX status */
				} while (status_var != TX_FREE);
				printf("Packet %d send OK\n", sendBuffer[0]);	
				if (wait_mess(0x0C,transmitter_numbers) != true) {
					MSG("no answer\n");
					lgw_stop();
					return EXIT_FAILURE;
				}
				if (p->payload[2] == 0) {
					MSG("reprogramming is finished\n");
				} else {
					MSG("transmission error\n");			
				}
			 }
			
		}
        /* clean up before leaving */
		lgw_stop();
        return EXIT_FAILURE;
    }

  }


	/* clean up before leaving */
	lgw_stop();

	printf("Exiting program\n");
	return EXIT_SUCCESS;
}


/* --- EOF ------------------------------------------------------------------ */
