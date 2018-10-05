package main

import (
	"github.com/leesper/couchdb-golang"
        "github.com/luismesas/goPi/MCP23S17"
        "github.com/luismesas/goPi/spi"
        "github.com/tarm/serial"
        "errors"
        "time"
        "bufio"
	"fmt"
        "os"
        "os/exec"
        "strings"
        "log"
	"syscall"
        s "strings"
)

// Message Constants

const IEM_WITH_ALERTER      = 1
const IEM_WITHOUT_ALERTER   = 0

/* Information Selector Constants */

const SW_VERSION_RESPONSE_LEN = 22
const SW_VERSION int          = 0x01
  /* Subselector constants */

  const COMM_PROC_01 int    = 0x01
  const IO_PROCESSOR_01 int = 0x02
  const ADCM_01 int         = 0x03
  const ABCM_PROC_A_01 int  = 0x04
  const ABCM_PROC_B_01 int  = 0x05

const HW_VERSION_RESPONSE_LEN = 7
const HW_VERSION int          = 0x02
  /* Subselector constants */

  const COMM_PROC_02 int    = 0x01
  const IO_PROCESSOR_02 int = 0x02
  const ADCM_02 int         = 0x03
  const ABCM_02 int         = 0x04

const MON_VOLTAGES_RESPONSE_LEN = 16
const MON_VOLTAGES int        = 0x03
  /* Subselector constants */
  
  const IEM_CPU_BOARD_03 int  = 0x01
  const ADCM_03 int           = 0x03
  const ABCM_03 int           = 0x04

const RESET_COUNTER_RESPONSE_LEN = 8
const RESET_COUNTER int       = 0x10
  /* Subselector constants */

  const COMM_PROC_10 int      = 0x01
  const ADCM_10 int           = 0x03
  const ABCM_10 int           = 0x04

const STATUS_VECTOR_RESPONSE_LEN = 7
const STATUS_VECTOR int       = 0x12
  /* Subselector constants */

  const COMM_PROC_AND_IO_PROC_12 int = 0x01

    /* Status Bits */

    const FLASH_TEST_PASSED_01    = 0x01
    const CP_TO_SP_LINK_ACTIVE_01 = 0x02
     
  const ADCM_12 int                  = 0x03
    /* Status Bits */

    const FLASH_TEST_PASSED_03     = 0x01

  const ABCM_12 int                  = 0x04
    /* Status Bits */

    const FLASH_TEST_PASSED_04     = 0x01
    const DETECTED_74V             = 0x02
    const ABCM_A_MAG_VALVE_DRIVE   = 0x04
    const ABCM_B_MAG_VALVE_DRIVE   = 0x08
    const A_TO_B_COMM_LINK_ACTIVE  = 0x10
  
const DIGITAL_INPUTS_RESPONSE_LEN = 13
const DIGITAL_INPUTS int      = 0x31

const ANALOG_INPUTS_RESPONSE_LEN = 22
const ANALOG_INPUTS int       = 0x32
  /* Subselector constants */

  const ANALOG_16V_INPUTS_32 int     = 0x01
  const ANALOG_10V_INPUTS_32 int     = 0x02
  const ANALOG_80V_INPUTS_32 int     = 0x03

const PRESSURE_INPUTS_RESPONSE_LEN = 22
const PRESSURE_INPUTS int     = 0x33

const CUR_4_20MA_INPUTS_RESPONSE_LEN = 22
const CUR_4_20MA_INPUTS       = 0x34

const SPEED_SENSOR_INPUTS_RESPONSE_LEN = 8
const SPEED_SENSOR_INPUTS int = 0x35

const NETWORK_INTERFACE_PARAMS_RESPONSE_LEN = 18
const NETWORK_INTERFACE_PARAMS = 0x40

const AMBIENT_LIGHT_INT_RESPONSE_LEN = 8
const AMBIENT_LIGHT_INT   int = 0x60

const REST_CMD int                           = 0x11
  /* Component selector */

  const COMM_PORC_11 int                     = 0x01
  const ADCM_11 int                          = 0x03
  const ABCM_11 int                          = 0x04

const SET_SPEED_SENSOR_REF_CMD int           = 0x36
  /* Speed Sensaor Reference */

  const ZERO_CROSSING_2_5V int               = 0x00
  const ZERO_CROSSING_0V int                 = 0x01

const SET_ADCM_LED_STATE_CMD int             = 0x61
  /* LED Mask */

  const LED_AT_12 int                        = 0x01
  const LED_AT_3 int                         = 0x02
  const LED_AT_6 int                         = 0x04
  const LED_AT_9 int                         = 0x08

const SET_ADCM_SONALERT_STATE_CMD            = 0x62
const SET_ABCM_MAG_VALVE_DRIVE_STATE_CMD int = 0x92
  /* ABCM Processor Selector */

  const ABCM_PROC_A_92 int                   = 0x04
  const ABCM_PROC_B_92 int                   = 0x05

// CRC16 constants

const zero_bit  int  = 0x1021
const one_bit   int  = 0x2042
const two_bit   int  = 0x4084
const three_bit int  = 0x8108
const four_bit  int  = 0x1231
const five_bit  int  = 0x2462
const six_bit   int  = 0x48c4
const seven_bit int  = 0x9188

var crc_table = [256]int{                                                                             0x0000, /* 0x00 */
                                                                                                    zero_bit, /* 0x01 */
                                                                                          one_bit           , /* 0x02 */
                                                                                          one_bit ^ zero_bit, /* 0x03 */
                                                                                two_bit                     , /* 0x04 */
                                                                                two_bit           ^ zero_bit, /* 0x05 */
                                                                                two_bit ^ one_bit           , /* 0x06 */
                                                                                two_bit ^ one_bit ^ zero_bit, /* 0x07 */
                                                                    three_bit                               , /* 0x08 */
                                                                    three_bit                     ^ zero_bit, /* 0x09 */
                                                                    three_bit           ^ one_bit           , /* 0x0A */
                                                                    three_bit           ^ one_bit ^ zero_bit, /* 0x0B */
                                                                    three_bit ^ two_bit                     , /* 0x0C */
                                                                    three_bit ^ two_bit           ^ zero_bit, /* 0x0D */
                                                                    three_bit ^ two_bit ^ one_bit           , /* 0x0E */
                                                                    three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x0F */
                                                         four_bit                                           , /* 0x10 */
                                                         four_bit ^                                 zero_bit, /* 0x11 */
                                                         four_bit ^                       one_bit           , /* 0x12 */
                                                         four_bit ^                       one_bit ^ zero_bit, /* 0x13 */
                                                         four_bit ^             two_bit                     , /* 0x14 */
                                                         four_bit ^             two_bit           ^ zero_bit, /* 0x15 */
                                                         four_bit ^             two_bit ^ one_bit           , /* 0x16 */
                                                         four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0x17 */
                                                         four_bit ^ three_bit                               , /* 0x18 */
                                                         four_bit ^ three_bit                     ^ zero_bit, /* 0x19 */
                                                         four_bit ^ three_bit           ^ one_bit           , /* 0x1A */
                                                         four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0x1B */
                                                         four_bit ^ three_bit ^ two_bit                     , /* 0x1C */
                                                         four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0x1D */
                                                         four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0x1E */
                                                         four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x1F */
                                              five_bit                                                      , /* 0x20 */
                                              five_bit ^                                            zero_bit, /* 0x21 */
                                              five_bit ^                                  one_bit           , /* 0x22 */
                                              five_bit ^                                  one_bit ^ zero_bit, /* 0x23 */
                                              five_bit ^                        two_bit                     , /* 0x24 */
                                              five_bit ^                        two_bit           ^ zero_bit, /* 0x25 */
                                              five_bit ^                        two_bit ^ one_bit           , /* 0x26 */
                                              five_bit ^                        two_bit ^ one_bit ^ zero_bit, /* 0x27 */
                                              five_bit ^            three_bit                               , /* 0x28 */
                                              five_bit ^            three_bit                     ^ zero_bit, /* 0x29 */
                                              five_bit ^            three_bit           ^ one_bit           , /* 0x2A */
                                              five_bit ^            three_bit           ^ one_bit ^ zero_bit, /* 0x2B */
                                              five_bit ^            three_bit ^ two_bit                     , /* 0x2C */
                                              five_bit ^            three_bit ^ two_bit           ^ zero_bit, /* 0x2D */
                                              five_bit ^            three_bit ^ two_bit ^ one_bit           , /* 0x2E */
                                              five_bit ^            three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x2F */
                                              five_bit ^ four_bit                                           , /* 0x30 */
                                              five_bit ^ four_bit ^                                 zero_bit, /* 0x31 */
                                              five_bit ^ four_bit ^                       one_bit           , /* 0x32 */
                                              five_bit ^ four_bit ^                       one_bit ^ zero_bit, /* 0x33 */
                                              five_bit ^ four_bit ^             two_bit                     , /* 0x34 */
                                              five_bit ^ four_bit ^             two_bit           ^ zero_bit, /* 0x35 */
                                              five_bit ^ four_bit ^             two_bit ^ one_bit           , /* 0x36 */
                                              five_bit ^ four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0x37 */
                                              five_bit ^ four_bit ^ three_bit                               , /* 0x38 */
                                              five_bit ^ four_bit ^ three_bit                     ^ zero_bit, /* 0x39 */
                                              five_bit ^ four_bit ^ three_bit           ^ one_bit           , /* 0x3A */
                                              five_bit ^ four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0x3B */
                                              five_bit ^ four_bit ^ three_bit ^ two_bit                     , /* 0x3C */
                                              five_bit ^ four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0x3D */
                                              five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0x3E */
                                              five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x3F */
                                    six_bit                                                                 , /* 0x40 */
                                    six_bit ^                                                       zero_bit, /* 0x41 */
                                    six_bit ^                                             one_bit           , /* 0x42 */
                                    six_bit ^                                             one_bit ^ zero_bit, /* 0x43 */
                                    six_bit ^                                   two_bit                     , /* 0x44 */
                                    six_bit ^                                   two_bit           ^ zero_bit, /* 0x45 */
                                    six_bit ^                                   two_bit ^ one_bit           , /* 0x46 */
                                    six_bit ^                                   two_bit ^ one_bit ^ zero_bit, /* 0x47 */
                                    six_bit ^                       three_bit                               , /* 0x48 */
                                    six_bit ^                       three_bit                     ^ zero_bit, /* 0x49 */
                                    six_bit ^                       three_bit           ^ one_bit           , /* 0x4A */
                                    six_bit ^                       three_bit           ^ one_bit ^ zero_bit, /* 0x4B */
                                    six_bit ^                       three_bit ^ two_bit                     , /* 0x4C */
                                    six_bit ^                       three_bit ^ two_bit           ^ zero_bit, /* 0x4D */
                                    six_bit ^                       three_bit ^ two_bit ^ one_bit           , /* 0x4E */
                                    six_bit ^                       three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x4F */
                                    six_bit ^            four_bit                                           , /* 0x50 */
                                    six_bit ^            four_bit ^                                 zero_bit, /* 0x51 */
                                    six_bit ^            four_bit ^                       one_bit           , /* 0x52 */
                                    six_bit ^            four_bit ^                       one_bit ^ zero_bit, /* 0x53 */
                                    six_bit ^            four_bit ^             two_bit                     , /* 0x54 */
                                    six_bit ^            four_bit ^             two_bit           ^ zero_bit, /* 0x55 */
                                    six_bit ^            four_bit ^             two_bit ^ one_bit           , /* 0x56 */
                                    six_bit ^            four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0x57 */
                                    six_bit ^            four_bit ^ three_bit                               , /* 0x58 */
                                    six_bit ^            four_bit ^ three_bit                     ^ zero_bit, /* 0x59 */
                                    six_bit ^            four_bit ^ three_bit           ^ one_bit           , /* 0x5A */
                                    six_bit ^            four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0x5B */
                                    six_bit ^            four_bit ^ three_bit ^ two_bit                     , /* 0x5C */
                                    six_bit ^            four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0x5D */
                                    six_bit ^            four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0x5E */
                                    six_bit ^            four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x5F */
                                    six_bit ^ five_bit                                                      , /* 0x60 */
                                    six_bit ^ five_bit ^                                            zero_bit, /* 0x61 */
                                    six_bit ^ five_bit ^                                  one_bit           , /* 0x62 */
                                    six_bit ^ five_bit ^                                  one_bit ^ zero_bit, /* 0x63 */
                                    six_bit ^ five_bit ^                        two_bit                     , /* 0x64 */
                                    six_bit ^ five_bit ^                        two_bit           ^ zero_bit, /* 0x65 */
                                    six_bit ^ five_bit ^                        two_bit ^ one_bit           , /* 0x66 */
                                    six_bit ^ five_bit ^                        two_bit ^ one_bit ^ zero_bit, /* 0x67 */
                                    six_bit ^ five_bit ^            three_bit                               , /* 0x68 */
                                    six_bit ^ five_bit ^            three_bit                     ^ zero_bit, /* 0x69 */
                                    six_bit ^ five_bit ^            three_bit           ^ one_bit           , /* 0x6A */
                                    six_bit ^ five_bit ^            three_bit           ^ one_bit ^ zero_bit, /* 0x6B */
                                    six_bit ^ five_bit ^            three_bit ^ two_bit                     , /* 0x6C */
                                    six_bit ^ five_bit ^            three_bit ^ two_bit           ^ zero_bit, /* 0x6D */
                                    six_bit ^ five_bit ^            three_bit ^ two_bit ^ one_bit           , /* 0x6E */
                                    six_bit ^ five_bit ^            three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x6F */
                                    six_bit ^ five_bit ^ four_bit                                           , /* 0x70 */
                                    six_bit ^ five_bit ^ four_bit ^                                 zero_bit, /* 0x71 */
                                    six_bit ^ five_bit ^ four_bit ^                       one_bit           , /* 0x72 */
                                    six_bit ^ five_bit ^ four_bit ^                       one_bit ^ zero_bit, /* 0x73 */
                                    six_bit ^ five_bit ^ four_bit ^             two_bit                     , /* 0x74 */
                                    six_bit ^ five_bit ^ four_bit ^             two_bit           ^ zero_bit, /* 0x75 */
                                    six_bit ^ five_bit ^ four_bit ^             two_bit ^ one_bit           , /* 0x76 */
                                    six_bit ^ five_bit ^ four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0x77 */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit                               , /* 0x78 */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit                     ^ zero_bit, /* 0x79 */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit           ^ one_bit           , /* 0x7A */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0x7B */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit                     , /* 0x7C */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0x7D */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0x7E */
                                    six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x7F */
                        seven_bit                                                                           , /* 0x80 */
                        seven_bit ^                                                                 zero_bit, /* 0x81 */
                        seven_bit ^                                                       one_bit           , /* 0x82 */
                        seven_bit ^                                                       one_bit ^ zero_bit, /* 0x83 */
                        seven_bit ^                                             two_bit                     , /* 0x84 */
                        seven_bit ^                                             two_bit           ^ zero_bit, /* 0x85 */
                        seven_bit ^                                             two_bit ^ one_bit           , /* 0x86 */
                        seven_bit ^                                             two_bit ^ one_bit ^ zero_bit, /* 0x87 */
                        seven_bit ^                                 three_bit                               , /* 0x88 */
                        seven_bit ^                                 three_bit                     ^ zero_bit, /* 0x89 */
                        seven_bit ^                                 three_bit           ^ one_bit           , /* 0x8A */
                        seven_bit ^                                 three_bit           ^ one_bit ^ zero_bit, /* 0x8B */
                        seven_bit ^                                 three_bit ^ two_bit                     , /* 0x8C */
                        seven_bit ^                                 three_bit ^ two_bit           ^ zero_bit, /* 0x8D */
                        seven_bit ^                                 three_bit ^ two_bit ^ one_bit           , /* 0x8E */
                        seven_bit ^                                 three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x8F */
                        seven_bit ^                      four_bit                                           , /* 0x90 */
                        seven_bit ^                      four_bit ^                                 zero_bit, /* 0x91 */
                        seven_bit ^                      four_bit ^                       one_bit           , /* 0x92 */
                        seven_bit ^                      four_bit ^                       one_bit ^ zero_bit, /* 0x93 */
                        seven_bit ^                      four_bit ^             two_bit                     , /* 0x94 */
                        seven_bit ^                      four_bit ^             two_bit           ^ zero_bit, /* 0x95 */
                        seven_bit ^                      four_bit ^             two_bit ^ one_bit           , /* 0x96 */
                        seven_bit ^                      four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0x97 */
                        seven_bit ^                      four_bit ^ three_bit                               , /* 0x98 */
                        seven_bit ^                      four_bit ^ three_bit                     ^ zero_bit, /* 0x99 */
                        seven_bit ^                      four_bit ^ three_bit           ^ one_bit           , /* 0x9A */
                        seven_bit ^                      four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0x9B */
                        seven_bit ^                      four_bit ^ three_bit ^ two_bit                     , /* 0x9C */
                        seven_bit ^                      four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0x9D */
                        seven_bit ^                      four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0x9E */
                        seven_bit ^                      four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0x9F */
                        seven_bit ^           five_bit                                                      , /* 0xA0 */
                        seven_bit ^           five_bit ^                                            zero_bit, /* 0xA1 */
                        seven_bit ^           five_bit ^                                  one_bit           , /* 0xA2 */
                        seven_bit ^           five_bit ^                                  one_bit ^ zero_bit, /* 0xA3 */
                        seven_bit ^           five_bit ^                        two_bit                     , /* 0xA4 */
                        seven_bit ^           five_bit ^                        two_bit           ^ zero_bit, /* 0xA5 */
                        seven_bit ^           five_bit ^                        two_bit ^ one_bit           , /* 0xA6 */
                        seven_bit ^           five_bit ^                        two_bit ^ one_bit ^ zero_bit, /* 0xA7 */
                        seven_bit ^           five_bit ^            three_bit                               , /* 0xA8 */
                        seven_bit ^           five_bit ^            three_bit                     ^ zero_bit, /* 0xA9 */
                        seven_bit ^           five_bit ^            three_bit           ^ one_bit           , /* 0xAA */
                        seven_bit ^           five_bit ^            three_bit           ^ one_bit ^ zero_bit, /* 0xAB */
                        seven_bit ^           five_bit ^            three_bit ^ two_bit                     , /* 0xAC */
                        seven_bit ^           five_bit ^            three_bit ^ two_bit           ^ zero_bit, /* 0xAD */
                        seven_bit ^           five_bit ^            three_bit ^ two_bit ^ one_bit           , /* 0xAE */
                        seven_bit ^           five_bit ^            three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xAF */
                        seven_bit ^           five_bit ^ four_bit                                           , /* 0xB0 */
                        seven_bit ^           five_bit ^ four_bit ^                                 zero_bit, /* 0xB1 */
                        seven_bit ^           five_bit ^ four_bit ^                       one_bit           , /* 0xB2 */
                        seven_bit ^           five_bit ^ four_bit ^                       one_bit ^ zero_bit, /* 0xB3 */
                        seven_bit ^           five_bit ^ four_bit ^             two_bit                     , /* 0xB4 */
                        seven_bit ^           five_bit ^ four_bit ^             two_bit           ^ zero_bit, /* 0xB5 */
                        seven_bit ^           five_bit ^ four_bit ^             two_bit ^ one_bit           , /* 0xB6 */
                        seven_bit ^           five_bit ^ four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0xB7 */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit                               , /* 0xB8 */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit                     ^ zero_bit, /* 0xB9 */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit           ^ one_bit           , /* 0xBA */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0xBB */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit ^ two_bit                     , /* 0xBC */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0xBD */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0xBE */
                        seven_bit ^           five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xBF */
                        seven_bit ^ six_bit                                                                 , /* 0xC0 */
                        seven_bit ^ six_bit ^                                                       zero_bit, /* 0xC1 */
                        seven_bit ^ six_bit ^                                             one_bit           , /* 0xC2 */
                        seven_bit ^ six_bit ^                                             one_bit ^ zero_bit, /* 0xC3 */
                        seven_bit ^ six_bit ^                                   two_bit                     , /* 0xC4 */
                        seven_bit ^ six_bit ^                                   two_bit           ^ zero_bit, /* 0xC5 */
                        seven_bit ^ six_bit ^                                   two_bit ^ one_bit           , /* 0xC6 */
                        seven_bit ^ six_bit ^                                   two_bit ^ one_bit ^ zero_bit, /* 0xC7 */
                        seven_bit ^ six_bit ^                       three_bit                               , /* 0xC8 */
                        seven_bit ^ six_bit ^                       three_bit                     ^ zero_bit, /* 0xC9 */
                        seven_bit ^ six_bit ^                       three_bit           ^ one_bit           , /* 0xCA */
                        seven_bit ^ six_bit ^                       three_bit           ^ one_bit ^ zero_bit, /* 0xCB */
                        seven_bit ^ six_bit ^                       three_bit ^ two_bit                     , /* 0xCC */
                        seven_bit ^ six_bit ^                       three_bit ^ two_bit           ^ zero_bit, /* 0xCD */
                        seven_bit ^ six_bit ^                       three_bit ^ two_bit ^ one_bit           , /* 0xCE */
                        seven_bit ^ six_bit ^                       three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xCF */
                        seven_bit ^ six_bit ^            four_bit                                           , /* 0xD0 */
                        seven_bit ^ six_bit ^            four_bit ^                                 zero_bit, /* 0xD1 */
                        seven_bit ^ six_bit ^            four_bit ^                       one_bit           , /* 0xD2 */
                        seven_bit ^ six_bit ^            four_bit ^                       one_bit ^ zero_bit, /* 0xD3 */
                        seven_bit ^ six_bit ^            four_bit ^             two_bit                     , /* 0xD4 */
                        seven_bit ^ six_bit ^            four_bit ^             two_bit           ^ zero_bit, /* 0xD5 */
                        seven_bit ^ six_bit ^            four_bit ^             two_bit ^ one_bit           , /* 0xD6 */
                        seven_bit ^ six_bit ^            four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0xD7 */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit                               , /* 0xD8 */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit                     ^ zero_bit, /* 0xD9 */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit           ^ one_bit           , /* 0xDA */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0xDB */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit ^ two_bit                     , /* 0xDC */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0xDD */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0xDE */
                        seven_bit ^ six_bit ^            four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xDF */
                        seven_bit ^ six_bit ^ five_bit                                                      , /* 0xE0 */
                        seven_bit ^ six_bit ^ five_bit ^                                            zero_bit, /* 0xE1 */
                        seven_bit ^ six_bit ^ five_bit ^                                  one_bit           , /* 0xE2 */
                        seven_bit ^ six_bit ^ five_bit ^                                  one_bit ^ zero_bit, /* 0xE3 */
                        seven_bit ^ six_bit ^ five_bit ^                        two_bit                     , /* 0xE4 */
                        seven_bit ^ six_bit ^ five_bit ^                        two_bit           ^ zero_bit, /* 0xE5 */
                        seven_bit ^ six_bit ^ five_bit ^                        two_bit ^ one_bit           , /* 0xE6 */
                        seven_bit ^ six_bit ^ five_bit ^                        two_bit ^ one_bit ^ zero_bit, /* 0xE7 */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit                               , /* 0xE8 */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit                     ^ zero_bit, /* 0xE9 */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit           ^ one_bit           , /* 0xEA */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit           ^ one_bit ^ zero_bit, /* 0xEB */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit ^ two_bit                     , /* 0xEC */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit ^ two_bit           ^ zero_bit, /* 0xED */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit ^ two_bit ^ one_bit           , /* 0xEE */
                        seven_bit ^ six_bit ^ five_bit ^            three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xEF */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit                                           , /* 0xF0 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^                                 zero_bit, /* 0xF1 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^                       one_bit           , /* 0xF2 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^                       one_bit ^ zero_bit, /* 0xF3 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^             two_bit                     , /* 0xF4 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^             two_bit           ^ zero_bit, /* 0xF5 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^             two_bit ^ one_bit           , /* 0xF6 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^             two_bit ^ one_bit ^ zero_bit, /* 0xF7 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit                               , /* 0xF8 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit                     ^ zero_bit, /* 0xF9 */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit           ^ one_bit           , /* 0xFA */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit           ^ one_bit ^ zero_bit, /* 0xFB */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit                     , /* 0xFC */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit           ^ zero_bit, /* 0xFD */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit           , /* 0xFE */
                        seven_bit ^ six_bit ^ five_bit ^ four_bit ^ three_bit ^ two_bit ^ one_bit ^ zero_bit, /* 0xFF */ }


// Global Variables

var Shadows [5]int                         // Shadow resgisters for the port extenders

var TestDB *couchdb.Database               // Pointer to the test database

var SerialPort *serial.Port                // Serial port for talking to the IEM
var ConsoleInput *bufio.Reader             // Console Input port

var AssemblyMajorPartNumber int            // Upper part of the assembly part number
var AssemblyMinorPartNumber int            // Lower part of the assembly part number
var AssemblyPartNumber string              // Assembly Part Number string
var AssemblySerialNumber string            // Assembly Serial Number string

var MainCircuitMajorPartNumber int         // Upper part of the Main Circuit part number
var MainCircuitMinorPartNumber int         // Lower part of the Main Circuit part number
var MainCircuitPartNumber string           // Main Circuit Part Number string
var MainCircuitSerialNumber string         // Main Circuit Serial Number string

var DualPowerSupplyMajorPartNumber int     // Upper Part of the Dual Power Supply part number
var DualPowerSupplyMinorPartNumber int     // Lower Part of the Dual Power Supply part number
var DualPowerSupplyPartNumber string       // Dual Power Supply Part Number string
var DualPowerSupplySerialNumber string     // Dual Power SUpply Serial Number string

var CabConnectorMajorPartNumber int        // Upper part of the Cab Connector part number
var CabConnectorMinorPartNumber int        // Lower part of the Cab Connector part number
var CabConnectorCardPartNumber string      // Cab Connector Part Number string
var CabConnectorSerialNumber string        // Cab Connector Serial Number string

var IOConnectorMajorPartNumber int         // Upper part of the IO Connector part number
var IOConnectorMinorPartNumber int         // Lower part of the IO Connector part number
var IOConnectorPartNumber string           // IO Connector Part Number string
var IOConnectorSerialNumber string         // IO Connector Serial Number string

var IEM4_20mAMajorPartNumber int           // Upper part of the IEM 4-20 mA part number
var IEM4_20mAMinorPartNumber int           // Lower part of the IEM 4-20 mA part number
var IEM4_20mAPartNumber string             // IEM 4-20 mA Part Number string
var IEM4_20mASerialNumber string           // IEM 4-20 mA Serial Number string

var ABCMMajorPartNumber int                // Upper part of the ABCM part number
var ABCMMinorPartNumber int                // Lower part of the ABCM part number
var ABCMPartNumber string                  // ABCM Part Number string
var ABCMSerialNumber string                // ABCM Serial Number string

var ADCMMajorPartNumber int                // Upper part of the ADCM part number
var ADCMMinorPartNumber int                // Lower part of the ADCM part number
var ADCMPartNumber string                  // ADCM Part Number string
var ADCMSerialNumber string                // ADCM Serial Number string

/* Test Result Structures */

// Range type test result

type RangeTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time the test was run
  Date string `json:"date"`                                 // Date the test was run
  Value int `json:"value"`                                  // Value generated by the test
  MaxValue int `json:"maxvalue"`                            // Maximum allowed value
  MinValue int `json:"minvalue"`                            // Minimum allowed value
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Lower Limit Test Result

type LowerLimitTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time the test was run
  Date string `json:"date"`                                 // Date the test was run
  Value int `json:"value"`                                  // Value generated by the test
  LowerLimit int `json:"lowerlimit"`                        // Minimum allowed value
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Upper Limit Test Result

type UpperLimitTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time the test was run
  Date string `json:"date"`                                 // Date the test was run
  Value int `json:"value"`                                  // Value generated by the test
  UpperLimit int `json:"upperlimit"`                        // Maximum allowed value
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Match Test Result

type MatchTestResult struct {          
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time the test was run
  Date string `json:"date"`                                 // Date the test was run
  Received int `json:"received"`                            // Value generated by the test
  Expected int `json:"expected"`                            // Value expected by the test
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Pass/Fail Test Result 

type PassFailTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time that the test was run
  Date string `json:"date"`                                 // Date that the test was run
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Hardware Version Number Test Result

type HardwareVersionTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time that the test was run
  Date string `json:"date"`                                 // Date that the test was run
  HardwareVersion int `json:"hardwareversion"`              // Harware Version Number of the module
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

// Software Version Number Test Result

type SoftwareVersionTestResult struct {
  AssemblyPartNumber string `json:"assemblypartnumber"`     // Assembly Part Number
  AssemblySerialNumber string `json:"assemblyserialnumber"` // Assembly Serial Number
  PartNumber string `json:"partnumber"`                     // Module Part Number
  SerialNumber string `json:"serialnumber"`                 // Module Serial Number
  TestName string `json:"name"`                             // Name of the test
  Time string `json:"time"`                                 // Time that the test was run
  Date string `json:"date"`                                 // Date that the test was run
  SoftwareVersion string `json:"softwareversion"`           // Software Version Number of the module
  Pass bool `json:"pass"`                                   // Pass/Fail flag
  couchdb.Document                                          // Associated Document Information
}

/*
   Procedure Name : CRC16

   Description    : Calculates the CRC on IEM messages

   Arguments      : bytes - Slice containing the message to be CRCed
                    size  - Number of bytes in the message

   Return Value   : Caluclated Message CRC
*/

func CRC16( bytes []int, size int ) int {
  crc := 0
  index := 0

  for i:=0;i < size;i++ {
    crc ^= (bytes[i] << 8)
    index = (crc >> 8) & 0xff
    
    crc = ((crc << 8) ^ crc_table[index]) & 0xffff
  }

  return crc
}

/*
    Procedure Name : SendBytes

    Description    : Takes the bytes and the CRC for an
                     IEM message, does the byte stuffing,
                     and sends the completed message to the
                     IEM.

    Arguments      : bytes - Slice that contains the message bytes and CRC
                     
    RetValue       : Number of bytes sent
                     Any error returned by the serial send routine
*/

func SendBytes( bytes []int ) (int, error) {

  var err error
  RetValue := -1
  outputIndex := 0

  output := make([]byte, 2*len(bytes)+4, 2*len(bytes) + 4) // Setup output message

  output[outputIndex] = 0xf5 // Add the starting byte
  outputIndex += 1

  /* Add the CRC and do the byte stuffing */

  for i := 0;i < len(bytes);i++ {
    if i == (len(bytes) - 1) {
      if bytes[i] & 0xf000 == 0xf000 {
        output[outputIndex] = 0xf0
        outputIndex += 1
        output[outputIndex] = (byte) (((bytes[i] & 0xf00) >> 8) & 0xff)
        outputIndex += 1
      } else {
        output[outputIndex] = (byte) ((bytes[i] >> 8) & 0xff)
        outputIndex += 1
      }

      if (bytes[i] & 0xf0) == 0xf0 {
        output[outputIndex] = 0xf0
        outputIndex += 1
        
        output[outputIndex] = (byte) (bytes[i] & 0xf)
        outputIndex += 1
      } else {
        output[outputIndex] = (byte) (bytes[i] & 0xff)
        outputIndex += 1
      }
      
      output[outputIndex] = 0xf6
      outputIndex += 1
    } else {
      if (bytes[i] & 0xf0) == 0xf0 {
        output[outputIndex] = 0xf0
        outputIndex += 1

        output[outputIndex] = (byte) (bytes[i] & 0xf)
        outputIndex += 1
      } else {
        output[outputIndex] = (byte) (bytes[i])
        outputIndex += 1
      }
    }
  }

  /* Send the commpled message to the IEM */

  if RetValue == -1 {
    RetValue, err = SerialPort.Write( output )
  }

  /* Return the bytes sent and any errors */

  return RetValue,err
}

/*
    Procedure Name : UnstuffMessage

    Description    : This routine takes an imcoming IEM message and
                     reverses the buff stuffing.

    Arguments      : bytes - Slice containg the message to unstuff
                     responseCount - Starting size of the message

    Retrun Value   : Length of message after unstuffing
*/

func UnstuffMessage( bytes []byte, responseCount int ) (int) {
  stuff := (int) (0)
  returnCount := (int) (0)

  /*
    In order to unstuff the message we look for 0xf0 bytes. 
    When we find one, we combine it with the following byte
    replacing the two bytes with one. As we go we keep track
    of the remaining bytes in the message.
  */

  for i := 0;i < responseCount;i++ {
    if stuff == 0 {
      bytes[returnCount] = bytes[i]

      if bytes[i] == 0xf0 {
        stuff = 1
      } else {
        returnCount += 1
      }
    } else {
      stuff = 0

      bytes[returnCount] |= bytes[i]

      returnCount += 1
    }
  }

  return returnCount
}

/*
    Procedure Name : WaitForResponse

    Description    : Waits for the return message which is a respnse
                     to the last message sent to the IEM.

    Arguments      : Slice used to contain the response message
                     Expected response message length

    Retrun Value   : Response Message Length
                     Any reception error
*/

func WaitForResponse( bytes []byte, responseCount int ) (int, error) {
  var byteCount int = 0
  var returnCount int = 0
  var err error = nil

  /*
      This Serial port is setup as non-blocking with a five second
      timeout. The strategy is to bring the message a few bytes at
      a time until we complete the message. We consider the message
      finished when we see the end framing byte or the input times
      out on a read. If we get a timeout, we return an error of no
      response. If we get a complete message, then we run it through
      the unstuffing routine before we return it to the caller.
  */

  returnCount, err = SerialPort.Read( bytes )

  byteCount += returnCount

  for byteCount < (responseCount + 10) {
    returnCount, err = SerialPort.Read( bytes[byteCount:] )

    byteCount += returnCount

    if byteCount >= 1 {
      if bytes[byteCount - 1] == 0xf6 {
        break
      }
    }

    if byteCount == 0 {
      err = errors.New("No response")

      break
    }
  } 

  if err == nil {
    byteCount = UnstuffMessage( bytes, byteCount )
  }

  return byteCount, err
}

/*
    Procedure Name : InformationSelectionCommand

    Description    : THis is the routine that is used to construct
                     messages that request information from the IEM.

    Argument       : selector    - Main information selector value
                     subselector - Information subselector value
                     response    - Slice used for returning the response

    Return Value   : Length of the response message
                     Any error generated in the exchange   
*/

func InformationSelectionCommand( selector int, subselector int, response []byte ) (int, error) {

  var returnCount int = 0
  var ResponseErr error = nil

  /* The main selector value determines what the request message should look like.
  */

  switch selector {
    case SW_VERSION :
      switch subselector {
        /*
           Communications Processor Software Version request
        */

        case COMM_PROC_01 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, SW_VERSION_RESPONSE_LEN )

        /*
           I/O Processor Software Version request
        */

        case IO_PROCESSOR_01 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, SW_VERSION_RESPONSE_LEN )

        /*
           ADCM Software Version request
        */

        case ADCM_01 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, SW_VERSION_RESPONSE_LEN )

        /*
           ABCM Processor A Software Version request
        */

        case ABCM_PROC_A_01 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, SW_VERSION_RESPONSE_LEN )

        /*
           ABCM Processor B Software Version request
        */

        case ABCM_PROC_B_01 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, SW_VERSION_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    case HW_VERSION :
      switch subselector {
        /*
           Communications Processor Hardware Version request
        */

        case COMM_PROC_02 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, HW_VERSION_RESPONSE_LEN )

        /*
           I/O Processor Hardware Version request
        */

        case IO_PROCESSOR_02 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, HW_VERSION_RESPONSE_LEN )

        /*
           ADCM Hardware Version request
        */

        case ADCM_02 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, HW_VERSION_RESPONSE_LEN )

        /*
           ABCM Hardware Version request
        */

        case ABCM_02 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, HW_VERSION_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    case MON_VOLTAGES :
      switch subselector {
        /*
           IEM CPU Board Monitored Voltages request
        */

        case IEM_CPU_BOARD_03 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, MON_VOLTAGES_RESPONSE_LEN )

        /*
           ADCM Monitored Voltages request
        */

        case ADCM_03 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, MON_VOLTAGES_RESPONSE_LEN )

        /*
           ABCM Monitored Voltages request
        */

        case ABCM_03 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, MON_VOLTAGES_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    case RESET_COUNTER :
      switch subselector {
        /*
           Communications Processor Reset Counter Value request
        */

        case COMM_PROC_10 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, RESET_COUNTER_RESPONSE_LEN )

        /*
           ADCM Reset Counter Value request
        */

        case ADCM_10 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, RESET_COUNTER_RESPONSE_LEN )

        /*
           ABCM Reset Counter Value request
        */

        case ABCM_10 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, RESET_COUNTER_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    case STATUS_VECTOR :
      switch subselector {
        /*
           Communications Processor Status Vector Value request
        */

        case COMM_PROC_AND_IO_PROC_12 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, STATUS_VECTOR_RESPONSE_LEN )

        /*
           ADCM Status Vector Value request
        */

        case ADCM_12 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, STATUS_VECTOR_RESPONSE_LEN )

        /*
           ABCM Status Vector Value request
        */

        case ABCM_12 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, STATUS_VECTOR_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    /*
       Digital Input Values request
    */

    case DIGITAL_INPUTS :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, DIGITAL_INPUTS_RESPONSE_LEN )

    case ANALOG_INPUTS :
      switch subselector {
        /*
           16 Volt Analog Input Values request
        */

        case ANALOG_16V_INPUTS_32 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, ANALOG_INPUTS_RESPONSE_LEN )

        /*
           10 Volt Analog Input Values request
        */

        case ANALOG_10V_INPUTS_32 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, ANALOG_INPUTS_RESPONSE_LEN )

        /*
           80 Volt Analog Input Values request
        */

        case ANALOG_80V_INPUTS_32 :
          message := []int{ selector, subselector, 0 }
          crc := CRC16( message, 2 )
          message[2] = crc
          SendBytes( message )
          returnCount, ResponseErr = WaitForResponse( response, ANALOG_INPUTS_RESPONSE_LEN )

        default :
          ResponseErr = errors.New("Unknown Subselector")
          returnCount = 0
      }

    /*
       Pressure Input Values request
    */

    case PRESSURE_INPUTS :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, PRESSURE_INPUTS_RESPONSE_LEN )

    /*
       Current 4-20 mA Input Values request
    */

    case CUR_4_20MA_INPUTS :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, CUR_4_20MA_INPUTS_RESPONSE_LEN )

    /*
       Speed Sensor Input Values request
    */

    case SPEED_SENSOR_INPUTS :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, SPEED_SENSOR_INPUTS_RESPONSE_LEN )

    /*
       Network Parameters request
    */

    case NETWORK_INTERFACE_PARAMS :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, NETWORK_INTERFACE_PARAMS_RESPONSE_LEN )

    /*
       ADCM Ambient Light Sensor Value request
    */

    case AMBIENT_LIGHT_INT :
      message := []int{ selector, 0, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )
      returnCount, ResponseErr = WaitForResponse( response, 6 )

    default :
      ResponseErr = errors.New("Unknown Selector")
      returnCount = 0
  }

  return returnCount, ResponseErr
}

/*
    Procedure Name : ResetCounterCommand

    Description    : This routine sends a command to the IEM to clear
                     the appropriate reset counter.

    Argument       : selector - Determines which reset counter to clear

    Return Value   : Indicator of whether the message was sent ( 1 sent, 0 not sent)
*/

func ResetCounterCommand( selector int ) (int, error) {
  var err error = nil
  RetValue := 1

  switch selector {
    /* Clear the Communications Processor Reset Counter */

    case COMM_PORC_11 :
      message := []int{ REST_CMD, selector, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )

    /* Clear the ADCM Reset Counter */

    case ADCM_11 :

      message := []int{ REST_CMD, selector, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )

    /* Clear the ABCM Reset Counter */

    case ABCM_11 :
      message := []int{ REST_CMD, selector, 0 }
      crc := CRC16( message, 2 )
      message[2] = crc
      SendBytes( message )

    default :
      err = errors.New("Unknown Selector")
      RetValue = 0
  }

  return RetValue, err
}

/*
    Procedure Name : SetSpeedSensorRefCommand

    Description    : This routine sends a message to the IEM to set
                     the speed sensor reference voltage.

    Argument       : reference - 0 for 2.5 volts and 1 for 0 volts.

    Return Value   : Flag indicating whether the message was sent ( 1 sent, 0 not sent)
*/

func SetSpeedSensorRefCommand( reference int ) (int, error) {
  var err error = nil
  RetValue := 1

  switch reference {
    /*
       Set the reference to 2.5 volts
    */

    case ZERO_CROSSING_2_5V :
      message := []int{ SET_SPEED_SENSOR_REF_CMD, 0, reference, 0 }
      crc := CRC16( message, 3 )
      message[3] = crc
      SendBytes( message )

    /*
       Set the reference to 0 volts
    */

    case ZERO_CROSSING_0V :
      message := []int{ SET_SPEED_SENSOR_REF_CMD, 0, reference, 0 }
      crc := CRC16( message, 3 )
      message[3] = crc
      SendBytes( message )

    default :
      err = errors.New("Unknown Reference")
      RetValue = 0
  }

  return RetValue, err
}

/*
    Procedure Name : SetADCM_LEDSStateCommand

    Description    : This routines sends a command to set the state
                     of the ADCM LEDs.

    Arguments      : ledMask    - Determines which LEDs to set
                     brightness - Brightness level of the LEDs

    Return Value   : Flag indicates whether the message was sent (1 sent, 0 not sent)
*/

func SetADCM_LEDStateCommand( ledMask int, brightness int ) (int, error) {
  var err error = nil
  RetValue := 1

  if brightness >= 0 && brightness <= 100 {
    if (ledMask & 0xf0) == 0 {
      message := []int{ SET_ADCM_LED_STATE_CMD, 0, ledMask, brightness, 0 }
      crc := CRC16( message, 4 )
      message[4] = crc
      SendBytes( message )
    } else {
      err = errors.New("Unknown Mask Bits")
      RetValue = 0
    }
  } else {
    err = errors.New("Unknown Brightness")
    RetValue = 0
  }

  return RetValue, err
}

/*
    Procedure Name : SetADCMSonalertStateCommand

    Description    : This routine sends a command to the IEM to enable/disable the ADCMs sonalert
                     and set its volume.

    Return Value   : Flag indicating whether the message was sent ( 1 sent, 0 not sent )
*/

func SetADCMSonalertStateCommand( enable int, volume int ) (int, error) {
  var err error = nil
  RetValue := 1

  if volume >= 0 && volume <= 100 {
    switch enable {
      case 0 :
        message := []int{ SET_ADCM_SONALERT_STATE_CMD, 0, enable, volume, 0 }
        crc := CRC16( message, 4 )
        message[4] = crc
        SendBytes( message )

      case 1 :
        message := []int{ SET_ADCM_SONALERT_STATE_CMD, 0, enable, volume, 0 }
        crc := CRC16( message, 4 )
        message[4] = crc
        SendBytes( message )

      default :
        err = errors.New("UnKnow Enable Value")
        RetValue = 0
    }
  } else {
    err = errors.New("Unkown Volume")
    RetValue = 0
  }

  return RetValue, err
}

/*
    Procedure Name : SetABCMMagValveDriveStateCommand

    Description    : This routine sends a command to the IEM to
                     set the Magnetic Valve Drive State for the
                     requested ADCM processor (A or B).

    Arguments      : processor - Determines which processor is affected
                     enable    - Determines whether the drive is enabled or disabled.

    Return Value   : Flage indicating whether the message was sent ( 1 sent, 0 not sent )
                     Any error returned from sending the message
*/

func SetABCMMagValveDriveStateCommand( processor int, enable int ) (int, error) {
  var err error = nil
  RetValue := 1

  switch processor {
    case ABCM_PROC_A_92 :
      switch enable {
        case 0 :
          message := []int{ SET_ABCM_MAG_VALVE_DRIVE_STATE_CMD, processor, enable, 0 }
          crc := CRC16( message, 3 )
          message[3] = crc
          SendBytes( message )

        case 1 :
          message := []int{ SET_ABCM_MAG_VALVE_DRIVE_STATE_CMD, processor, enable, 0 }
          crc := CRC16( message, 3 )
          message[3] = crc
          SendBytes( message )

        default :
          err = errors.New("Unknown Enable Value")
          RetValue = 0
      }

    case ABCM_PROC_B_92 :
      switch enable {
        case 0 :
          message := []int{ SET_ABCM_MAG_VALVE_DRIVE_STATE_CMD, processor, enable, 0 }
          crc := CRC16( message, 3 )
          message[3] = crc
          SendBytes( message )

        case 1 :
          message := []int{ SET_ABCM_MAG_VALVE_DRIVE_STATE_CMD, processor, enable, 0 }
          crc := CRC16( message, 3 )
          message[3] = crc
          SendBytes( message )

        default :
          err = errors.New("Unknown Enable Value")
          RetValue = 0
      }

    default :
      err = errors.New("Unknow Processor")
      RetValue = 0
  }

  return RetValue, err
}

/* 
    Procedure Name : Init

    Description    : This routine sets up the initial state of the IEM tester before a test is run.

    Arguments      : mcp - Slice of pointer to control structures for the port extenders.

    Return Value   : Flag indicating whether the initialization was successful ( 1 successful, 0 not successful)
                     Any error that occurred during initialization.
*/

func Init( mcp []*MCP23S17.MCP23S17 ) (int, error) {
  var err error = nil
  var err1 error = nil
  RetValue := 1

  /*
     Set the port extenders to their initial values.
  */

  mcp[0].Write( 0xfc, MCP23S17.OLATA )
  mcp[0].Write( 0xcf, MCP23S17.OLATB )

  Shadows[0] = 0xcffc

  mcp[1].Write( 0xff, MCP23S17.OLATA )
  mcp[1].Write( 0xff, MCP23S17.OLATB )

  Shadows[1] = 0xffff

  mcp[2].Write( 0xff, MCP23S17.OLATA )
  mcp[2].Write( 0xff, MCP23S17.OLATB )

  Shadows[2] = 0xffff

  mcp[3].Write( 0x06, MCP23S17.OLATA )
  mcp[3].Write( 0xc0, MCP23S17.OLATB )

  Shadows[3] = 0xc006

  mcp[4].Write( 0x00, MCP23S17.OLATA )
  mcp[4].Write( 0x00, MCP23S17.OLATB )

  Shadows[4] = 0x0000

  /*
     Turn off the ADCM Sonalert.
  */

  RetValue, err = SetADCMSonalertStateCommand( 0, 100 )

  if err != nil {
    RetValue = 0
  }

  /*
     Turn off the ADCM LEDs.
  */

  RetValue, err1 = SetADCM_LEDStateCommand( 0, 20 )

  if err1 != nil {
    if err == nil {
      err = err1
    }

    RetValue = 0
  }

  /*
     Turn off the ABCM Mag Valve drive on both processors.
  */

  RetValue, err1 = SetABCMMagValveDriveStateCommand( ABCM_PROC_A_92, 0 )

  if err1 != nil {
    if err == nil {
      err = err1
    }

    RetValue = 0
  }

  RetValue, err1 = SetABCMMagValveDriveStateCommand( ABCM_PROC_B_92, 0 )

  if err1 != nil {
    if err == nil {
      err = err1
    }

    RetValue = 0
  }

  return RetValue, err
}

/*
    Procedure Name : Test_4_20MA

    Description    : This routine runs the IEM 4-20 mA test.

    Arguments      : mcp - Slice of pointers to port extender control structures.

    Return Value   : Pass/Fail flag
                     Any error that occurred during the test.
*/

func Test_4_20MA( mcp []*MCP23S17.MCP23S17 ) (int, error) {
  var err error = nil
  var responseCount int
  RetValue := 1
  Passed := 1

  response := make( []byte, 30 )

  /* 
     Turn on bit 13 of port extender zero. Then ask for the IEM 4-20 mA inputs.
  */

  Shadows[0] |= 0x2000
  
  mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

  responseCount, err = InformationSelectionCommand( CUR_4_20MA_INPUTS, 0, response )

  if err != nil || responseCount != CUR_4_20MA_INPUTS_RESPONSE_LEN {

    RetValue = 0
    Passed = 0

    if err == nil && responseCount != 0 {
      err = errors.New( "Bad 4_20 MA Inputs response count." )
    }
  }
  
  if err == nil {
    /*
       Check channel 8 of the returned values. Record the whether it passes or fails
       and write the result to the database. Then turn on bit 14 of port extender zero
       and wait a second. Then ask the IEM for the 4-20 mA Inputs again.
    */

    counts := 0

    counts = (int) (response[17])
    counts = (counts << 8) + (int) (response[18])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = IEM4_20mAPartNumber
    Test.SerialNumber = IEM4_20mASerialNumber
    Test.TestName = "4-20mA Test 1 Channel 8 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3708
    Test.MinValue = 3492
    Test.Pass = true

    if counts <= 3492 || counts >= 3708 {
      fmt.Printf(" Test 1 Channel 8 Failed (Got %d Expected > 3492 and < 3708)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    Shadows[0] |= 0x4000

    mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(1)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( CUR_4_20MA_INPUTS, 0, response )

    if err != nil || responseCount != CUR_4_20MA_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil && responseCount != 0 {
        err = errors.New( "Bad 4_20 MA Inputs response count." )
      }

      log.Printf("%q", err)
    }

    if Passed == 1 {
      fmt.Printf(" Test 1 Channel 8 Passed.\r\n")
    }
  }

  Passed = 1

  /*
     Check channel 1 for proper range and set the pass/fail flag. Write the test result to the database.
  */

  if err == nil {
    counts := 0

    counts = (int) (response[3])
    counts = (counts << 8) + (int)(response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = IEM4_20mAPartNumber
    Test.SerialNumber = IEM4_20mASerialNumber
    Test.TestName = "4-20mA Test 2 Channel 1 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2100
    Test.MinValue = 1900
    Test.Pass = true

    if counts <= 1900 || counts >= 2100 {
      fmt.Printf(" Test 2 Channel 1 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if err == nil {
      /*
          Check channel two for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[5])
      counts = (counts << 8) + (int)(response[6])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 2 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 2 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel three for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[7])
      counts = (counts << 8) + (int)(response[8])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 3 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 3 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel four for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[9])
      counts = (counts << 8) + (int)(response[10])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 4 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 4 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel five for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[11])
      counts = (counts << 8) + (int)(response[12])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 5 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 5 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel six for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[13])
      counts = (counts << 8) + (int)(response[14])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 6 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 6 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

    }

    if err == nil {
      /*
          Check channel seven for the proper range and set the pass/fail flag. Write the test result to the database.
          Then turn off bit 14 of pert extender zero and wait a second. Again ask the IEM for the 4-20 mA inputs.
      */

      counts = (int) (response[15])
      counts = (counts << 8) + (int)(response[16])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 2 Channel 7 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 2100
      Test.MinValue = 1900
      Test.Pass = true

      if counts <= 1900 || counts >= 2100 {
        fmt.Printf(" Test 2 Channel 7 Failed (Got %d Expected > 1900 and < 2100)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    Shadows[0] &= ^0x4000

    mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(1)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( CUR_4_20MA_INPUTS, 0, response )

    if err != nil || responseCount != CUR_4_20MA_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil && responseCount != 0 {
        err = errors.New( "Bad 4_20 MA Inputs response count." )
      }

      log.Printf("%q", err)
    }

    if Passed == 1 {
      fmt.Printf(" Test 2 Channels 1 to 7 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check channel one for the proper range and set the pass/fail flag. Write the test result to the database.
    */

    counts := (int)(response[3])
    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = IEM4_20mAPartNumber
    Test.SerialNumber = IEM4_20mASerialNumber
    Test.TestName = "4-20mA Test 3 Channel 1 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 4100
    Test.MinValue = 3800
    Test.Pass = true

    if counts <= 3800 || counts >= 4200 {
      fmt.Printf(" Test 3 Channel 1 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if err == nil {
      /*
          Check channel two for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[5])
      counts = (counts << 8) + (int) (response[6])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 2 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 2 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel three for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[7])
      counts = (counts << 8) + (int) (response[8])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 3 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 3 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel four for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[9])
      counts = (counts << 8) + (int) (response[10])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 4 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 4 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel five for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[11])
      counts = (counts << 8) + (int) (response[12])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 5 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 5 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel six for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[13])
      counts = (counts << 8) + (int) (response[14])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 6 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 6 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if err == nil {
      /*
          Check channel seven for the proper range and set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[15])
      counts = (counts << 8) + (int) (response[16])
  
      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = IEM4_20mAPartNumber
      Test.SerialNumber = IEM4_20mASerialNumber
      Test.TestName = "4-20mA Test 3 Channel 7 Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4200
      Test.MinValue = 3800
      Test.Pass = true

      if counts <= 3800 || counts >= 4200 {
        fmt.Printf(" Test 3 Channel 7 Failed (Got %d Expected > 3800 and < 4200)\r\n", counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if Passed == 1 {
      fmt.Printf(" Test 3 Channels 1 to 7 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the IEM for the I/O processors reset counter. Turn on bit 13 of port extender 0.
        Wait three seconds and ask the IEM again for the I/O processor reset counter..
    */

    responseCount, err = InformationSelectionCommand( RESET_COUNTER, COMM_PROC_10, response )

    if err == nil && responseCount == RESET_COUNTER_RESPONSE_LEN {

      before := (int) (response[4])
      before = (before << 8) + (int) (response[5])

      Shadows[0] |= 0x2000

      mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )
    
      start := time.Now()

      t := time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(3)*time.Second {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( RESET_COUNTER, COMM_PROC_10, response )

      if err == nil && responseCount == RESET_COUNTER_RESPONSE_LEN {
        /*
           Compare the first value of the reset counter to the second value of the reset. 
           Set the pass/fail flag to pass if they matche and fail if they don't match.
           Then write the test result to the database.
        */

        after := (int) (response[4])
        after = (after << 8) + (int) (response[5])

        Test := MatchTestResult{}

        Test.AssemblyPartNumber = AssemblyPartNumber
        Test.AssemblySerialNumber = AssemblySerialNumber
        Test.PartNumber = IEM4_20mAPartNumber
        Test.SerialNumber = IEM4_20mASerialNumber
        Test.TestName = "4-20mA Test 4 Reset Counter Test"

        timeDate := time.Now()
        hour, min, sec := timeDate.Clock()
        year, month, day := timeDate.Date()

        Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
        Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
        Test.Received = after
        Test.Expected = before
        Test.Pass = true

        if before != after {
          fmt.Printf(" Test 4 Reset Counter Test Failed (Got %d Expected %d)\r\n", after, before)

          Test.Pass = false
          RetValue = 0
          Passed = 0
        }

        Test.SetID(couchdb.GenerateUUID())

        err = couchdb.Store( TestDB, &Test )
      } else {
        RetValue = 0
        Passed = 0

        if err != nil && responseCount != 0 {
          err = errors.New( "Bad Reset Counter Response." )
        }
      }
    } else {
      RetValue = 0
      Passed = 0

      if err != nil && responseCount != 0 {
        err = errors.New( "Bad Reset Counter Response." )
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 Reset Counter Test Passed.\r\n")
    }

    /*
       Again ask the IEM for the 4-20 mA inputs.
    */

    responseCount, err = InformationSelectionCommand( CUR_4_20MA_INPUTS, 0, response )

    if err != nil || responseCount != CUR_4_20MA_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil && responseCount != 0 {
        err = errors.New( "Bad 4_20 MA Inputs response count." )
      }

      log.Printf("%q", err)
    }
  }

  Passed = 1

  if err == nil {
    counts := (int) (response[17])

    counts = (counts << 8) + (int) (response[18])

    /*
        Check channel 8 for the correct range and set the pass/fail flag. Write the test result to the database.
    */

    Test := LowerLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = IEM4_20mAPartNumber
    Test.SerialNumber = IEM4_20mASerialNumber
    Test.TestName = "4-20mA Test 4 Reset Counter Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.LowerLimit = 3492
    Test.Pass = true

    if counts <= 3492 {
      fmt.Printf(" Test 4 Channel 8 Failed (Got %d Expected > 3492)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if Passed == 1 {
      fmt.Printf(" Test 4 Channel 8 Passed.\r\n")
    }
  }

  /*
      Set the tester back to its initial state.
  */

  _, err1 := Init( mcp )

  if err == nil {
    err = err1
  }

  return RetValue, err
}

/*
    Procedure Name : Test_CPUMain

    Description    : This routine runs the IEM Main CPU test.

    Arguments      : mcp - Slice of pointers to the port extender control structures
                     IEMType - 0 for no alerter, 1 for aleter present

    Retrun Value   : Flag indicating whether the test passed or failed.
                     Any error that occurred during the test.
*/

func Test_CPUMain( mcp []*MCP23S17.MCP23S17, IEMType int ) (int, error) {
  var err error = nil
  var responseCount int

  response := make([] byte, 50)

  group := 1
  skip := 0
  RetValue := 1
  Passed := 1
  zeroPressureReading := 0

  /*
      Turn on bit 12 of port extender 0. Then ask the IEM for the monitored voltanges
      for the CPU board.
  */

  Shadows[0] |= 0x1000

  mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

  responseCount, err = InformationSelectionCommand( MON_VOLTAGES, IEM_CPU_BOARD_03, response )

  if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
    RetValue = 0

    if err == nil && responseCount != 0 {
      err = errors.New("Bad Monitored Voltages.")
    }

    log.Printf("%q", err)
  }
  
  if err == nil {
    /*
        Check the 12 Volt entry for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])
    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 1 12 Volt Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 11400
    Test.MinValue = 12600
    Test.Pass = true

    if counts <= 11400 || counts >= 12600 {
      fmt.Printf(" Test 1 12 Volts Failed ( Got %d Expected 11400 to 12600)\r\n")

      Test.Pass = false
      Passed = 0
      RetValue = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if err == nil {
      /*
          Check the 3.3 Volt entry for the proper range and then set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[5])
      counts = (counts << 8) + (int) (response[6])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 1 3.3 Volt Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 3135
      Test.MinValue = 3465
      Test.Pass = true

      if counts <= 3135 || counts >= 3465 {
        fmt.Printf(" Test 1 3.3 Volts Failed ( Got %d Expected 3135 to 3465)\r\n")

        Test.Pass = false
        Passed = 0
        RetValue = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }
 
    if err == nil {
      /*
          Check the 5 Volt entry for th proper range and then set the pass/fail flag. Write the test result to the database.
      */

      counts = (int) (response[7])
      counts = (counts << 8) + (int) (response[8])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 1 5 Volt Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 4750
      Test.MinValue = 5250
      Test.Pass = true

      if counts <= 4750 || counts >= 5250 {
        fmt.Printf(" Test 1 5 Volts Failed ( Got %d Expected 4750 to 5250)\r\n")

        Test.Pass = false
        Passed = 0
        RetValue = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    if Passed == 1 {
      fmt.Printf(" Test 1 Monitored Voltages Passed\r\n")
    }

    Passed = 1

    /*
        Turn off the top eight bits of port extender 1. THen wait 200 milliseconds.
    */

    NextBit := 0x8000
    ReturnBit := (byte) (0x01)

    Shadows[1] &= 0xff

    mcp[1].Write( (byte) ((Shadows[1] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For bit 15 to bit 8 of port extender 1, turn each bit one at a time. After turning on a bit, wait for 200 milliseconds.
        Then ask the IEM for digital input values and check that only that bit is turned on in the response and then set the pass/fail
        flag. Write the test result to the database. 
    */

    for i:= 0;i < 8;i++ {
      Shadows[1] |= NextBit

      mcp[1].Write( (byte) ((Shadows[1] >> 8) & 0xff), MCP23S17.OLATB )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil && responseCount != 0 {
          err = errors.New("Bad Digital Inputs.")
        }

        log.Printf("%q", err)

        break
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 2 74 Volt Outputs (1 -> 8) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^response[3])
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      if response[3] != ^ReturnBit || err != nil {
        fmt.Printf(" Test 2 74 Volt Output %d Failed (got %X Expected %X)\r\n", i, response[3], ^ReturnBit)

        Test.Pass = false
        RetValue = 0
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[1] &= ^NextBit
      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
        Turn the top eight bits of port extender 1 back on.
    */

    Shadows[1] |= 0xff00

    mcp[1].Write( (byte) ((Shadows[1] >> 8) & 0xff), MCP23S17.OLATB )

    if Passed == 1 {
      fmt.Printf(" Test 2 74 Volt Outputs 1 to 8 Passed\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Turn the lower eight bits of port extender 1 and wait 200 milliseconds.
    */

    NextBit := 0x80
    ReturnBit := (byte) (0x01)

    Shadows[1] &= 0xff00

    mcp[1].Write( (byte) (Shadows[1] & 0xff), MCP23S17.OLATA )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For bit 7 through bit zero of port extender 1, turn on each bit one at a time. Ask the
        IEM for digital input values. Check that only current bit is on in the response and
        then set the pass/fail flag. Write the test result to the database.
        
    */

    for i := 0;i < 8;i++ {
      Shadows[1] |= NextBit

      mcp[1].Write( (byte) (Shadows[1] & 0xff), MCP23S17.OLATA )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 2 74 Volt Outputs (9 -> 16) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^response[4])
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      if response[4] != ^ReturnBit || err != nil {
        fmt.Printf(" Test 2 74 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 9, response[4], ^ReturnBit)

        Test.Pass = false
        RetValue = 0
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[1] &= ^NextBit
      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
        Turn the lower eight bits of port extender one back on.
    */

    Shadows[1] |= 0xff

    mcp[1].Write( (byte) (Shadows[1] & 0xff), MCP23S17.OLATA )

    if Passed == 1 {
      fmt.Printf(" Test 2 74 Volt Outputs 9 to 16 Passed\r\n")
    }
  }

  Passed = 1

  if err == nil {
    NextBit := 0x8000
    ReturnBit := (byte) (0x01)

    /*
        Turn off the top eight bits of port extender 2 and wait 200 milliseconds.
    */

    Shadows[2] &= 0xff

    mcp[2].Write( (byte) ((Shadows[2] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For bit 15 to bit 8 of port extender 2, turn on each bit one at a time. Wait 200 milliseconds 
        and ask the IEM for digital input values. Check that only the correct bit is on the response
        and then set the pass/fail flag. Write the test result to the data base.
    */

    for i := 0;i < 8;i++ {
      Shadows[2] |= NextBit

      mcp[2].Write( (byte) ((Shadows[2] >> 8) & 0xff), MCP23S17.OLATB )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 2 74 Volt Outputs (17 -> 24) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^response[5])
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      if response[5] != ^ReturnBit || err != nil {
        fmt.Printf(" Test 2 74 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 17, response[5], ^ReturnBit)

        Test.Pass = false
        RetValue = 0;
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[2] &= ^NextBit

      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
       Turn the top eight bits of prot extender 2 back on.
    */

    Shadows[2] |= 0xff00

    mcp[2].Write( (byte) ((Shadows[2] >> 8) & 0xff), MCP23S17.OLATB )

    if Passed == 1 {
      fmt.Printf(" Test 2 74 Volt Outputs 17 to 24 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    NextBit := 0x80
    ReturnBit := (byte) (0x01)

    /*
        Turn off the lower eight bits of port extender 2 and wait 200 milliseconds.
    */

    Shadows[2] &= 0xff00

    mcp[2].Write( (byte) (Shadows[2] & 0xff), MCP23S17.OLATA )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For bit 7 to bit 0 of port extender 2, turn on each bit one at a time. Wait 200 milliseconds and
        tne ask the IEM for digital input values. Check that only the current bit is on and then set
        the pass/fail flag. Write the test result to the database.
    */

    for i := 0;i < 8;i++ {
      Shadows[2] |= NextBit

      mcp[2].Write( (byte) (Shadows[2] & 0xff), MCP23S17.OLATA )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 2 74 Volt Outputs (25 -> 32) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^response[6])
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      if response[6] != ^ReturnBit || err != nil {
        fmt.Printf(" Test 2 74 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 25, response[6], ^ReturnBit)

        Test.Pass = false
        RetValue = 0;
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[2] &= ^NextBit

      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
        Turn the lower eight bits of port extender 2 back on.
    */

    Shadows[2] |= 0xff

    mcp[2].Write( (byte) (Shadows[2] & 0xff), MCP23S17.OLATA )

    if Passed == 1 {
      fmt.Printf(" Test 2 74 Volt Outputs 25 to 32 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    NextBit := 0x8000
    ReturnBit := (byte) (0x02)

    /*
        Turn off bit 15 and bit 14 of port extender 3 and wait 200 milliseconds.
    */

    Shadows[3] &= 0x3fff

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For bit 15 to bit 14 of port extender 3, turn on one bit at a time. Wait 200 milliseconds and
        ask the IEM for digital input values. Check that only the current bit is on and then set the
        pass/fail flag. Write the test result to the database.
    */

    for i := 0;i < 2;i++ {
      Shadows[3] |= NextBit

      mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 2 74 Volt Outputs (33 -> 34) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (response[7])
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      if ((response[7] & ReturnBit) != ReturnBit) || err != nil {
        fmt.Printf(" Test 2 74 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 33, response[7], ReturnBit)

        Test.Pass = false
        RetValue = 0
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[3] &= ^NextBit

      NextBit >>= 1

      ReturnBit >>= 1
    }

    /*
        Turn bit 15 and bit 14 of port extender 3 back on.
    */

    Shadows[3] |= 0xc000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    if Passed == 1 {
      fmt.Printf(" Test 2 74 Volt Outputs 33 and 34 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Turn off Bits 8->11 of port extender 0 and wait 200 milliseconds.
    */

    NextBit := 0x0800
    ReturnBit := (byte) (0x01)

    Shadows[0] &= 0xf0ff

    mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For each bit turn on each bit one at a time and ask the IEM for digital inputs. Wait 200 milliseconds,
        check that current bit is the only bit set and then set the pass/fail flag. Write the test result to the
        database.
    */

    for i := 0;i < 4;i++ {
      Shadows[0] |= NextBit

      mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 3 32 Volt Outputs (1 -> 4) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^(response[9] & 0xf) & 0xf)
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      test := (^(response[9] & 0x0f) & 0x0f)
 
      if test != ReturnBit || err != nil {
        fmt.Printf(" Test 3 32 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 1, test, ReturnBit)

        Test.Pass = false
        RetValue = 0;
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[0] &= ^NextBit

      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
         Turn bits 8->11 of port extender 0 back on.
    */

    Shadows[0] |= 0x0f00

    mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

    if Passed == 1 {
      fmt.Printf(" Test 3 32 Volt Outputs 1 to 4 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    NextBit := 0x80
    ReturnBit := (byte) (0x20)

    /*
        Turn off bits 6 and 7 of port extender 0 and wait 200 milliseconds.
    */

    Shadows[0] &= 0xff3f

    mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For each bit turn the bits on one at a time and wait 200 milliseconds. Ask the IEM for digital inputs.
        Check that current bit is the only bit set and then set the pass/fail flag. Write the test result to the
        database.
    */

    for i := 0;i < 2;i++ {
      Shadows[0] |= NextBit

      mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

      start = time.Now()

      t = time.Now()

      elapsed = t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 3 32 Volt Outputs (5 -> 6) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (response[9] & 0x30)
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      test := response[9] & 0x30
 
      if test != ReturnBit || err != nil {
        fmt.Printf(" Test 3 32 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 5, test, ReturnBit)

        Test.Pass = false
        RetValue = 0;
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[0] &= ^NextBit

      NextBit >>= 1

      ReturnBit >>= 1
    }

    /*
        Turn bits 6 and 7 of port extender 0 back on.
    */

    Shadows[0] |= 0xc0

    mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

    if Passed == 1 {
      fmt.Printf(" Test 3 32 Volt Outputs 5 and 6 Passed.\r\n")
    }
  }
  
  Passed = 1

  if err == nil {
    NextBit := 0x20
    ReturnBit := (byte) (0x01)

    /*
        Turn off bits 2 -> 5 of port extender 0 and wait 200 milliseconds.
    */

    Shadows[0] &= 0xffc3

    mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    /*
        For each bit turn one bit at a time and wait 200 milliseconds. Ask the IEM for digital inputs.
        Check that the current bit is the only one on and then set the pass/fail bit. Write the test
        result to the database.
    */

    for i := 0;i < 4;i++ {
      Shadows[0] |= NextBit

      mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

      start := time.Now()

      t := time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      responseCount, err = InformationSelectionCommand( DIGITAL_INPUTS, 0, response )

      if err != nil || responseCount != DIGITAL_INPUTS_RESPONSE_LEN {
        RetValue = 0
        Passed = 0

        if err == nil {
          err = errors.New("Bad Digital Inputs.")

          log.Printf("%q", err)
        }
      }

      Test := MatchTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 3 32 Volt Outputs (7 -> 10) Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Received = (int) (^response[8] & 0xf)
      Test.Expected = (int) (ReturnBit)
      Test.Pass = true

      test := ^response[8] & 0x0f

      if test != ReturnBit || err != nil {
        fmt.Printf(" Test 3 32 Volt Output %d Failed (Got %X Expected %X)\r\n", i + 7, test, ReturnBit)

        Test.Pass = false
        RetValue = 0;
        Passed = 0

        if err != nil {
          break
        }
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      Shadows[0] &= ^NextBit

      NextBit >>= 1

      ReturnBit <<= 1
    }

    /*
        Turn bits 2 -> 5 of port extender 0 back on.
    */

    Shadows[0] |= 0x3c

    mcp[0].Write( (byte) (Shadows[0] & 0xff), MCP23S17.OLATA )

    if Passed == 1 {
      fmt.Printf(" Test 3 32 Volt Outputs 7 to 10 Passed.\r\n")
    }

    /*
        Ask the IEM for the 80 Volt Analog Inputs.
    */

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        For each of the seven inputs check the value against the proper range and set the pass/fail flag.
        Write the test result to the data base.
    */

    for i := 0;i < 7;i++ {
      counts := (int) (response[2*i + 3])

      counts = (counts << 8) + (int) (response[2*i + 4])

      Test := UpperLimitTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 4 80 Volt Analog Inputs (1 -> 7) Low Voltage Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.UpperLimit = 25
      Test.Value = counts
      Test.Pass = true

      if counts > 25 {
        fmt.Printf(" Test 4 80 Volt Analog Input %d Failed (Got %d Expected <= 25)\r\n", i + 1, counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    /*
        Turn off bits 13 of port extender 3 and turn on bit 12 of port extender 3. Wait 200 milliseconds.
        Ask the IEM for 80 Volt analog inputs.
    */

    Shadows[3] &= ^0x3000

    Shadows[3] |= 0x1000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Inputs 1 to 7 Passed low voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and set the pass/fail flag. Write the test result to the 
        database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 1 Medium Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 1 Failed (Got %d Expected > 441 and < 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    counts = (int) (response[9])

    /*
        Check input 4 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (counts << 8) + (int) (response[10])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 4 Medium Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 4 Failed (Got %d Expected > 441 and < 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Set bit 13 of port extender 3 and wait 200 milliseconds. Ask the IEM for 80 Volt Analog Inputs.
    */

    Shadows[3] |= 0x2000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )
  
    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Inputs 1 and 4 Passed the medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 1 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 1 Failed (Got %d Expected  > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 4 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[9])

    counts = (counts << 8) + (int) (response[10])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 4 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 4 Failed (Got %d Expected  > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bits 12 and 13 of port extender 3 and turn on bit 11 of port extender 3. Wait 200 milliseconds and
        ask the IEM for 80 Volt Analog Inputs.
    */

    Shadows[3] &= ^0x3800

    Shadows[3] |= 0x800

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Inputs 1 and 4 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 2 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[5])

    counts = (counts << 8) + (int) (response[6])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 2 Medium Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 2 Failed (Got %d Expected > 441 and < 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 3 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[7])

    counts = (counts << 8) + (int) (response[8])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 3 Medium Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 3 Failed (Got %d Expected > 441 and < 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn on bit 12 of port extender 3 and wait 200 milliseconds. Ask the IEM for 80 Volt Analog Inputs.
    */

    Shadows[3] |= 0x2000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Inputs 2 and 3 Passed the medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 2 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[5])

    counts = (counts << 8) + (int) (response[6])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 2 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 2 Failed (Got %d Expected > 2214 and < 2705)\r\n", counts)

      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 3 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[7])

    counts = (counts << 8) + (int) (response[8])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 3 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 3 Failed (Got %d Expected > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bits 11 -> 13 of port extender 3, turn on bit 10 of port extender 3, and wait 200 milliseconds. Ask the IEM for 80 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x3c00

    Shadows[3] |= 0x400

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Inputs 2 and 3 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 6 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[13])

    counts = (counts << 8) + (int) (response[14])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 6 Medium Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 6 Failed (Got %d Expected > 441 and > 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 7 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[15])

    counts = (counts << 8) + (int) (response[16])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 7 Medium Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 7 Failed (Got %d Expected > 441 and > 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn on bit 13 of port extender 3 and wait 200 milliseconds. Ask the IEM for 80 Volt analog
        inputs.
    */

    Shadows[3] |= 0x2000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Inputs 6 and 7 Passed the medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 6 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[13])

    counts = (counts << 8) + (int) (response[14])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 6 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 6 Failed (Got %d Expected > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 7 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[15])

    counts = (counts << 8) + (int) (response[16])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 7 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 7 Failed (Got %d Expected > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn bits 10 -> 13 of port extender 3, turn on bit 9 of port extender 3, and wait 200 milliseconds. Ask the IEM for 80 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x3e00

    Shadows[3] |= 0x200

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Inputs 6 and 7 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 5 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[11])

    counts = (counts << 8) + (int) (response[12])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 5 Medium Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 441
    Test.MinValue = 538
    Test.Pass = true

    if counts <= 441 || counts >= 538 {
      fmt.Printf(" Test 4 80 Volt Analog Input 5 Failed (Got %d Expected > 441 and < 538)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn on bit 13 of port extender 3 and wait 200 milliseconds. Ask the IEM for 80 Volt analog
        inputs.
    */

    Shadows[3] |= 0x2000

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )
    
    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_80V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Input 5 Passed the medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 5 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[11])

    counts = (counts << 8) + (int) (response[12])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 4 80 Volt Analog Input 5 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 2214
    Test.MinValue = 2705
    Test.Pass = true

    if counts <= 2214 || counts >= 2705 {
      fmt.Printf(" Test 4 80 Volt Analog Input 5 Failed (Got %d Expected > 2214 and < 2705)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bits 8 -> 13 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x3f00

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 4 80 Volt Analog Input 5 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        For inputs 1 -> 6, check the input for the proper range, set the pass/fail flag, and write the test
        result to the database.
    */

    for i := 0;i < 6;i ++ {
      counts := (int) (response[2*i + 3])

      counts = (counts << 8) + (int) (response[2*i + 4])

      Test := RangeTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 5 10 Volt Analog Input (1 -> 6) Medium Voltage Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.Value = counts
      Test.MaxValue = 1995
      Test.MinValue = 2205
      Test.Pass = true

      if counts <= 1995 || counts >= 2205 {
        fmt.Printf(" Test 5 10 Volt Analog Input %d Failed (Got %d Expected > 1995 and < 2205)\r\n", i + 1, counts)

        Test.Pass = false
        RetValue = 0
        Passed = 0
      }

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )
    }

    /*
        Turn on bits 7 and 8 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] |= 0x180

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 1 to 6 Passed the medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 1 Low Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 1 Failed (Got %d Expected > 475 and > 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 2 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[5])

    counts = (counts << 8) + (int) (response[6])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 2 low Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 2 Failed (Got %d Expected > 475 and > 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 8 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x100

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 1 and 2 Passed the low voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Wrtie the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 1 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3040
    Test.MinValue = 3716
    Test.Pass = true

    if counts <= 3040 || counts >= 3716 {
      fmt.Printf(" Test 5 10 Volt Analog Input 1 Failed (Got %d Expected > 3040 and < 3716)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check imput 2 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[5])

    counts = (counts << 8) + (int) (response[6])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 2 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3040
    Test.MinValue = 3716
    Test.Pass = true

    if counts <= 3040 || counts >= 3716 {
      fmt.Printf(" Test 5 10 Volt Analog Input 2 Failed (Got %d Expected > 3040 and < 3716)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 7 of port extender 3, turn on bits 8 and 6 of port extender 3, and wait 200 milliseconds.
        Ask the IEM for 10 Volt analog inputs.
    */

    Shadows[3] &= ^0x80

    Shadows[3] |= 0x140

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 1 and 2 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 3 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[7])

    counts = (counts << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 3 Low Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 3 Failed (Got %d Expected > 475 and < 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 4 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[9])

    counts = (counts << 8) + (int) (response[10])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 4 Low Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 4 Failed (Got %d Expected > 475 and < 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 8 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x100

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Print(" Test 5 10 Volt Analog Inputs 3 and 4 Passed the low voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 3 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[7])

    counts = (counts << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 3 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3040
    Test.MinValue = 3716
    Test.Pass = true

    if counts <= 3040 || counts >= 3716 {
      fmt.Printf(" Test 5 10 Volt Analog Input 3 Failed (Got %d Expecteed > 3040 and < 3716)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 4 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[9])

    counts = (counts << 8) + (int) (response[10])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 4 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3325
    Test.MinValue = 3765
    Test.Pass = true

    if counts <= 3325 || counts >= 3675 {
      fmt.Printf(" Test 5 10 Volt Analog Input 4 Failed (Got %d Expecteed > 3325 and < 3675)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 6 of port extender 3, turn on bit 5 of port extender 3, and wait 200 milliseconds. Ask the IEM
        for 10 Volt analog inputs.
    */

    Shadows[3] &= ^0x60

    Shadows[3] |= 0x20

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    Shadows[3] |= 0x100

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 3 an 4 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 5 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[11])

    counts = (counts << 8) + (int) (response[12])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 5 Low Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 5 Failed (Got %d Expected > 475 and < 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 6 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[13])

    counts = (counts << 8) + (int) (response[14])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 6 Low Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 475
    Test.MinValue = 581
    Test.Pass = true

    if counts <= 475 || counts >= 581 {
      fmt.Printf(" Test 5 10 Volt Analog Input 6 Failed (Got %d Expected > 475 and < 581)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 8 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x100

    mcp[3].Write( (byte) ((Shadows[3] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_10V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 5 and 6 Passed the low voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 5 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[11])

    counts = (counts << 8) + (int) (response[12])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 5 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3040
    Test.MinValue = 3716
    Test.Pass = true

    if counts <= 3040 || counts >= 3716 {
      fmt.Printf(" Test 5 10 Volt Analog Input Failed 5 (Got %d Expected > 3040 and < 3716)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check input 6 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts = (int) (response[13])

    counts = (counts << 8) + (int) (response[14])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 5 10 Volt Analog Input 6 High Voltage Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3040
    Test.MinValue = 3716
    Test.Pass = true

    if counts <= 3040 || counts >= 3716 {
      fmt.Printf(" Test 5 10 Volt Analog Input Failed 6 (Got %d Expected > 3040 and < 3716)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bits 3 -> 5 of port extender 3 and wait 200 milliseconds. Ask the IEM for 10 Volt
        analog inputs.
    */

    Shadows[3] &= ^0x38

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )
    
    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_16V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 5 10 Volt Analog Inputs 5 and 6 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := UpperLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 6 16 Volt Analog Input 1 Low Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.UpperLimit = 125
    Test.Pass = true

    if counts > 125 {
      fmt.Printf(" Test 6 16 Volt Ananlog Input 1 Failed (Got %d Expected < 125)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn on bit 3 of port extender 3 and wait 200 milliseconds. Ask the IEM for 16 Volt
        analog inputs.
    */

    Shadows[3] |= 0x08

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )
    
    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_16V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 6 16 Volt Analog Input 1 Passed the low voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 6 16 Volt Analog Input 1 Medium Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 450
    Test.MinValue = 550
    Test.Pass = true

    if counts <= 450 || counts >= 550 {
      fmt.Printf(" Test 6 16 Volt Analog Input 1 Failed (Got %d Expected > 475 and < 525)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
       Turn on bit 4 of port extender 3 and wait 200 milliseconds. Ask the IEM for 16 Volt
       analog inputs.
    */

    Shadows[3] |= 0x10

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )
    
    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( ANALOG_INPUTS, ANALOG_16V_INPUTS_32, response )

    if err != nil || responseCount != ANALOG_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 6 16 Volt Analog Input 1 Passed medium voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check input 1 for the proper range and then set the pass/fail flag. Write the test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 6 16 Volt Analog Input 1 High Voltage Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3060
    Test.MinValue = 3740
    Test.Pass = true

    if counts <= 3060 || counts >= 3740 {
      fmt.Printf(" Test 6 16 Volt Analog Input 1 Failed (Got %d Expected > 6821 and < 7539)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn off bit 4 of port extender 3 and wait 200 milliseconds.
    */

    Shadows[3] &= ^0x10

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(200)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 6 16 Volt Analog Input 1 Passed the high voltage test.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the user to set his pressure regulator to proper setting.
    */

    fmt.Printf("\r\nPlease adjust the pressure regulator to 30 PSI.\r\n")

    fmt.Printf("Hit any key when ready.\r\n")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    ConsoleInput.Reset(os.Stdin)

    /*
        Ask the user if he wants to run the pressure tests.
    */

    if group == 1 {
      fmt.Printf("\r\nDo you wish to run Pressure Tests y or n (y default) : ")
    } else {
      fmt.Printf("\r\nDo you wish to test PT1 y or n (y default) : ")
    }

    char = (byte) (0)

    err1 = (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    ConsoleInput.Reset(os.Stdin)

    /*
        If he doesn't want to run the pressure tests, then set the skip flag.
    */

    if char == 'n' {
      skip = 1
    } 

    /*
        Ask the IEM for an initial pressure reading to elimate and zero pressure
        offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
       Tell the user to apply pressure to PT1. He's got thirty seconds to do it.
       If we detect the correct pressure within that 30 seconds, then we move on.
       If we don't detect the correct pressure within the 30 seconds, then we
       set the pass/fail flag.
    */

    fmt.Printf("\r\nApply 30 PSI to IEM pressure input port PT1.\r\n")

    zeroPressureReading = (int) (response[3])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[4])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if i >= 150 || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT1 Failed (Got %d Expected > 589 and < 721)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")
        }

        break
      } else {
        counts = (int) (response[3])

        counts = (counts << 8) + (int) (response[4])

        if (counts - zeroPressureReading) >= 589 && (counts - zeroPressureReading) <= 721 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT1 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 589
    Test.MinValue = 721
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT1 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT2 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure inputs to use to eliminate
        any zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT2.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT2.\r\n")

    zeroPressureReading = (int) (response[5])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[6])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has 30 seconds to apply pressure to PT2. If we detect the
        correct pressure within the 30 seconds, then we move on. If we don't
        detect the correct pressure within the 30 second period, then we the 
        set the pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT2 Failed (Got %d Expected > 589 and < 721)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[5])

        counts = (counts << 8) + (int) (response[6])

        if counts - zeroPressureReading >= 589 && counts - zeroPressureReading <= 721 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT2 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 589
    Test.MinValue = 721
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT2 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT3 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure readings to use to eliminate any
        zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }


  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT3.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT3.\r\n")

    zeroPressureReading = (int) (response[7])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[8])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has thirty seconds to apply the correct pressure to PT3. If we
        see the correct pressure on PT3 within the 30 second period, then we move
        on. If we don't see the correct pressure within the thirty second period
        then we set the pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT3 Failed (Got %d Expected > 589 and < 721)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[7])

        counts = (counts << 8) + (int) (response[8])

        if counts - zeroPressureReading >= 589 && counts - zeroPressureReading <= 721 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT3 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 589
    Test.MinValue = 721
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT3 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT4 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure readings that we can use to eliminate any
        zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT4.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT4.\r\n")

    zeroPressureReading = (int) (response[9])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[10])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has 30 seconds to apply the correct pressure to PT4. If we detect
        correct pressure before the end of the 30 second period then we move on.
        If we don't detect the correct pressure, then we set the pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT4 Failed (Got %d Expected > 589 and < 721)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[9])

        counts = (counts << 8) + (int) (response[10])

        if counts - zeroPressureReading >= 589 && counts - zeroPressureReading <= 721 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT4 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 589
    Test.MinValue = 721
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT4 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT5 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure readings that we can use to eliminate any
        zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT5.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT5.\r\n")

    zeroPressureReading = (int) (response[11])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[12])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has 30 seconds to apply correct pressure to PT5. If we detect the
        correct pressure withing the 30 second period, then we move on. If we do
        not detect the correct pressure within the 30 second period then we set the
        pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT5 Failed (Got %d Expected > 589 and < 721)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[11])

        counts = (counts << 8) + (int) (response[12])

        if counts - zeroPressureReading >= 442 && counts - zeroPressureReading <= 541 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT5 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 589
    Test.MinValue = 721
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT5 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT6 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
       Ask the IEM for an initial set of pressure readings that we can use to eliminate any
       zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT8.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT6.\r\n")

    zeroPressureReading = (int) (response[13])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[14])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has 30 seconds to apply the correct pressure to PT6. If we detect
        the correct pressure within the 30 second period, then we move on. If we
        do not detect the correct pressure within the 30 second period, then we 
        set the pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT6 Failed (Got %d Expected >= 4000)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[13])

        counts = (counts << 8) + (int) (response[14])

        if counts - zeroPressureReading >= 4000 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Wrtie the test result to the database.
    */

    Test := LowerLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT6 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.LowerLimit = 4000
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT6 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1
  
  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT7 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure readings that we can user to eliminate any
        zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply pressure to PT7.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT7.\r\n")

    zeroPressureReading = (int) (response[15])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[16])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := 0

    /*
        The user has 30 seconds to apply the correct pressure to PT7. If we see 
        the correct pressure within the 30 second period, then we move on. If we
        do not see the correct pressure within the 30 second period, the we set
        the pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Preesure Input PT7 Failed (Got %d Expected >= 4000)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[15])

        counts = (counts << 8) + (int) (response[16])

        if counts - zeroPressureReading >= 4000 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(200)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := LowerLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT7 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.LowerLimit = 4000
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT7 Passed.\r\n")
    } else {
      Test.Pass = false
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  Passed = 1

  if group == 0 {
    skip = 0
  }

  if err == nil {
    if group == 0 {
      ConsoleInput.Reset(os.Stdin)

      fmt.Printf("\r\nDo you wish to test PT8 y or n (y default) : ")

      char := (byte) (0)

      err1 := (error) (nil)

      char, err1 = ConsoleInput.ReadByte()

      for err1 != nil && char == 0 {
        char, err1 = ConsoleInput.ReadByte()
      }

      ConsoleInput.Reset(os.Stdin)

      if char == 'n' {
        skip = 1
      } 
    }

    /*
        Ask the IEM for an initial set of pressure readings that we can use to eliminate any
        zero pressure offset.
    */

    responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

    if err != nil || responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Analog Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil && skip == 0 {
    /*
        Tell the user to apply the correct pressure to PT8.
    */

    fmt.Printf("\r\n\nApply 30 PSI to IEM pressure input port PT8.\r\n")

    zeroPressureReading = (int) (response[17])

    zeroPressureReading = (zeroPressureReading << 8) + (int) (response[18])

    start := time.Now()

    t := time.Now()

    i := 0

    counts := (int) (0)

    /*
        The user has 30 seconds to apply the correct pressure to PT8. If we detect the
        correct pressure within the 30 second period, then we move on. If we do not 
        detect the correct pressure within the 30 second period, then we set the 
        pass/fail flag.
    */

    for err == nil {
      responseCount, err = InformationSelectionCommand( PRESSURE_INPUTS, 0, response )

      if (i >= 150) || (err != nil) {
        RetValue = 0
        Passed = 0

        fmt.Printf("\r Test 7 Pressure Input PT8 Failed (Got %d Expected >= 4000)\r\n", counts - zeroPressureReading)

        if err == nil && responseCount != PRESSURE_INPUTS_RESPONSE_LEN {
          err = errors.New("Bad Pressure Inputs")

          log.Printf("%q", err)
        }

        break
      } else {
        counts = (int) (response[17])

        counts = (counts << 8) + (int) (response[18])

        if counts - zeroPressureReading >= 4000 {
          break
        }
      }

      t = time.Now()

      elapsed := t.Sub(start)

      for elapsed < time.Duration(500)*time.Millisecond {
        t = time.Now()

        elapsed = t.Sub(start)
      } 

      start = t

      i += 1

      fmt.Printf("\r%2d", (30 - i/5))
    } 

    /*
        Write the test result to the database.
    */

    Test := LowerLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 7 Pressure Input PT8 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.LowerLimit = 4000
    Test.Pass = true

    if Passed == 1 {
      fmt.Printf("\r\n Test 7 Pressure Input PT8 Passed.\r\n")
    } else {
      Test.Pass = true
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  if err == nil {
    /*
        Turn off bit 2 of port extender 3, tell the IEM to set the 
        zero crossing reference to 0 volts, and wait a second.
    */

    Shadows[3] &= ^0x04

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    responseCount, err = SetSpeedSensorRefCommand( ZERO_CROSSING_0V )

    if err != nil || responseCount != 1 {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Speed Sensor Reference Error.")
      }
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(1)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 
  }

  Passed = 1

  if err == nil {
    /*
        Ask the IEM for speed sensor inputs.
    */

    responseCount, err = InformationSelectionCommand( SPEED_SENSOR_INPUTS, 0, response )

    if err != nil || responseCount != SPEED_SENSOR_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Speed Sensor Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
       Check the speed sensor input for the proper range and then set the pass/fail flag. Write the
       test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 8 Speed Sensor Input for 0 Volt Crossings Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 102
    Test.MinValue = 98
    Test.Pass = true

    if counts <= 98 || counts >= 102 {
      fmt.Printf(" Test 8 Speed Sensor Input for 0 Volt Coroosings Failed (Got %d Expected > 98 and < 102)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
       Turn on bit 2 of port extender 3, tell the IEM to set the zero crossing
       detector reference to 2.5 Volts, and wait 500 milliseconds.
    */

    Shadows[3] |= 0x04

    mcp[3].Write( (byte) (Shadows[3] & 0xff), MCP23S17.OLATA )

    responseCount, err = SetSpeedSensorRefCommand( ZERO_CROSSING_2_5V )

    if err != nil || responseCount != 1 {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Speed Sensor Reference Error.")

        log.Printf("%q", err)
      }
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(500)*time.Millisecond {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 8 Speed Sensor Input for 0 Volt Crossings Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the IEM for speed sensor inputs.
    */

    responseCount, err = InformationSelectionCommand( SPEED_SENSOR_INPUTS, 0, response )

    if err != nil || responseCount != SPEED_SENSOR_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Speed Sensor Inputs.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Check the speed sensor input for the proper range and then set the pass/fail flag. Write the
        test result to the database.
    */

    counts := (int) (response[3])

    counts = (counts << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 8 Speed Sensor Input for 2.5 Volt Crossings Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 102
    Test.MinValue = 98
    Test.Pass = true

    if counts <= 98 || counts >= 102 {
      fmt.Printf(" Test 8 Speed Sensor Input for 2.5 Volt crossings Failed (Got %d Expected > 98 and < 102)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn bit 13 of port extender 0, wait a second, and ask the IEM for 4-20 mA
        inputs.
    */

    Shadows[0] |= 0x2000

    mcp[0].Write( (byte) ((Shadows[0] >> 8) & 0xff), MCP23S17.OLATB )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(2)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( CUR_4_20MA_INPUTS, 0, response )

    if err != nil || responseCount != CUR_4_20MA_INPUTS_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad 4-20 Ma Inputs.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 8 Speed Sensor Input for 2.5 Volt crossings Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check channel 8 for the proper range and then set the pass/fail flag. Write the
        test result to the database
    */

    counts := (int) (response[17])

    counts = (counts << 8) + (int) (response[18])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 9 4-20 mA Channel 8 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = counts
    Test.MaxValue = 3708
    Test.MinValue = 3492
    Test.Pass = true

    if counts <= 3492 || counts >= 3708 {
      fmt.Printf(" Test 9 4-20 mA Channel 8 Failed (Got %d Expected > 3492 and < 3708)\r\n", counts)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
       Ask the IEM for status vector for the communications and I/O processors.
    */

    responseCount, err = InformationSelectionCommand( STATUS_VECTOR, COMM_PROC_AND_IO_PROC_12, response )

    if err != nil || responseCount != STATUS_VECTOR_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Status Vector.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 9 Channel 1 Passed.\r\n")
    }
  }

  fmt.Printf("\r\n")

  if err == nil {
    /*
        Check the post status of the flash test and set the pass/fail flag. Write the
        test result to the database.
    */

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 10 Flash Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & FLASH_TEST_PASSED_01) != FLASH_TEST_PASSED_01 {
      Test.Pass = false
      RetValue = 0
      
      fmt.Printf("IEM Main CPU Flash Test Failed.\r\n")
    } else {
      fmt.Printf("IEM Main CPU Flash Test Passed.\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check the post status of the communications check and then set the pass/fail
        flag. Write the test result to the database.
    */

    Test = PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 13 Communication Check Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & CP_TO_SP_LINK_ACTIVE_01) != CP_TO_SP_LINK_ACTIVE_01 {
      Test.Pass = false
      RetValue = 0
      
      fmt.Printf("IEM Main CPU Communication Check Failed.\r\n")
    } else {
      
      fmt.Printf("IEM Main CPU Communication Check Passed.\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  if err == nil {
    /*
        Ask the IEM for the hardware version of the communications processor.
    */

    responseCount, err = InformationSelectionCommand( HW_VERSION, COMM_PROC_02, response )

    if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Hardware Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the harware version of the communication processor to the database.
    */

    Test := HardwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 11 Communication Processor Hardware Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.HardwareVersion = (int) (response[3])
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Hardware Version for Communications Processor %d\r\n", response[3])

    /*
        Ask IEM for the hardware version of the I/O processor.
    */

    responseCount, err = InformationSelectionCommand( HW_VERSION, IO_PROCESSOR_02, response )

    if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Hardware Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
   /*
        Write the hardware version for the I/O processor to the database.
   */


    Test := HardwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 11 IO Processor Hardware Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.HardwareVersion = (int) (response[3])
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Hardware Version for IO Processor %d\r\n", response[3])

    if IEMType == IEM_WITH_ALERTER {
      /*
          Ask the IEM for the hardware version of the ABCM.
      */

      responseCount, err = InformationSelectionCommand( HW_VERSION, ABCM_02, response )

      if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
        RetValue = 0

        if err == nil {
          err = errors.New("Bad Hardware Version.")

          log.Printf("%q", err)
        }
      }
    }
  }

  if err == nil {
    if IEMType == IEM_WITH_ALERTER {
      /*
          Write the hardware version of the ABCM to the database.
      */

      Test := HardwareVersionTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 11 ABCM Hardware Version Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.HardwareVersion = (int) (response[3])
      Test.Pass = true

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      fmt.Printf("Hardware Version for ABCM %d\r\n", response[3])

      /*
          Ask the IEM for the hardware version of the ADCM.
      */

      responseCount, err = InformationSelectionCommand( HW_VERSION, ADCM_02, response )

      if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
        RetValue = 0

        if err == nil {
          err = errors.New("Bad Hardware Version.")

          log.Printf("%q", err)
        }
      }
    }
  }

  if err == nil {
    if IEMType == IEM_WITH_ALERTER {
      /*
          Write the hardware version of the ADCM to the database.
      */

      Test := HardwareVersionTestResult{}

      Test.AssemblyPartNumber = AssemblyPartNumber
      Test.AssemblySerialNumber = AssemblySerialNumber
      Test.PartNumber = MainCircuitPartNumber
      Test.SerialNumber = MainCircuitSerialNumber
      Test.TestName = "Main CPU Test 11 ADCM Hardware Version Test"

      timeDate := time.Now()
      hour, min, sec := timeDate.Clock()
      year, month, day := timeDate.Date()

      Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
      Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
      Test.HardwareVersion = (int) (response[3])
      Test.Pass = true

      Test.SetID(couchdb.GenerateUUID())

      err = couchdb.Store( TestDB, &Test )

      fmt.Printf("Hardware Version for ADCM %d\r\n", response[3])
    }

    /*
        Ask the IEM for the software version of the communications processor.
    */

    responseCount, err = InformationSelectionCommand( SW_VERSION, COMM_PROC_01, response )

    if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Software Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the software version of the communications processor to the database.
    */

    Test := SoftwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 12 Communications Processor Software Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
    version := (string) (response[3:3 + index])
    Test.SoftwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Software Version for Communications Processor %s\r\n", response[3:responseCount - 3])

    /*
        Ask the IEM for the software version of the I/O processor.
    */

    responseCount, err = InformationSelectionCommand( SW_VERSION, IO_PROCESSOR_01, response )

    if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Hardware Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the software version of the I/O processor to the database.
    */

    Test := SoftwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 12 IO Processor Software Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
    version := (string) (response[3:3 + index])
    Test.SoftwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Software Version for IO Processor %s\r\n", response[3:responseCount - 3])

    if IEMType == IEM_WITH_ALERTER {
      /*
          Ask the IEM for the software version of the ADCM.
      */

      responseCount, err = InformationSelectionCommand( SW_VERSION, ADCM_01, response )

      if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
        RetValue = 0

        if err == nil {
          err = errors.New("Bad Software Version.")

          log.Printf("%q", err)
        }
      }

      if err == nil {
        /*
            Write the software version of the ADCM to the database.
        */

        Test := SoftwareVersionTestResult{}

        Test.AssemblyPartNumber = AssemblyPartNumber
        Test.AssemblySerialNumber = AssemblySerialNumber
        Test.PartNumber = MainCircuitPartNumber
        Test.SerialNumber = MainCircuitSerialNumber
        Test.TestName = "Main CPU Test 12 ADCM Software Version Test"

        timeDate := time.Now()
        hour, min, sec := timeDate.Clock()
        year, month, day := timeDate.Date()

        Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
        Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
        index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
        version := (string) (response[3:3 + index])
        Test.SoftwareVersion = version
        Test.Pass = true

        Test.SetID(couchdb.GenerateUUID())

        err = couchdb.Store( TestDB, &Test )

        fmt.Printf("Software Version for ADCM Processor %s\r\n", response[3:responseCount - 3])

        /*
            Ask the IEm for the softwar version of the ABCM processor A.
        */

        responseCount, err = InformationSelectionCommand( SW_VERSION, ABCM_PROC_A_01, response )

        if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
          RetValue = 0

          if err == nil {
            err = errors.New("Bad Software Version.")

            log.Printf("%q", err)
          }
        }
      }

      if err == nil {
        /*
            Write the software version of the ABCM processor A to the database.
        */

        Test := SoftwareVersionTestResult{}

        Test.AssemblyPartNumber = AssemblyPartNumber
        Test.AssemblySerialNumber = AssemblySerialNumber
        Test.PartNumber = MainCircuitPartNumber
        Test.SerialNumber = MainCircuitSerialNumber
        Test.TestName = "Main CPU Test 12 ABCM Processor A Software Version Test"

        timeDate := time.Now()
        hour, min, sec := timeDate.Clock()
        year, month, day := timeDate.Date()

        Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
        Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
        index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
        version := (string) (response[3:3 + index])
        Test.SoftwareVersion = version
        Test.Pass = true

        Test.SetID(couchdb.GenerateUUID())

        err = couchdb.Store( TestDB, &Test )

        fmt.Printf("Software Version for ABCM Processor A %s\r\n", response[3:responseCount - 3])

        /*
            Ask the IEM for the software version of the ABCM processor B.
        */

        responseCount, err = InformationSelectionCommand( SW_VERSION, ABCM_PROC_B_01, response )

        if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
          RetValue = 0

          if err == nil {
            err = errors.New("Bad Software Version.")

            log.Printf("%q", err)
          }
        }
      }

      if err == nil {
        /*
            Write the software version of the ABCM processor B to the database.
        */

        Test := SoftwareVersionTestResult{}

        Test.AssemblyPartNumber = AssemblyPartNumber
        Test.AssemblySerialNumber = AssemblySerialNumber
        Test.PartNumber = MainCircuitPartNumber
        Test.SerialNumber = MainCircuitSerialNumber
        Test.TestName = "Main CPU Test 12 ABCM Processor B Software Version Test"

        timeDate := time.Now()
        hour, min, sec := timeDate.Clock()
        year, month, day := timeDate.Date()

        Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
        Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
        index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
        version := (string) (response[3:3 + index])
        Test.SoftwareVersion = version
        Test.Pass = true

        Test.SetID(couchdb.GenerateUUID())

        err = couchdb.Store( TestDB, &Test )

        fmt.Printf("Software Version for ABCM Processor B %s\r\n", response[3:responseCount - 3])
      }
    }
  }

  
  if err == nil {
    /*
        Ask the IEM for network addresses.
    */

    responseCount, err = InformationSelectionCommand( NETWORK_INTERFACE_PARAMS, 0, response )

    if err != nil || responseCount != NETWORK_INTERFACE_PARAMS_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Network Parameters.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Extract the network address and ping that address.
    */

    address := fmt.Sprintf("%d.%d.%d.%d\r\n", response[3], response[4], response[5], response[6])

    out, _ := exec.Command("ping", address, "-c 3", "-w 3").Output()

    fmt.Printf("%s", out)

    /*
       Check the results of the ping for all responses received and then set the pass/fail flag.
       Write the test result to the database.
    */

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = MainCircuitPartNumber
    Test.SerialNumber = MainCircuitSerialNumber
    Test.TestName = "Main CPU Test 15 Network Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if !(strings.Contains(string(out), "0% packet loss")) {
      Test.Pass = false
      RetValue = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
  }

  /*
       Set the IEm tester back to its initial condition.
  */

  _, err1 := Init( mcp )

  if err == nil {
    err = err1
  }

  return RetValue, err
}

/*
    Procedure Name : Test_ABCM

    Description    : This routine performs all of the ABCM tests.

    Arguments      : mcp - Slice of pointers for the port extender structures

    Return Value   : Pass/Fail flag
                     Any error encountered during the tests.
*/

func Test_ABCM( mcp []*MCP23S17.MCP23S17 ) (int, error) {
  var err error = nil
  var responseCount int

  response := make([] byte, 50)

  RetValue := 1
  Passed := 1

  /*
      Wait two seconds and then ask the IEM for ABCM Monitored Voltages.
  */

  start := time.Now()

  t := time.Now()

  elapsed := t.Sub(start)

  for elapsed < time.Duration(2)*time.Second {
    t = time.Now()

    elapsed = t.Sub(start)
  } 

  responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ABCM_03, response )

  if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
    RetValue = 0

    if err == nil {
      err = errors.New("Bad Monitored Voltages.")

      log.Printf("%q", err)
    }
  }

  if err == nil {
    /*
        Check the 12 Volt entry for the proper range and then set the pass/fail flag. Write the
        test result to the database.
    */

    voltage := (int) (response[3])

    voltage = (voltage << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 1 12 Volt Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 11400
    Test.MinValue = 12600
    Test.Pass = true

    if voltage <= 11400 || voltage >= 12600 {
      fmt.Printf(" Test 1 12 Volts Failed (Got %d Expected > 11400 and < 12600)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )
   
    /*
        Check the 3.3 Volt entry for the proper range and then set the pass/fail flag. Write the
        test result to the database.
    */

    voltage = (int) (response[5])

    voltage = (voltage << 8) + (int) (response[6])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 1 3.3 Volt Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 3135
    Test.MinValue = 3465
    Test.Pass = true

    if voltage <= 3135 || voltage >= 3465 {
      fmt.Printf(" Test 1 3.3 Volts Failed (Got %d Expected > 3135 and < 3465)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Wait a second and then ask the IEM for the ABCM status vector.
    */

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(1)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    responseCount, err = InformationSelectionCommand( STATUS_VECTOR, ABCM_12, response )

    if err != nil || responseCount != STATUS_VECTOR_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Status Vector.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 1 Monitored Voltages Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check the 74 Volts detected status and then set the pass/fail flag. Write the test result to the database.
    */

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 2 74 Volt Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & DETECTED_74V) != DETECTED_74V {
      Test.Pass = false
      RetValue = 0
      Passed = 0
    
      fmt.Printf("ABCM 74 Volts not detected\r\n")
    } else {
      fmt.Printf("ABCM 74 Volts detected\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check the status of the post flash test and then set the pass/fail flag.
        Write the test result to the database.
    */

    Test = PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 3 Flash Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & FLASH_TEST_PASSED_04) != FLASH_TEST_PASSED_04 {
      Test.Pass = false
      RetValue = 0
      Passed = 0

      fmt.Printf("ABCM Flash Test didn't pass.\r\n")
    } else {
      fmt.Printf("ABCM Flash Test passed.\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check the A to B communications check status and then set the pass/fail flag.
        Write the test result to the database.
    */

    Test = PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 6 A to B Communications Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & A_TO_B_COMM_LINK_ACTIVE) != A_TO_B_COMM_LINK_ACTIVE {
      Test.Pass = false
      RetValue = 0
      Passed = 0

      fmt.Printf("ABCM Inter-processor Communication Check failed.\r\n")
    } else {
      fmt.Printf("ABCM Inter-processor Communication Check passed.\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check that both the A and B mag valve drives are currently off and the
        set the pass/fail flag. Write the test result to the database.
    */

    Test1 := MatchTestResult{}

    Test1.AssemblyPartNumber = AssemblyPartNumber
    Test1.AssemblySerialNumber = AssemblySerialNumber
    Test1.PartNumber = ABCMPartNumber
    Test1.SerialNumber = ABCMSerialNumber
    Test1.TestName = "ABCM Test 7 A and B Mag Valve off Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test1.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test1.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test1.Received = (int) (response[3] & (ABCM_A_MAG_VALVE_DRIVE | ABCM_B_MAG_VALVE_DRIVE))
    Test1.Expected = 0
    Test1.Pass = true

    if (response[3] & ABCM_A_MAG_VALVE_DRIVE) == ABCM_A_MAG_VALVE_DRIVE ||
       (response[3] & ABCM_B_MAG_VALVE_DRIVE) == ABCM_B_MAG_VALVE_DRIVE {

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test1.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test1 )

    /*
        Ask the IEM for the hardware version of the ABCM.
    */

    responseCount, err = InformationSelectionCommand( HW_VERSION, ABCM_02, response )

    if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Hardware Version.")

        log.Printf("%q", err)
      }
    }

    if Passed == 1 {
      fmt.Printf(" Test 7 Both A and B Feedbacks are false as required.\r\n")
    }
  }

  if err == nil {
    /*
        Write the ABCM hardware version to the database.
    */

    HardwareVersion := (int) (response[3])

    Test := HardwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 4 Hardware Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.HardwareVersion = HardwareVersion
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("ABCM Hardware Version %d\r\n", HardwareVersion )

    /*
        Ask the IEM for the software version for ABCM processor A.
    */

    responseCount, err = InformationSelectionCommand( SW_VERSION, ABCM_PROC_A_01, response )

    if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Software Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the software version for the ABCM processor A to the database.
    */

    Test := SoftwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 5 Software Version Processor A Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
    version := (string) (response[3:3 + index])
    Test.SoftwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Software Version for ABCM Processor A %s\r\n", response[3:responseCount - 3])

    /*
        Ask the IEM for the software version of the ABCM processor B.
    */

    responseCount, err = InformationSelectionCommand( SW_VERSION, ABCM_PROC_B_01, response )

    if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Software Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the software version of the ABCM processor B to the database.
    */

    Test := SoftwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 5 Software Version Processor B Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
    version := (string) (response[3:3 + index])
    Test.SoftwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("Software Version for ABCM Processor B %s\r\n", response[3:responseCount - 3] )

    /*
        Set the A mag drive signal high and the B mag drive signal low on the ABCM and
        wait 5 seconds.
    */

    _,err = SetABCMMagValveDriveStateCommand( ABCM_PROC_A_92, 1 )

    _,err = SetABCMMagValveDriveStateCommand( ABCM_PROC_B_92, 0 )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 
  }

  if err == nil {
    /*
        Ask the IEM for the ABCM status vector.
    */

    responseCount, err = InformationSelectionCommand( STATUS_VECTOR, ABCM_12, response )

    if err != nil || responseCount != STATUS_VECTOR_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Status Vector.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check that the A mag valve drive signal is high and the B mag valve drive signal
        is low and set the pass/fail flag. Write the test result to the database.
    */

    status := (int) (response[3])

    const ABCM_A_MAG_VALVE_DRIVE   = 0x04
    const ABCM_B_MAG_VALVE_DRIVE   = 0x08
    
    Test := MatchTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 7 Mag Valve Drive A 1 Mag Valve Drive B 0 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Received = (int) (response[3] & (ABCM_A_MAG_VALVE_DRIVE | ABCM_B_MAG_VALVE_DRIVE))
    Test.Expected = ABCM_A_MAG_VALVE_DRIVE
    Test.Pass = true

    if (status & ABCM_A_MAG_VALVE_DRIVE) != ABCM_A_MAG_VALVE_DRIVE ||
       (status & ABCM_B_MAG_VALVE_DRIVE) == ABCM_B_MAG_VALVE_DRIVE {

      AState := 0

      if status & ABCM_A_MAG_VALVE_DRIVE == ABCM_A_MAG_VALVE_DRIVE {
        AState = 1
      }

      BState := 0

      if status & ABCM_B_MAG_VALVE_DRIVE == ABCM_B_MAG_VALVE_DRIVE {
        BState = 1
      }

      fmt.Printf(" Test 7 Feedback State Failed (Got A %d B %d Expected A 1 B 0)\r\n", AState, BState)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Set the B mag valve drive signal high and wait five seconds.
    */

    _,err = SetABCMMagValveDriveStateCommand( ABCM_PROC_B_92, 1 )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 7 Feedback State A 1 B 0 Passed.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the IEM for the ABCM status vector.
    */

    responseCount, err = InformationSelectionCommand( STATUS_VECTOR, ABCM_12, response )

    if err != nil || responseCount != STATUS_VECTOR_RESPONSE_LEN {
      RetValue = 0
      Passed = 0

      if err == nil {
        err = errors.New("Bad Status Vector.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Check that the A mag valve drive signal is high and the B mag valve drive
        signal is high. Then set the pass/fail flag. Write the test result to the 
        database.
    */

    status := (int) (response[3])

    Test := MatchTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ABCMPartNumber
    Test.SerialNumber = ABCMSerialNumber
    Test.TestName = "ABCM Test 7 Mag Valve Drive A 1 Mag Valve Drive B 1 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Received = (int) (response[3] & (ABCM_A_MAG_VALVE_DRIVE | ABCM_B_MAG_VALVE_DRIVE))
    Test.Expected = ABCM_A_MAG_VALVE_DRIVE | ABCM_B_MAG_VALVE_DRIVE
    Test.Pass = true

    if (status & ABCM_A_MAG_VALVE_DRIVE) != ABCM_A_MAG_VALVE_DRIVE ||
       (status & ABCM_B_MAG_VALVE_DRIVE) != ABCM_B_MAG_VALVE_DRIVE {

      AState := 0

      if status & ABCM_A_MAG_VALVE_DRIVE == ABCM_A_MAG_VALVE_DRIVE {
        AState = 1
      }

      BState := 0

      if status & ABCM_B_MAG_VALVE_DRIVE == ABCM_B_MAG_VALVE_DRIVE {
        BState = 1
      }

      fmt.Printf(" Test 7 Feedback State Failed (Got A %d B %d Expected A 1 B 1)\r\n", AState, BState)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    } 

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    gpio := mcp[4].Read( MCP23S17.GPIOA )

    if (gpio & 1) != 1 {
      RetValue = 0
      Passed = 0
    }

    if Passed == 1 {
      fmt.Printf(" Test 7 Feedback State A 1 B 1 Passed.\r\n")
    }

    /*
        Set both the A and B mag valve drive signals low.
    */

    _,err = SetABCMMagValveDriveStateCommand( ABCM_PROC_A_92, 0 )
  }

  if err == nil {
    _,err = SetABCMMagValveDriveStateCommand( ABCM_PROC_B_92, 0 )
  }

  /*
      Take the IEM tester back to its initial state.
  */

  _, err1 := Init( mcp )

  if err == nil {
    err = err1
  }

  return RetValue, err
}

/*
    Procedure Name : Test_ADCM

    Description    : This routine performs all of the ADCM tests.

    Arguments      : mcp - Slice of pointers to the port extender control structures.

    Return Value   : Pass/Fail flag
                     Any error encountered during the tests.
*/

func Test_ADCM( mcp []*MCP23S17.MCP23S17 ) (int, error) {
  var err error = nil
  var responseCount int
  var intensity int

  response := make([] byte, 50)

  RetValue := 1
  Passed := 1

  /*
      Ask the IEM for the ADCM monitored voltages.
  */

  responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ADCM_03, response )

  if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
    RetValue = 0
      Passed = 0

    if err == nil {
      err = errors.New("Bad Monitored Voltages.")

      log.Printf("%q", err)
    }
  }

  if err == nil {
    /*
        Check the 12 Volt entry for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage := (int) (response[3])

    voltage = (voltage << 8) + (int) (response[4])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 1 12 Volt Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 12600
    Test.MinValue = 11400
    Test.Pass = true

    if voltage <= 11400 || voltage >= 12600 {
      fmt.Printf(" Test 1 12 Volts Failed (Got %d Expected > 11400 and < 12600)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Check the 4 Volt entry for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage = (int) (response[5])

    voltage = (voltage << 8) + int(response[6])

    Test = RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 1 4 Volt Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 3800
    Test.MinValue = 4200
    Test.Pass = true

    if voltage <= 3800 || voltage >= 4200 {
      fmt.Printf(" Test 1 4 Volts Failed (Got %d Expected > 3800 and < 4200)\r\n", voltage)

      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Set the LEDs on the ADCM to a low level and wait two seconds.
    */

    _,err1 := SetADCM_LEDStateCommand( LED_AT_3 | LED_AT_6 | LED_AT_9 | LED_AT_12, 20 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(2)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 1 Monitored Voltages Passed.\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the user if the LEDs are all on and then set the pass/fail flag.
        Write the test result to the database.
    */

    fmt.Printf("Are all of the LEDs on the ADCM on (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)
    
    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 2 LEDs On Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (char & 0xdf) == 'N' {
      Test.Pass = false
      RetValue = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Set the ADCM LEDs to a brighter setting.
    */

    _,err1 = SetADCM_LEDStateCommand( LED_AT_3 | LED_AT_6 | LED_AT_9 | LED_AT_12, 80 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(2)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 
  }

  Passed = 1

  if err == nil {
    /*
        Ask the user if the LEDs are now brighter and then set the pass/fail flag.
        Write the test result to the database.
    */

    err1 := (error) (nil)
    
    err1 = SerialPort.Flush()

    fmt.Printf("Are all of the LEDs on the ADCM on and brighter (y or n) ? ")

    char := (byte) (0)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 2 LEDs Brighter Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (char & 0xdf) == 'N' {
      Test.Pass = false
      RetValue = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    char, err1 = ConsoleInput.ReadByte()

    err1 = SerialPort.Flush()

    /*
        Turn off all of the LEDs and wait two seconds.
    */

    _,err = SetADCM_LEDStateCommand( 0, 50 )

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(2)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 
  }

  if err == nil {
    /*
        Ask the user if the LEDs are all off and then set the pass/fail flag.
        Write the test result to the database.
    */

    fmt.Printf("Are all of the LEDs on the ADCM off (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)
    
    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 2 LEDs Off Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (char & 0xdf) == 'N' {
      Test.Pass = false
      RetValue = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Turn on the ADCM sonalert at a low level and wait 5 seconds.
    */

    _, err1 = SetADCMSonalertStateCommand( 1, 25 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 
  }

  if err == nil {
    /*
        Ask the IEM for ADCM monitored voltages.
    */

    responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ADCM_03, response )

    if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Monitored Voltages.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check the sonalert voltage for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage := (int) (response[7])

    voltage = (voltage << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 3 Sonalert Setting 25 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 6300
    Test.MinValue = 5700
    Test.Pass = true

    if voltage <= 5700 || voltage >= 6300 {
      fmt.Printf(" Test 3 Sonalert Voltage Failed (Got %d Expected > 5700 and < 6300)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Ask the user if he can hear the sonalert and the set the pass/fail flag.
        Write the test result to the database.
    */

    fmt.Printf("Is the sonalert buzzer sounding? (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test1 := PassFailTestResult{}

    Test1.AssemblyPartNumber = AssemblyPartNumber
    Test1.AssemblySerialNumber = AssemblySerialNumber
    Test1.PartNumber = ADCMPartNumber
    Test1.SerialNumber = ADCMSerialNumber
    Test1.TestName = "ADCM Test 3 Sonaler Setting 25 Sounding Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test1.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test1.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test1.Pass = true

    if (char & 0xdf) == 'N' {
      Test1.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test1.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test1 )

    /*
        Set the ADCM sonalert to a higher level and wait five seconds.
    */

    _, err1 = SetADCMSonalertStateCommand( 1, 50 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 3 Sonalert Voltage Passed first setting.\r\n")
    }
  }

  if err == nil {
    /*
        Ask the IEM for ADCM monitored voltages.
    */

    responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ADCM_03, response )

    if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Monitored Voltages.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check the sonalert voltage for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage := (int) (response[7])

    voltage = (voltage << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 3 Sonaler Setting 50 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 8400
    Test.MinValue = 7600
    Test.Pass = true

    if voltage <= 7600 || voltage >= 8400 {
      fmt.Printf(" Test 3 Sonalert Voltage Failed (Got %d Expected > 7600 and < 8400)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Ask the user if he can hear the sonalert and then set the pass/fail flag.
        Write the test result to the database.
    */

    fmt.Printf("Is the sonalert buzzer sounding? (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test1 := RangeTestResult{}

    Test1.AssemblyPartNumber = AssemblyPartNumber
    Test1.AssemblySerialNumber = AssemblySerialNumber
    Test1.PartNumber = ADCMPartNumber
    Test1.SerialNumber = ADCMSerialNumber
    Test1.TestName = "ADCM Test 3 Sonaler Setting 50 Sounding Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test1.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test1.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test1.Pass = true

    if (char & 0xdf) == 'N' {
      Test1.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test1.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test1 )

    /*
        Set the ADCM sonalert to a yet higher level and wait five seconds.
    */

    _, err1 = SetADCMSonalertStateCommand( 1, 75 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 3 Sonalert Voltage Passed second setting.\r\n")
    }
  }

  Passed = 1

  if err == nil {
    /*
        Ask the IEM for ADCM monitored voltages.
    */

    responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ADCM_03, response )

    if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Monitored Voltages.")
      }
    }
  }

  if err == nil {
    /*
        Check the sonalert voltage for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage := (int) (response[7])

    voltage = (voltage << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 3 Sonaler Setting 75 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 10500
    Test.MinValue = 9500
    Test.Pass = true

    if voltage <= 9500 || voltage >= 10500 {
      fmt.Printf(" Test 3 Sonalert Voltage Failed (Got %d Expected > 9500 and < 10500)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Ask the user if he can hear the sonalert and then set the pass/flag.
        Write the test result to the database.
    */

    fmt.Printf("Is the sonalert buzzer sounding? (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test1 := PassFailTestResult{}

    Test1.AssemblyPartNumber = AssemblyPartNumber
    Test1.AssemblySerialNumber = AssemblySerialNumber
    Test1.PartNumber = ADCMPartNumber
    Test1.SerialNumber = ADCMSerialNumber
    Test1.TestName = "ADCM Test 3 Sonaler Setting 75 Sounding Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test1.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test1.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test1.Pass = true

    if (char & 0xdf) == 'N' {
      Test1.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test1.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test1 )

    /*
        Set the ADCM sonalert to its top level and wait five seconds.
    */

    _, err1 = SetADCMSonalertStateCommand( 1, 100 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 3 Sonalert Voltage Passed third setting.\r\n")
    }
  }

  if err == nil {
    /*
        Ask the IEM for the ADCM monitored voltages.
    */

    responseCount, err = InformationSelectionCommand( MON_VOLTAGES, ADCM_03, response )

    if err != nil || responseCount != MON_VOLTAGES_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Monitored Voltages.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check tha sonalert voltage for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    voltage := (int) (response[7])

    voltage = (voltage << 8) + (int) (response[8])

    Test := RangeTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 3 Sonaler Setting 100 Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = voltage
    Test.MaxValue = 12600
    Test.MinValue = 11400
    Test.Pass = true

    if voltage <= 11400 || voltage >= 12600 {
      fmt.Printf(" Test 3 Sonalert Voltage Failed (Got %d Expected > 11400 and 12600)\r\n", voltage)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Ask the user if he can hear the sonalert and then set the pass/fail flag.
        Write the test result to the database.
    */

    fmt.Printf("Is the sonalert buzzer sounding? (y or n) ? ")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    char, err1 = ConsoleInput.ReadByte()

    Test1 := PassFailTestResult{}

    Test1.AssemblyPartNumber = AssemblyPartNumber
    Test1.AssemblySerialNumber = AssemblySerialNumber
    Test1.PartNumber = ADCMPartNumber
    Test1.SerialNumber = ADCMSerialNumber
    Test1.TestName = "ADCM Test 3 Sonaler Setting 100 Sounding Test"

    timeDate = time.Now()
    hour, min, sec = timeDate.Clock()
    year, month, day = timeDate.Date()

    Test1.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test1.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test1.Pass = true

    if (char & 0xdf) == 'N' {
      Test1.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test1.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test1 )

    /*
        Turn off the ADCM sonalert and wait five seconds.
    */

    _, err1 = SetADCMSonalertStateCommand( 0, 25 )

    if err == nil {
      err = err1
    }

    start := time.Now()

    t := time.Now()

    elapsed := t.Sub(start)

    for elapsed < time.Duration(5)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    } 

    if Passed == 1 {
      fmt.Printf(" Test 3 Sonalert Voltage Passed fourth setting.\r\n")
    }
  }

  if err == nil {
    /*
        Ask the IEM for the ADCM status vector.
    */

    responseCount, err = InformationSelectionCommand( STATUS_VECTOR, ADCM_12, response )

    if err != nil || responseCount != STATUS_VECTOR_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Status Vector.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Check the post flash test status and the set the pass/flag.
        Write the test result to the database.
    */

    Test := PassFailTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 4 Flash Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Pass = true

    if (response[3] & FLASH_TEST_PASSED_03) == FLASH_TEST_PASSED_03 {
      fmt.Printf("ADCM Flash Test Passed.\r\n")
    } else {
      Test.Pass = false
      RetValue = 0

      fmt.Printf("ADCM Flash Test Failed.\r\n")
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Ask the IEM for the hardware version of the ADCM.
    */

    responseCount, err1 := InformationSelectionCommand( HW_VERSION, ADCM_02, response )

    if err == nil {
      err = err1
    }

    if err != nil || responseCount != HW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Hardware Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the ADCM hardware version to the database.
    */

    version := (int) (response[3])

    Test := HardwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 5 Hardware Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.HardwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    fmt.Printf("ADCM Hardware Version %d", version)

    /*
        Ask the IEM for the ADCM software version.
    */

    responseCount, err = InformationSelectionCommand( SW_VERSION, ADCM_01, response )

    if err != nil || responseCount != SW_VERSION_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Software Version.")

        log.Printf("%q", err)
      }
    }
  }

  if err == nil {
    /*
        Write the ADCM software version to the database.
    */

    Test := SoftwareVersionTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 6 Software Version Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    index := s.Index((string) (response[3:responseCount - 3]), (string) (0))
    version := (string) (response[3:3 + index])
    Test.SoftwareVersion = version
    Test.Pass = true

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    /*
        Tell the user to make sure that the ADCMs ambient light sensor is unobstructed.
        Then ask the IEM for the ADCMs ambient light intensity reading.
    */

    fmt.Printf("ADCM Software Version %s\r\n", response[3:responseCount - 3])

    fmt.Printf("\r\n\nPosition ADCM so that it has an unobstructed view of the ambient light in room.\r\n")

    fmt.Printf("Hit any key when ready.\r\n")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    responseCount, err = InformationSelectionCommand( AMBIENT_LIGHT_INT, 0, response )

    if err != nil || responseCount != AMBIENT_LIGHT_INT_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Ambient Light Intensity.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check the ambient light intensity for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    intensity = (int) (response[3])

    intensity = (intensity << 8) + (int) (response[4])

    Test := LowerLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 7 Ambient Light High Level Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = intensity
    Test.LowerLimit = 300
    Test.Pass = true

    if intensity <= 300 {
      fmt.Printf(" Test 7 Ambient Light Sensor Failed (Got %d Expected > 300\r\n", intensity)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if Passed == 1 {
      fmt.Printf(" Test 7 Ambient Light Sensor Passed high test with value %d.\r\n", intensity)
    }
  }

  if err == nil {
    /*
        Tell the user to cover the ADCM ambient light sensor and then ask the IEM
        for the ADCM light intensity.
    */

    fmt.Printf("\r\n\nCover the round display window on the ADCM.\r\n")

    fmt.Printf("Hit any key when ready.\r\n")

    char := (byte) (0)

    err1 := (error) (nil)

    char, err1 = ConsoleInput.ReadByte()

    for err1 != nil && char == 0 {
      char, err1 = ConsoleInput.ReadByte()
    }

    responseCount, err = InformationSelectionCommand( AMBIENT_LIGHT_INT, 0, response )

    if err != nil || responseCount != AMBIENT_LIGHT_INT_RESPONSE_LEN {
      RetValue = 0

      if err == nil {
        err = errors.New("Bad Ambient Light Intensity.")

        log.Printf("%q", err)
      }
    }
  }

  Passed = 1

  if err == nil {
    /*
        Check the ambient light intensity for the proper range and then set the pass/fail flag.
        Write the test result to the database.
    */

    previousIntensity := intensity/2

    intensity = (int) (response[3])

    intensity = (intensity << 8) + (int) (response[4])

    Test := UpperLimitTestResult{}

    Test.AssemblyPartNumber = AssemblyPartNumber
    Test.AssemblySerialNumber = AssemblySerialNumber
    Test.PartNumber = ADCMPartNumber
    Test.SerialNumber = ADCMSerialNumber
    Test.TestName = "ADCM Test 7 Ambient Light Low Level Test"

    timeDate := time.Now()
    hour, min, sec := timeDate.Clock()
    year, month, day := timeDate.Date()

    Test.Time = fmt.Sprintf("%2.2d:%2.2d:%2.2d", hour, min, sec)
    Test.Date = fmt.Sprintf("%2.2d/%2.2d/%4d", month, day, year)
    Test.Value = intensity
    Test.UpperLimit = previousIntensity
    Test.Pass = true

    if intensity >= previousIntensity {
      fmt.Printf(" Test 7 Ambient Light Sensor Failed (Got %d Expected < %d\r\n", intensity, previousIntensity)

      Test.Pass = false
      RetValue = 0
      Passed = 0
    }

    Test.SetID(couchdb.GenerateUUID())

    err = couchdb.Store( TestDB, &Test )

    if Passed == 1 {
      fmt.Printf(" Test 7 Ambient Light Sensor Passed low test with value %d.\r\n", intensity)
    }
  }

  /*
      Put the IEM tester back to its initial state.
  */

  _, err1 := Init( mcp )

  if err == nil {
    err = err1
  }

  return RetValue, err
}

/*
    Procedure Name : termEcho

    Desciption     : This routine turns echo on or off for the console input

    Arguments      : true for echo on and false for echo off

    Return Value   : This routine has no return value.
*/

func termEcho(on bool) {
  // Common settings and variables for both stty calls.

  attrs := syscall.ProcAttr{ Dir:   "",
                             Env:   []string{},
                             Files: []uintptr{os.Stdin.Fd(), os.Stdout.Fd(), os.Stderr.Fd()},
                             Sys:   nil}

  var ws syscall.WaitStatus
  cmd := "echo"

  if on == false {
    cmd = "-echo"
  }

  // Enable/disable echoing.

  pid, err := syscall.ForkExec( "/bin/stty",
                                []string{"stty", cmd},
                                &attrs)

  if err != nil {
    panic(err)
  }

  // Wait for the stty process to complete.

  _, err = syscall.Wait4(pid, &ws, 0, nil)

  if err != nil {
    panic(err)
  }
}
 
/*
    Procedure Name : termCanon

    Description    : This routine turns canonical mode on or off for the console input.

    Arguments      : true for on and false for off.

    Return Value   : This routine has no return value.
*/

func termCanon(on bool) {
  // Common settings and variables for both stty calls.

  attrs := syscall.ProcAttr{ Dir:   "",
                             Env:   []string{},
                             Files: []uintptr{os.Stdin.Fd(), os.Stdout.Fd(), os.Stderr.Fd()},
                             Sys:   nil}

  var ws syscall.WaitStatus
  cmd := "icanon"

  if on == false {
    cmd = "-icanon"
  }

  // Enable/disable echoing.

  pid, err := syscall.ForkExec( "/bin/stty",
                                []string{"stty", cmd},
                                &attrs)

  if err != nil {
    panic(err)
  }

  // Wait for the stty process to complete.

  _, err = syscall.Wait4(pid, &ws, 0, nil)

  if err != nil {
    panic(err)
  }
}

/*
    Procedure Name : GetSerialNumber

    Description    : This routine inputs a serial number or part number in non-canonical mode with
                     no echo. Thus it is responsigle for collecting the number, echoing characters,
                     and supporting backspace.

    Arguments      : number - A sloce of bytes where the incoming number is stored.

    Return Value   : Slice containing the character string entered for the number.
                     Any error that occurred during the number entry.
*/

func GetSerialNumber( number []byte ) ([]byte, error) {
  err := error(nil)

  /*
      Flush the console input.
  */

  ConsoleInput.Reset(os.Stdin)

  /*
      Scan until we find the first non newline character and save it.
  */

  number = append(number, '\n')

  char1 := (byte) (0)

  for (err == nil) && (number[0] == '\n') {
    char1, err = ConsoleInput.ReadByte()

    number[0] = char1
  }

  fmt.Printf("%c", number[0])

  i := 1

  number = append(number, 0)

  /*
      Now we collect the entered number string supporting back space as
      we go.
  */

  for err == nil {
    char1, err = ConsoleInput.ReadByte()

    if number[i] != '\n' {
      if char1 == 0x7f {
        if i > 0 {
          i = i - 1
        }
      } else {
        number[i] = char1

        i += 1

        number = append(number, 0)
      }

      if char1 == 0x7f {
        char1 = 0x08
      }

      if char1 != '\n' {
        fmt.Printf("%c", char1)
      }

      if char1 == 0x08 {
        fmt.Printf(" \b")
      }
    }

    if i > 0 {
      if number[i - 1] == '\n' {
        break;
      }
    }
  }

  /*
      Now we size our slice to just the collected character string.
      Then we again flush the console input.
  */

  number = number[:i - 1]

  ConsoleInput.Reset(os.Stdin)

  return number, err
}

/*
    Procedure Name : ValidatePartNumber

    Description    : Take an incoming byte string and verify that it looks
                     like a valid part number.

    Arguments      : partNumber - Bytes string to validate

    Return Value   : true if it's a valid part number and otherwise false
*/

func ValidatePartNumber( partNumber []byte ) bool {
  RetValue := true

  /*
      Currently a valid part number consists of six decimal digits
      followed by a dask followed by three decimal digits.
  */

  length := 0

  for i := 0;i < len(partNumber);i++ {
    if partNumber[i] == 0 {
      break
    } else {
      length += 1
    }
  }

  if length == 10 {
    for i := 0;i < 10;i++ {
      if i < 6 {
        if partNumber[i] < '0' || partNumber[i] > '9' {
          RetValue = false

          break
        }
      } else {
        if i == 6 && partNumber[i] != '-' {
          RetValue = false

          break
        }

        if i > 6 && (partNumber[i] < '0' || partNumber[i] > '9') {
          RetValue = false

          break
        }
      }
    }
  } else {
    RetValue = false
  }

  return RetValue
}

/*
    Procedure Name : ValidateSerialNumber

    Description    : This routine takes a byte string and determines if it
                     looks like a valid serial number.

    Arguments      : serialNumber - Byte string to validate

    Return Value   : true if this looks like a valid serial number otherwise false
*/

func ValidateSerialNumber( serialNumber []byte) bool {
  RetValue := true
  length := 0

  /*
      Currently a valid serial number has four decimal digits followed by the letters QE
      followed by five decimal digits.
  */

  for i := 0;i < len(serialNumber);i++ {
    if serialNumber[i] == 0 {
      break
    } else {
      length += 1
    }
  }

  if length == 11 {
    for i := 0;i < 11;i++ {
      if i < 4 {
        if serialNumber[i] < '0' || serialNumber[i] > '9' {
          RetValue = false

          break
        }
      }

      if i == 4 && serialNumber[i] != 'Q' {
        RetValue = false

        break
      }

      if i == 5 && serialNumber[i] != 'E' {
        RetValue = false

        break;
      }

      if i > 5 {
        if serialNumber[i] < '0' || serialNumber[i] > '9' {
          RetValue = false
    
          break
        }
      }
    }
  } else {
    RetValue = false
  }

  return RetValue
}

/*
    Procedure Name : GetNumberPair

    Description    : This routine inputs a valid part number and a valid serial number.

    Arguments      : identifier - String that tells the user what pair of numbers that we're looking for.
                     majorPartNumbers - Slice containing valid numbers for the upper part of the part 
                                        number
                     minorPartNumber  - Valid lower part of the part number

    Return Value   : Part number string
                     Serial number string
                     Upper part of the part number
                     Lower part of the part number
                     Any error that occurred during pair enty
*/

func GetNumberPair( identifier string, majorPartNumbers []int, minorPartNumber int ) (string, string, int, int, error) {
  var number []byte
  var number1 []byte
  var firstPart int
  var secondPart int

  /*
      Ask the user for the part number and then collect the entry.
  */

  fmt.Printf("\r\nEnter %s Part Number : ", identifier)

  number, err := GetSerialNumber( number )

  /*
      Ask the user for the serial number and then collect the entry.
  */

  fmt.Printf("\r\nEnter %s Serial Number : ", identifier)

  number1, err = GetSerialNumber( number1 )
  
  /*
      Validate the part number string and the serial number string.
  */

  flag := ValidatePartNumber( number )

  flag1 := ValidateSerialNumber( number1 )

  if flag {
    /*
       If the part number string is valid, then extract the upper and lower parts
       of the part number as numbers. Finally, validate the extracted numbers 
       against what is acceptable for this entry.
    */

    fmt.Sscanf( (string) (number[:6]), "%d", &firstPart )

    fmt.Sscanf( (string) (number[7:]), "%d", &secondPart )

    flag = false

    for i := 0;i < len(majorPartNumbers);i++ {
      if majorPartNumbers[i] == firstPart {
        if minorPartNumber == 0 {
          flag = true
        } else {
          if minorPartNumber == secondPart {
            flag = true
          }
        }
      } 
    }
  }

  for !flag || !flag1 {
    
    /*
        If either the part number of the serial number is not valid then we
        tell the user and ask him to reenter the pair.
    */

    if !flag {
      fmt.Printf("\r\n\nInvalid %s Part Number\r\n", identifier)
    }

    if !flag1 {
      if !flag {
        fmt.Printf("\r\nInvalid %s Serial Number\r\n", identifier)
      } else {
        fmt.Printf("\r\n\nInvalid %s Serial Number\r\n", identifier)
      }
    }

    number = number[:0]

    number1 = number1[:0]

    fmt.Printf("\r\nEnter %s Part Number : ", identifier)

    number, err = GetSerialNumber( number )

    fmt.Printf("\r\nEnter %s Serial Number : ", identifier)

    number1, err = GetSerialNumber( number1 )

    flag = ValidatePartNumber( number )

    flag1 = ValidateSerialNumber( number1 )

    fmt.Sscanf( (string) (number[:6]), "%d", &firstPart )

    fmt.Sscanf( (string) (number[7:]), "%d", &secondPart )

    flag = false

    for i := 0;i < len(majorPartNumbers);i++ {
      if majorPartNumbers[i] == firstPart {
        if minorPartNumber == 0 {
          flag = true
        } else {
          if minorPartNumber == secondPart {
            flag = true
          }
        }
      } 
    }
  }

  return string(number), string(number1), firstPart, secondPart, err
}

/*
    Procedure Name : GetAssemblyNumber

    Description    : This routine asks for the top level assembly part number and serial number.

    Arguments      : This routine has no arguments.

    Return Value   : Any error that occurred during number entry.
*/

func GetAssemblyNumbers() error {
  var err error

  /*
      For top level assembly numbers we only allow three numbers for the upper part of the part number :
        251470 - IEM with alerter
        251469 - IEM without alerter
        250470 - ADCM only

      for top level assembly numbers we allow any number for the lower part of the part number. This is
      indicated as a zero which is the wild card.
      
  */

  assemblyChoices := []int {251470, 251469, 250470}

  AssemblyPartNumber, AssemblySerialNumber, AssemblyMajorPartNumber, AssemblyMinorPartNumber, err =  GetNumberPair( "Assembly", assemblyChoices, 0 )
  
  return err
}

/*
    Procedure Name : GetNonAlerterIEMNumbers

    Description    : This routine collects all of the part number/serial number pairs for an alerter assembly

    Arguments      : This routine has no arguments.

    Return Value   : Any error returned during the collection of the numbers.
*/

func GetAlerterIEMNumbers() error {
  var err error

  moduleNumber := []int {227411}

  MainCircuitPartNumber, MainCircuitSerialNumber, MainCircuitMajorPartNumber, MainCircuitMinorPartNumber, err = GetNumberPair( "IEM Main Circuit", moduleNumber, 100)
  DualPowerSupplyPartNumber, DualPowerSupplySerialNumber, DualPowerSupplyMajorPartNumber, DualPowerSupplyMinorPartNumber, err = GetNumberPair("IEM Dual Power Supply", moduleNumber, 200)
  CabConnectorCardPartNumber, CabConnectorSerialNumber, CabConnectorMajorPartNumber, CabConnectorMinorPartNumber, err = GetNumberPair("IEM Cab Connector Card", moduleNumber, 300)
  IOConnectorPartNumber, IOConnectorSerialNumber, IOConnectorMajorPartNumber, IOConnectorMinorPartNumber, err = GetNumberPair("IEM IO Connector Card", moduleNumber, 400)
  IEM4_20mAPartNumber, IEM4_20mASerialNumber, IEM4_20mAMajorPartNumber, IEM4_20mAMinorPartNumber, err = GetNumberPair("IEM 4-20mA", moduleNumber, 500)
  ABCMPartNumber, ABCMSerialNumber, ABCMMajorPartNumber, ABCMMinorPartNumber, err = GetNumberPair("IEM Alerter Brake Control Module", moduleNumber, 600)

  moduleNumber[0] = 250470

  ADCMPartNumber, ADCMSerialNumber, ADCMMajorPartNumber, ADCMMinorPartNumber, err = GetNumberPair("IEM Alerter Display Control Module", moduleNumber, 0)

  start := time.Now()

  t := time.Now()

  elapsed := t.Sub(start)

  for elapsed < time.Duration(200)*time.Millisecond {
    t = time.Now()

    elapsed = t.Sub(start)
  } 

  ConsoleInput.Reset(os.Stdin)

  return err
}

/*
    Procedure Name : GetNonAlerterIEMNumbers

    Description    : This routine collects all of the part number/serial number pairs associated with an IEM without alerter assembly.

    Arguments      : This routine has no arguments.

    Return Value   : Any error that occurs during the collection.
*/

func GetNonAlerterIEMNumbers() error {
  var err error

  moduleNumber := []int {227411}

  MainCircuitPartNumber, MainCircuitSerialNumber, MainCircuitMajorPartNumber, MainCircuitMinorPartNumber, err = GetNumberPair( "IEM Main Circuit", moduleNumber, 100)
  DualPowerSupplyPartNumber, DualPowerSupplySerialNumber, DualPowerSupplyMajorPartNumber, DualPowerSupplyMinorPartNumber, err = GetNumberPair("IEM Dual Power Supply", moduleNumber, 200)
  CabConnectorCardPartNumber, CabConnectorSerialNumber, CabConnectorMajorPartNumber, CabConnectorMinorPartNumber, err = GetNumberPair("IEM Cab Connector Card", moduleNumber, 300)
  IOConnectorPartNumber, IOConnectorSerialNumber, IOConnectorMajorPartNumber, IOConnectorMinorPartNumber, err = GetNumberPair("IEM IO Connector Card", moduleNumber, 400)
  IEM4_20mAPartNumber, IEM4_20mASerialNumber, IEM4_20mAMajorPartNumber, IEM4_20mAMinorPartNumber, err = GetNumberPair("IEM 4-20mA", moduleNumber, 500)

  start := time.Now()

  t := time.Now()

  elapsed := t.Sub(start)

  for elapsed < time.Duration(200)*time.Millisecond {
    t = time.Now()

    elapsed = t.Sub(start)
  } 

  ConsoleInput.Reset(os.Stdin)

  return err
}

/*
    Procedure Name : main

    Description    : This is the main routine.

    Arguments      : This routine has no arguments
 
    Return Value   : This routine has no return value
*/

func main() {
  var err2 error
  var err1 error

  /*
     Set the logging flags so that logs include file and line information.
  */

  log.SetFlags(log.LstdFlags | log.Lshortfile)

  /*
      Open up stdin as buffered i/o.
  */

  ConsoleInput = bufio.NewReader(os.Stdin)

  /*
      Open up the serial port that goes to the IEM.
  */

  c := &serial.Config{Name:"/dev/ttyS0", Baud:9600, ReadTimeout: time.Second*5 }

  SerialPort, err2 = serial.OpenPort(c)
  
  if err2 != nil {
    log.Print("%q", err2)
  }

  /*
      Open up a connection to couchdb.
  */

  TestDB,err1 = couchdb.NewDatabase("http://127.0.0.1:5984/testdb")

  if ( err1 != nil ) {
    fmt.Println("error opening test database: %s\n", err1)
  }

  /*
      Check that the database is responsive.
  */

  err1 = TestDB.Available()

  if ( err1 != nil ) {
    fmt.Println("error opening test database not available: %s\n", err1)
  }

  /*
      Open and initialize the control structures for the port extenders.
  */

  mcp23s17_0 := MCP23S17.NewMCP23S17( 0, spi.DEFAULT_BUS, spi.DEFAULT_CHIP ) 
  mcp23s17_1 := MCP23S17.NewMCP23S17( 1, spi.DEFAULT_BUS, spi.DEFAULT_CHIP ) 
  mcp23s17_2 := MCP23S17.NewMCP23S17( 2, spi.DEFAULT_BUS, spi.DEFAULT_CHIP ) 
  mcp23s17_3 := MCP23S17.NewMCP23S17( 3, spi.DEFAULT_BUS, spi.DEFAULT_CHIP ) 
  mcp23s17_4 := MCP23S17.NewMCP23S17( 4, spi.DEFAULT_BUS, spi.DEFAULT_CHIP ) 

  mcp23s17 := []*MCP23S17.MCP23S17 {mcp23s17_0, mcp23s17_1, mcp23s17_2, mcp23s17_3, mcp23s17_4}

  err := mcp23s17[0].Open()

  if ( err != nil ) {
    fmt.Println("error connecting to chip 0: %s\n", err)
  }

  err = mcp23s17[1].Open()

  if ( err != nil ) {
    fmt.Println("error connecting to chip 1: %s\n", err)
  }

  err = mcp23s17[2].Open()

  if ( err != nil ) {
    fmt.Println("error connecting to chip 2: %s\n", err)
  }

  err = mcp23s17[3].Open()

  if ( err != nil ) {
    fmt.Println("error connecting to chip 3: %s\n", err)
  }

  err = mcp23s17[4].Open()

  if ( err != nil ) {
    fmt.Println("error connecting to chip 4: %s\n", err)
  }

  /*
      Initialize the port extenders.
  */

  mcp23s17[0].Write( 0x7e, MCP23S17.IOCON )
  mcp23s17[0].Write( 0x7e, MCP23S17.IOCON + 1 )
  mcp23s17[0].Write( 0xfc, MCP23S17.OLATA )
  mcp23s17[0].Write( 0xcf, MCP23S17.OLATB )

  Shadows[0] = 0xcffc

  mcp23s17[0].Write( 0x00, MCP23S17.IODIRA )
  mcp23s17[0].Write( 0x00, MCP23S17.IODIRB )

  mcp23s17[1].Write( 0x7e, MCP23S17.IOCON )
  mcp23s17[1].Write( 0x7e, MCP23S17.IOCON + 1 )
  mcp23s17[1].Write( 0xff, MCP23S17.OLATA )
  mcp23s17[1].Write( 0xff, MCP23S17.OLATB )

  Shadows[1] = 0xffff

  mcp23s17[1].Write( 0x00, MCP23S17.IODIRA )
  mcp23s17[1].Write( 0x00, MCP23S17.IODIRB )

  mcp23s17[2].Write( 0x7e, MCP23S17.IOCON )
  mcp23s17[2].Write( 0x7e, MCP23S17.IOCON + 1 )
  mcp23s17[2].Write( 0xff, MCP23S17.OLATA )
  mcp23s17[2].Write( 0xff, MCP23S17.OLATB )

  Shadows[2] = 0xffff

  mcp23s17[2].Write( 0x00, MCP23S17.IODIRA )
  mcp23s17[2].Write( 0x00, MCP23S17.IODIRB )

  mcp23s17[3].Write( 0x7e, MCP23S17.IOCON )
  mcp23s17[3].Write( 0x7e, MCP23S17.IOCON + 1 )
  mcp23s17[3].Write( 0x04, MCP23S17.OLATA )
  mcp23s17[3].Write( 0xc0, MCP23S17.OLATB )

  Shadows[3] = 0xc004

  mcp23s17[3].Write( 0x00, MCP23S17.IODIRA )
  mcp23s17[3].Write( 0x00, MCP23S17.IODIRB )

  mcp23s17[4].Write( 0x7e, MCP23S17.IOCON )
  mcp23s17[4].Write( 0x7e, MCP23S17.IOCON + 1 )
  mcp23s17[4].Write( 0x00, MCP23S17.OLATA )
  mcp23s17[4].Write( 0x00, MCP23S17.OLATB )

  Shadows[4] = 0x0000

  mcp23s17[4].Write( 0xff, MCP23S17.IODIRA )
  mcp23s17[4].Write( 0x00, MCP23S17.IODIRB )

  /*
      Bring up powr to the IEM.
  */

  Shadows[3] |= 2

  mcp23s17[3].Write( 0x06, MCP23S17.OLATA )

  n := (int) (0)
  err3 := (error) (nil)

  /*
      Initialize the input buffer for initial data coming from the IEM.
      Wait some time for the IEM to come up and stop sending us power on
      self test text.
  */

  buf1 := make([]byte, 100)

  for i := 0;i < len(buf1);i++ {
    buf1[i] = '+'
  }

  start := time.Now()

  t := time.Now()

  elapsed := t.Sub(start)

  for elapsed < time.Duration(1)*time.Second {
    t = time.Now()

    elapsed = t.Sub(start)
  } 

  for err3 == nil {
    n, err3 = SerialPort.Read(buf1)
  }

  /*
      Send the IEM serial port two carriage return/line feed pairs in order
      to get the IEM ready to talk to us. Then wait a little and flush the
      serial port.
  */

  output := []byte {0x0d,0x0a,0x0d,0x0a}

  _, err3 = SerialPort.Write( output )

  start = time.Now()

  t = time.Now()

  elapsed = t.Sub(start)

  for elapsed < time.Duration(250)*time.Millisecond {
    t = time.Now()

    elapsed = t.Sub(start)
  } 

  err3 = SerialPort.Flush()

  _, err3 = Init( mcp23s17 )

  /*
      Turn off echo and canonical mode on the console input.
  */

  termCanon( false)

  termEcho( false )

  /*
      Ask for the top level assembly numbers.
  */

  err3 = GetAssemblyNumbers()

  alerter := 0

  /*
      Determing which top level assembly that we have and record it for later.
  */

  if AssemblyMajorPartNumber == 251470 {
    /*
        This is the IEM with alerter.
    */

    GetAlerterIEMNumbers()

    alerter = 1
  } else {
    if AssemblyMajorPartNumber == 250470 {
      /*
          This is the ADCM only.
      */

      alerter = 2

      ADCMMajorPartNumber = 227411
      ADCMMinorPartNumber = 700
      ADCMPartNumber = "227411-700"
      ADCMSerialNumber = AssemblySerialNumber
    } else {
      /*
          This is the IEM without alerter
      */

      GetNonAlerterIEMNumbers()
    }
  }

  /*
      Turn echo and canonical mode back on for console input.
  */

  termEcho( true )

  termCanon( true )

  /*
      Print the current time and date.
  */

  now := time.Now()

  hour, min, sec := now.Clock()
  year, month, day := now.Date()
  
  fmt.Printf("\r\n\n%2.2d:%2.2d:%2.2d\r\n", hour, min, sec)
  fmt.Printf("%2.2d/%2.2d/%4d\r\n", month, day, year)
  
  if alerter > 0 {
    /*
       Now we wait some extra so that the IEM has collected the proper
       informtaion from the ADCM and ABCM.
    */

    fmt.Printf("\r\n\nInitializing Tester. Please wait.\r\n")

    start = time.Now()

    t = time.Now()

    elapsed = t.Sub(start)

    for elapsed < time.Duration(15)*time.Second {
      t = time.Now()

      elapsed = t.Sub(start)
    }     
  }

  /*
      Now we print the users menu.
  */

  char := (byte) (0)

  char1 := (byte) (0)

  for char != 'q' {
    ConsoleInput.Reset(os.Stdin)

    if alerter == 1 {
      fmt.Printf("\r\n\n1) 4-20 mA Test\r\n")

      fmt.Printf("2) CPU Main Test\r\n")

      fmt.Printf("3) ABCM Test\r\n")

      fmt.Printf("4) ADCM Test\r\n")

      fmt.Printf("q) Quit\r\n\n\n")
    } else {
      if alerter == 2 {
        fmt.Printf("\r\n\n1) ADCM Test\r\n")

        fmt.Printf("q) Quit\r\n\n\n")
      } else {
        fmt.Printf("\r\n\n1) 4-20 mA Test\r\n")

        fmt.Printf("2) CPU Main Test\r\n")

        fmt.Printf("q) Quit\r\n\n\n")
      }
    }

    /*
        THen we wait for him to enter his test request.
    */

    fmt.Printf("Enter test number and hit return: ")

    char = (byte) (0)

    char1 = (byte) (0)

    err1 = (error) (nil)

    n = -1

    char, err1 = ConsoleInput.ReadByte()

    for err1 == nil && ((char == 0) || (char == '\n')) {
      char, err1 = ConsoleInput.ReadByte()
    }

    char1, err1 = ConsoleInput.ReadByte()

    for err1 == nil && char1 != '\n' {
      char1, err1 = ConsoleInput.ReadByte()
    }

    fmt.Printf("\r\n")

    /*
       Now we execute the test request.
    */

    switch char {
      case '1' :
        if alerter < 2 {
          n, err3 = Test_4_20MA( mcp23s17 )
        } else {
          n, err3 = Test_ADCM( mcp23s17 )
        }

      case '2' :
        if alerter < 2 {
          n, err3 = Test_CPUMain( mcp23s17, alerter )
        }
      case '3' :
        if alerter == 1 {
          n, err3 = Test_ABCM( mcp23s17 )
        }
      case '4' :
        if alerter == 1 {
          n, err3 = Test_ADCM( mcp23s17 )
        }
      case 'q' :
        ConsoleInput.Reset(os.Stdin)
      default :
        ConsoleInput.Reset(os.Stdin)
        continue
    }

    /*
        Then we display the pass/fail message for the requested test.
    */

    if n >= 0 {
      if char != 'q' {
        result := []byte{'P','a','s','s','e','d'}
        result1 := []byte{'F','a','i','l','e','d'}

        if n == 0 {
          result = result1
        }

        if err3 != nil {
          log.Printf("%q %s", err3, result)
        } else {
          log.Printf("%q", result)
        }
      }
    }
  }

  /*
      The very last thing that we do is turn off power to the IEM.
  */

  mcp23s17[3].Write( 0x04, MCP23S17.OLATA )
}
