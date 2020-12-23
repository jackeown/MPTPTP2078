%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t25_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:46 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       : 3807 (28646 expanded)
%              Number of leaves         :  729 (11282 expanded)
%              Depth                    :   16
%              Number of atoms          : 19515 (89225 expanded)
%              Number of equality atoms : 1579 (10596 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f188,f195,f202,f209,f222,f229,f236,f237,f244,f251,f258,f265,f272,f279,f286,f293,f300,f312,f319,f326,f333,f340,f360,f367,f392,f399,f408,f418,f426,f435,f453,f470,f483,f492,f500,f508,f518,f525,f537,f552,f560,f578,f585,f605,f607,f619,f626,f633,f645,f654,f669,f676,f683,f748,f758,f771,f778,f785,f848,f964,f980,f990,f992,f1014,f1021,f1028,f1080,f1090,f1095,f1112,f1119,f1141,f1148,f1172,f1179,f1186,f1193,f1201,f1205,f1213,f1221,f1242,f1256,f1262,f1270,f1293,f1307,f1320,f1334,f1347,f1350,f1365,f1377,f1398,f1411,f1418,f1425,f1428,f1458,f1472,f1485,f1499,f1512,f1515,f1566,f1591,f1654,f1671,f1672,f1679,f1686,f1695,f1721,f1736,f1807,f1809,f1817,f1843,f1847,f1855,f1863,f1881,f1889,f1899,f1908,f1916,f1924,f1966,f1979,f2000,f2014,f2063,f2160,f2199,f2546,f2569,f2710,f2725,f2734,f2743,f2750,f2754,f2755,f2759,f2760,f2764,f2765,f2769,f2770,f2772,f2774,f2778,f2781,f2783,f2785,f2787,f2789,f2791,f2793,f2796,f2799,f2802,f2805,f2807,f2808,f2809,f2811,f2815,f2818,f2820,f2821,f2825,f2829,f2831,f2833,f2837,f2841,f2843,f2844,f2847,f2849,f2851,f2853,f2854,f2856,f2857,f2860,f2862,f2864,f2884,f2897,f2911,f2925,f2932,f2987,f3000,f3014,f3028,f3035,f3398,f3429,f3568,f3578,f3610,f3617,f3624,f3632,f3639,f3646,f3655,f3662,f3670,f3677,f3678,f3679,f3680,f3681,f3682,f3690,f3698,f3700,f3705,f3710,f3715,f3720,f3721,f3722,f3730,f3738,f3746,f3751,f3756,f3761,f3766,f3773,f3780,f3781,f3784,f3787,f3790,f3791,f3792,f3794,f3796,f3798,f3799,f3800,f3808,f3810,f3811,f3813,f3815,f3816,f3817,f3819,f3821,f3822,f3823,f3824,f3825,f3826,f3827,f3828,f3829,f3830,f3831,f3832,f3834,f3836,f3838,f3840,f3849,f3858,f3860,f3861,f3862,f3864,f3866,f3868,f3870,f3894,f3901,f3908,f3911,f3935,f3942,f3949,f3951,f3953,f3981,f3988,f3995,f4005,f4011,f4012,f4105,f4120,f4135,f4143,f4158,f4173,f4326,f4331,f4336,f4341,f4352,f4478,f4486,f4501,f4516,f4524,f4539,f4554,f4570,f4580,f4590,f4600,f4607,f4617,f4627,f4634,f4644,f4651,f4658,f4665,f4672,f4679,f4686,f4693,f4700,f4707,f4714,f4721,f4728,f4735,f4745,f4755,f4762,f4772,f4779,f4786,f4793,f4800,f4807,f4814,f4821,f4828,f4835,f4842,f4849,f4856,f4863,f4873,f4883,f4890,f4900,f4907,f4914,f4921,f4928,f4935,f4942,f4949,f4956,f4963,f4970,f4977,f4984,f4991,f5001,f5011,f5018,f5028,f5035,f5042,f5049,f5056,f5063,f5070,f5077,f5084,f5091,f5098,f5105,f5112,f5118,f5122,f5126,f5130,f5134,f5144,f5168,f5187,f5305,f5320,f5335,f5343,f5358,f5373,f5526,f5531,f5536,f5541,f5603,f5696,f5709,f5718,f5732,f5746,f5765,f5774,f5848,f5857,f5866,f5872,f5881,f5887,f5893,f5899,f5905,f5911,f5917,f5923,f5929,f5935,f5941,f5947,f5953,f5959,f5968,f5977,f5983,f5992,f5998,f6004,f6010,f6016,f6022,f6028,f6034,f6040,f6046,f6052,f6058,f6064,f6074,f6078,f6082,f6092,f6118,f6134,f6174,f6178,f6181,f6185,f6187,f6189,f6243,f6256,f6269,f6363,f6378,f6393,f6401,f6416,f6431,f6447,f6457,f6467,f6477,f6484,f6494,f6504,f6511,f6521,f6528,f6535,f6542,f6549,f6556,f6563,f6570,f6577,f6584,f6591,f6598,f6605,f6612,f6622,f6632,f6639,f6649,f6656,f6663,f6670,f6677,f6684,f6691,f6698,f6705,f6712,f6719,f6726,f6733,f6740,f6750,f6760,f6767,f6777,f6784,f6791,f6798,f6805,f6812,f6819,f6826,f6833,f6840,f6847,f6854,f6861,f6868,f6878,f6888,f6895,f6905,f6912,f6919,f6926,f6933,f6940,f6947,f6954,f6961,f6968,f6975,f6982,f6989,f6994,f6999,f7004,f7009,f7011,f7014,f7017,f7019,f7021,f7023,f7025,f7026,f7034,f7042,f7043,f7044,f7047,f7050,f7051,f7059,f7067,f7068,f7069,f7070,f7072,f7073,f7075,f7077,f7080,f7082,f7084,f7086,f7088,f7089,f7090,f7091,f7092,f7093,f7094,f7095,f7096,f7097,f7101,f7104,f7124,f7125,f7126,f7140,f7148,f7156,f7157,f7160,f7163,f7165,f7167,f7169,f7171,f7187,f7197,f7198,f7387,f7608,f7621,f7630,f7644,f7658,f7677,f7686,f7760,f7769,f7778,f7784,f7793,f7799,f7805,f7811,f7817,f7823,f7829,f7835,f7841,f7847,f7853,f7859,f7865,f7871,f7880,f7889,f7895,f7904,f7910,f7916,f7922,f7928,f7934,f7940,f7946,f7952,f7958,f7964,f7970,f7976,f7986,f7990,f7994,f7999,f8022,f8030,f8037,f8065,f8078,f8091,f8391,f8530,f8531,f8532,f8533,f8534,f8535,f8537,f8538,f8539,f8541,f8636,f8649,f8658,f8672,f8686,f8705,f8714,f8788,f8797,f8806,f8812,f8821,f8827,f8833,f8839,f8845,f8851,f8857,f8863,f8869,f8875,f8881,f8887,f8893,f8899,f8908,f8917,f8923,f8932,f8938,f8944,f8950,f8956,f8962,f8968,f8974,f8980,f8986,f8992,f8998,f9004,f9008,f9012,f9016,f9044,f9085,f9093,f9100,f9168,f9314,f9327,f9340,f9507,f9610,f9625,f9640,f9648,f9663,f9678,f9831,f9836,f9841,f9846,f9906,f9916,f9950,f9961,f10065,f10080,f10095,f10103,f10118,f10133,f10286,f10291,f10296,f10301,f10349,f10356,f10392,f10399,f10406,f10413,f10420,f10427,f10434,f10441,f10449,f10456,f10463,f10470,f10472,f10479,f10486,f10493,f10500,f10503,f10510,f10512,f10519,f10525,f10526,f10575,f10590,f10605,f10613,f10628,f10643,f10701])).

fof(f10701,plain,
    ( ~ spl15_4
    | ~ spl15_6
    | spl15_17
    | ~ spl15_120
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_contradiction_clause,[],[f10700])).

fof(f10700,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_17
    | ~ spl15_120
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10699,f201])).

fof(f201,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl15_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f10699,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_17
    | ~ spl15_120
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(forward_demodulation,[],[f10698,f1147])).

fof(f1147,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl15_150 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1146,plain,
    ( spl15_150
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_150])])).

fof(f10698,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_17
    | ~ spl15_120
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10697,f235])).

fof(f235,plain,
    ( ~ v12_waybel_0(sK3,sK1)
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl15_17
  <=> ~ v12_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f10697,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v12_waybel_0(sK3,sK1)
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10696,f194])).

fof(f194,plain,
    ( l1_orders_2(sK1)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl15_4
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f10696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v12_waybel_0(sK3,sK1)
    | ~ spl15_120
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10558,f963])).

fof(f963,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ spl15_120 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl15_120
  <=> r1_tarski(k3_waybel_0(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_120])])).

fof(f10558,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v12_waybel_0(sK3,sK1)
    | ~ spl15_1260 ),
    inference(superposition,[],[f128,f10448])).

fof(f10448,plain,
    ( k3_waybel_0(sK0,sK3) = k3_waybel_0(sK1,sK3)
    | ~ spl15_1260 ),
    inference(avatar_component_clause,[],[f10447])).

fof(f10447,plain,
    ( spl15_1260
  <=> k3_waybel_0(sK0,sK3) = k3_waybel_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1260])])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t23_waybel_0)).

fof(f10643,plain,
    ( spl15_1296
    | ~ spl15_1299
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10630,f10447,f1146,f200,f193,f179,f10641,f10635])).

fof(f10635,plain,
    ( spl15_1296
  <=> r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1296])])).

fof(f10641,plain,
    ( spl15_1299
  <=> ~ v13_waybel_0(k3_waybel_0(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1299])])).

fof(f179,plain,
    ( spl15_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_0])])).

fof(f10630,plain,
    ( ~ v13_waybel_0(k3_waybel_0(sK0,sK3),sK0)
    | r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(forward_demodulation,[],[f10629,f10448])).

fof(f10629,plain,
    ( r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k3_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10533,f201])).

fof(f10533,plain,
    ( r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2109,f10448])).

fof(f2109,plain,
    ( ! [X3] :
        ( r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK1,X3)),k3_waybel_0(sK1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k3_waybel_0(sK1,X3),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2105,f180])).

fof(f180,plain,
    ( l1_orders_2(sK0)
    | ~ spl15_0 ),
    inference(avatar_component_clause,[],[f179])).

fof(f2105,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r1_tarski(k4_waybel_0(sK0,k3_waybel_0(sK1,X3)),k3_waybel_0(sK1,X3))
        | ~ v13_waybel_0(k3_waybel_0(sK1,X3),sK0) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t24_waybel_0)).

fof(f2099,plain,
    ( ! [X1] :
        ( m1_subset_1(k3_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f2098,f1147])).

fof(f2098,plain,
    ( ! [X1] :
        ( m1_subset_1(k3_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2090,f194])).

fof(f2090,plain,
    ( ! [X1] :
        ( m1_subset_1(k3_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1) )
    | ~ spl15_150 ),
    inference(superposition,[],[f143,f1147])).

fof(f143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_k3_waybel_0)).

fof(f10628,plain,
    ( spl15_1292
    | ~ spl15_1295
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10615,f10447,f1146,f200,f193,f179,f10626,f10620])).

fof(f10620,plain,
    ( spl15_1292
  <=> r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1292])])).

fof(f10626,plain,
    ( spl15_1295
  <=> ~ v12_waybel_0(k3_waybel_0(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1295])])).

fof(f10615,plain,
    ( ~ v12_waybel_0(k3_waybel_0(sK0,sK3),sK0)
    | r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(forward_demodulation,[],[f10614,f10448])).

fof(f10614,plain,
    ( r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k3_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10532,f201])).

fof(f10532,plain,
    ( r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k3_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2108,f10448])).

fof(f2108,plain,
    ( ! [X2] :
        ( r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK1,X2)),k3_waybel_0(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(k3_waybel_0(sK1,X2),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2104,f180])).

fof(f2104,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r1_tarski(k3_waybel_0(sK0,k3_waybel_0(sK1,X2)),k3_waybel_0(sK1,X2))
        | ~ v12_waybel_0(k3_waybel_0(sK1,X2),sK0) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f10613,plain,
    ( spl15_1290
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10606,f10447,f1146,f200,f193,f10611])).

fof(f10611,plain,
    ( spl15_1290
  <=> r1_tarski(k3_waybel_0(sK0,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1290])])).

fof(f10606,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10531,f201])).

fof(f10531,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2107,f10448])).

fof(f2107,plain,
    ( ! [X5] :
        ( r1_tarski(k3_waybel_0(sK1,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t3_subset)).

fof(f10605,plain,
    ( spl15_1286
    | ~ spl15_1289
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10592,f10447,f1146,f200,f193,f10603,f10597])).

fof(f10597,plain,
    ( spl15_1286
  <=> r1_tarski(k4_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1286])])).

fof(f10603,plain,
    ( spl15_1289
  <=> ~ v13_waybel_0(k3_waybel_0(sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1289])])).

fof(f10592,plain,
    ( ~ v13_waybel_0(k3_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k4_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(forward_demodulation,[],[f10591,f10448])).

fof(f10591,plain,
    ( r1_tarski(k4_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k3_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10530,f201])).

fof(f10530,plain,
    ( r1_tarski(k4_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2103,f10448])).

fof(f2103,plain,
    ( ! [X1] :
        ( r1_tarski(k4_waybel_0(sK1,k3_waybel_0(sK1,X1)),k3_waybel_0(sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k3_waybel_0(sK1,X1),sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f1202])).

fof(f1202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k4_waybel_0(sK1,X0),X0)
        | ~ v13_waybel_0(X0,sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1158,f194])).

fof(f1158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK1)
        | r1_tarski(k4_waybel_0(sK1,X0),X0)
        | ~ v13_waybel_0(X0,sK1) )
    | ~ spl15_150 ),
    inference(superposition,[],[f127,f1147])).

fof(f10590,plain,
    ( spl15_1282
    | ~ spl15_1285
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10577,f10447,f1146,f200,f193,f10588,f10582])).

fof(f10582,plain,
    ( spl15_1282
  <=> r1_tarski(k3_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1282])])).

fof(f10588,plain,
    ( spl15_1285
  <=> ~ v12_waybel_0(k3_waybel_0(sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1285])])).

fof(f10577,plain,
    ( ~ v12_waybel_0(k3_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k3_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(forward_demodulation,[],[f10576,f10448])).

fof(f10576,plain,
    ( r1_tarski(k3_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k3_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10529,f201])).

fof(f10529,plain,
    ( r1_tarski(k3_waybel_0(sK1,k3_waybel_0(sK0,sK3)),k3_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k3_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2102,f10448])).

fof(f2102,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(sK1,k3_waybel_0(sK1,X0)),k3_waybel_0(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(k3_waybel_0(sK1,X0),sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f1203])).

fof(f1203,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_waybel_0(sK1,X1),X1)
        | ~ v12_waybel_0(X1,sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1159,f194])).

fof(f1159,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK1)
        | r1_tarski(k3_waybel_0(sK1,X1),X1)
        | ~ v12_waybel_0(X1,sK1) )
    | ~ spl15_150 ),
    inference(superposition,[],[f129,f1147])).

fof(f10575,plain,
    ( spl15_1280
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(avatar_split_clause,[],[f10568,f10447,f1146,f200,f193,f10573])).

fof(f10573,plain,
    ( spl15_1280
  <=> m1_subset_1(k3_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1280])])).

fof(f10568,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(subsumption_resolution,[],[f10528,f201])).

fof(f10528,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1260 ),
    inference(superposition,[],[f2099,f10448])).

fof(f10526,plain,
    ( spl15_166
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_168 ),
    inference(avatar_split_clause,[],[f10523,f1240,f1199,f179,f1231])).

fof(f1231,plain,
    ( spl15_166
  <=> v12_waybel_0(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_166])])).

fof(f1199,plain,
    ( spl15_160
  <=> m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_160])])).

fof(f1240,plain,
    ( spl15_168
  <=> r1_tarski(k3_waybel_0(sK0,sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_168])])).

fof(f10523,plain,
    ( v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_168 ),
    inference(subsumption_resolution,[],[f10522,f180])).

fof(f10522,plain,
    ( ~ l1_orders_2(sK0)
    | v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_160
    | ~ spl15_168 ),
    inference(subsumption_resolution,[],[f10520,f1200])).

fof(f1200,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_160 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f10520,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_168 ),
    inference(resolution,[],[f1241,f128])).

fof(f1241,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ spl15_168 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f10525,plain,
    ( ~ spl15_0
    | ~ spl15_160
    | spl15_167
    | ~ spl15_168 ),
    inference(avatar_contradiction_clause,[],[f10524])).

fof(f10524,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_167
    | ~ spl15_168 ),
    inference(subsumption_resolution,[],[f10523,f1235])).

fof(f1235,plain,
    ( ~ v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_167 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f1234,plain,
    ( spl15_167
  <=> ~ v12_waybel_0(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_167])])).

fof(f10519,plain,
    ( spl15_1278
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10384,f1396,f1146,f193,f179,f10517])).

fof(f10517,plain,
    ( spl15_1278
  <=> k3_waybel_0(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) = k3_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1278])])).

fof(f1396,plain,
    ( spl15_202
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_202])])).

fof(f10384,plain,
    ( k3_waybel_0(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) = k3_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f130])).

fof(f130,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',existence_m1_subset_1)).

fof(f4382,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = k3_waybel_0(sK1,X0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f4365,f180])).

fof(f4365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | k3_waybel_0(sK0,X0) = k3_waybel_0(sK1,X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(duplicate_literal_removal,[],[f4364])).

fof(f4364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = k3_waybel_0(sK1,X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(equality_resolution,[],[f2486])).

fof(f2486,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k3_waybel_0(sK1,X3) = k3_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2485,f1147])).

fof(f2485,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k3_waybel_0(sK1,X3) = k3_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2484,f1397])).

fof(f1397,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl15_202 ),
    inference(avatar_component_clause,[],[f1396])).

fof(f2484,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k3_waybel_0(sK1,X3) = k3_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2465,f194])).

fof(f2465,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k3_waybel_0(sK1,X3) = k3_waybel_0(X2,X3) )
    | ~ spl15_150 ),
    inference(superposition,[],[f174,f1147])).

fof(f174,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k3_waybel_0(X0,X3) = k3_waybel_0(X1,X3) ) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                        & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t13_waybel_0)).

fof(f10512,plain,
    ( spl15_1268
    | ~ spl15_0
    | ~ spl15_4
    | spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10511,f1396,f1146,f390,f193,f179,f10477])).

fof(f10477,plain,
    ( spl15_1268
  <=> k3_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k3_waybel_0(sK1,sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1268])])).

fof(f390,plain,
    ( spl15_53
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f10511,plain,
    ( k3_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k3_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f10382,f391])).

fof(f391,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_53 ),
    inference(avatar_component_clause,[],[f390])).

fof(f10382,plain,
    ( k3_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k3_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f149])).

fof(f149,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc1_subset_1)).

fof(f10510,plain,
    ( spl15_1276
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10381,f1396,f1146,f249,f193,f179,f10508])).

fof(f10508,plain,
    ( spl15_1276
  <=> k3_waybel_0(sK0,sK7) = k3_waybel_0(sK1,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1276])])).

fof(f249,plain,
    ( spl15_20
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f10381,plain,
    ( k3_waybel_0(sK0,sK7) = k3_waybel_0(sK1,sK7)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f345])).

fof(f345,plain,
    ( ! [X0] : m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ spl15_20 ),
    inference(backward_demodulation,[],[f344,f146])).

fof(f146,plain,(
    ! [X0] : m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc2_subset_1)).

fof(f344,plain,
    ( ! [X0] : sK7 = sK9(X0)
    | ~ spl15_20 ),
    inference(resolution,[],[f341,f147])).

fof(f147,plain,(
    ! [X0] : v1_xboole_0(sK9(X0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK7 = X0 )
    | ~ spl15_20 ),
    inference(resolution,[],[f131,f250])).

fof(f250,plain,
    ( v1_xboole_0(sK7)
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f249])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t8_boole)).

fof(f10503,plain,
    ( spl15_1272
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | spl15_57
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10502,f1396,f1146,f406,f310,f193,f179,f10491])).

fof(f10491,plain,
    ( spl15_1272
  <=> k3_waybel_0(sK0,sK14(sK0)) = k3_waybel_0(sK1,sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1272])])).

fof(f310,plain,
    ( spl15_36
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f406,plain,
    ( spl15_57
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).

fof(f10502,plain,
    ( k3_waybel_0(sK0,sK14(sK0)) = k3_waybel_0(sK1,sK14(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_57
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f10501,f407])).

fof(f407,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_57 ),
    inference(avatar_component_clause,[],[f406])).

fof(f10501,plain,
    ( k3_waybel_0(sK0,sK14(sK0)) = k3_waybel_0(sK1,sK14(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f10380,f311])).

fof(f311,plain,
    ( l1_struct_0(sK0)
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f10380,plain,
    ( k3_waybel_0(sK0,sK14(sK0)) = k3_waybel_0(sK1,sK14(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f166])).

fof(f166,plain,(
    ! [X0] :
      ( m1_subset_1(sK14(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc4_struct_0)).

fof(f10500,plain,
    ( spl15_1274
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f10379,f2741,f1396,f1146,f193,f179,f10498])).

fof(f10498,plain,
    ( spl15_1274
  <=> k3_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k3_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1274])])).

fof(f2741,plain,
    ( spl15_334
  <=> m1_subset_1(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_334])])).

fof(f10379,plain,
    ( k3_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k3_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(resolution,[],[f4382,f2742])).

fof(f2742,plain,
    ( m1_subset_1(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_334 ),
    inference(avatar_component_clause,[],[f2741])).

fof(f10493,plain,
    ( spl15_1272
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_976 ),
    inference(avatar_split_clause,[],[f10378,f7610,f1396,f1146,f193,f179,f10491])).

fof(f7610,plain,
    ( spl15_976
  <=> m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_976])])).

fof(f10378,plain,
    ( k3_waybel_0(sK0,sK14(sK0)) = k3_waybel_0(sK1,sK14(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_976 ),
    inference(resolution,[],[f4382,f7611])).

fof(f7611,plain,
    ( m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_976 ),
    inference(avatar_component_clause,[],[f7610])).

fof(f10486,plain,
    ( spl15_1270
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f10377,f2732,f1396,f1146,f193,f179,f10484])).

fof(f10484,plain,
    ( spl15_1270
  <=> k3_waybel_0(sK0,sK14(sK1)) = k3_waybel_0(sK1,sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1270])])).

fof(f2732,plain,
    ( spl15_332
  <=> m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_332])])).

fof(f10377,plain,
    ( k3_waybel_0(sK0,sK14(sK1)) = k3_waybel_0(sK1,sK14(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(resolution,[],[f4382,f2733])).

fof(f2733,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_332 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f10479,plain,
    ( spl15_1268
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1084 ),
    inference(avatar_split_clause,[],[f10376,f8638,f1396,f1146,f193,f179,f10477])).

fof(f8638,plain,
    ( spl15_1084
  <=> m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1084])])).

fof(f10376,plain,
    ( k3_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k3_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1084 ),
    inference(resolution,[],[f4382,f8639])).

fof(f8639,plain,
    ( m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_1084 ),
    inference(avatar_component_clause,[],[f8638])).

fof(f10472,plain,
    ( spl15_1266
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10471,f1396,f1146,f193,f179,f10468])).

fof(f10468,plain,
    ( spl15_1266
  <=> k3_waybel_0(sK0,sK4(sK0)) = k3_waybel_0(sK1,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1266])])).

fof(f10471,plain,
    ( k3_waybel_0(sK0,sK4(sK0)) = k3_waybel_0(sK1,sK4(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f10375,f180])).

fof(f10375,plain,
    ( k3_waybel_0(sK0,sK4(sK0)) = k3_waybel_0(sK1,sK4(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f123])).

fof(f123,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v13_waybel_0(X1,X0)
          & v12_waybel_0(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] :
          ( v13_waybel_0(X1,X0)
          & v12_waybel_0(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc7_waybel_0)).

fof(f10470,plain,
    ( spl15_1266
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_688 ),
    inference(avatar_split_clause,[],[f10374,f5698,f1396,f1146,f193,f179,f10468])).

fof(f5698,plain,
    ( spl15_688
  <=> m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_688])])).

fof(f10374,plain,
    ( k3_waybel_0(sK0,sK4(sK0)) = k3_waybel_0(sK1,sK4(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_688 ),
    inference(resolution,[],[f4382,f5699])).

fof(f5699,plain,
    ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_688 ),
    inference(avatar_component_clause,[],[f5698])).

fof(f10463,plain,
    ( spl15_1264
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f10373,f1887,f1396,f1146,f193,f179,f10461])).

fof(f10461,plain,
    ( spl15_1264
  <=> k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k3_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1264])])).

fof(f1887,plain,
    ( spl15_278
  <=> m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_278])])).

fof(f10373,plain,
    ( k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k3_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_278 ),
    inference(resolution,[],[f4382,f1888])).

fof(f1888,plain,
    ( m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_278 ),
    inference(avatar_component_clause,[],[f1887])).

fof(f10456,plain,
    ( spl15_1262
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10372,f1396,f1199,f1146,f193,f179,f10454])).

fof(f10454,plain,
    ( spl15_1262
  <=> k3_waybel_0(sK0,sK4(sK1)) = k3_waybel_0(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1262])])).

fof(f10372,plain,
    ( k3_waybel_0(sK0,sK4(sK1)) = k3_waybel_0(sK1,sK4(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f1200])).

fof(f10449,plain,
    ( spl15_1260
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f10371,f1396,f1146,f200,f193,f179,f10447])).

fof(f10371,plain,
    ( k3_waybel_0(sK0,sK3) = k3_waybel_0(sK1,sK3)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f4382,f201])).

fof(f10441,plain,
    ( spl15_1258
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_978 ),
    inference(avatar_split_clause,[],[f10369,f7619,f1396,f1146,f193,f179,f10439])).

fof(f10439,plain,
    ( spl15_1258
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1258])])).

fof(f7619,plain,
    ( spl15_978
  <=> m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_978])])).

fof(f10369,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_978 ),
    inference(resolution,[],[f4382,f7620])).

fof(f7620,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_978 ),
    inference(avatar_component_clause,[],[f7619])).

fof(f10434,plain,
    ( spl15_1256
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_790 ),
    inference(avatar_split_clause,[],[f10368,f6361,f1396,f1146,f193,f179,f10432])).

fof(f10432,plain,
    ( spl15_1256
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1256])])).

fof(f6361,plain,
    ( spl15_790
  <=> m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_790])])).

fof(f10368,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_790 ),
    inference(resolution,[],[f4382,f6362])).

fof(f6362,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_790 ),
    inference(avatar_component_clause,[],[f6361])).

fof(f10427,plain,
    ( spl15_1254
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1086 ),
    inference(avatar_split_clause,[],[f10367,f8647,f1396,f1146,f193,f179,f10425])).

fof(f10425,plain,
    ( spl15_1254
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1254])])).

fof(f8647,plain,
    ( spl15_1086
  <=> m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1086])])).

fof(f10367,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1086 ),
    inference(resolution,[],[f4382,f8648])).

fof(f8648,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_1086 ),
    inference(avatar_component_clause,[],[f8647])).

fof(f10420,plain,
    ( spl15_1252
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_492 ),
    inference(avatar_split_clause,[],[f10366,f4484,f1396,f1146,f193,f179,f10418])).

fof(f10418,plain,
    ( spl15_1252
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1252])])).

fof(f4484,plain,
    ( spl15_492
  <=> m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_492])])).

fof(f10366,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_492 ),
    inference(resolution,[],[f4382,f4485])).

fof(f4485,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_492 ),
    inference(avatar_component_clause,[],[f4484])).

fof(f10413,plain,
    ( spl15_1250
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f10365,f5707,f1396,f1146,f193,f179,f10411])).

fof(f10411,plain,
    ( spl15_1250
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1250])])).

fof(f5707,plain,
    ( spl15_690
  <=> m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_690])])).

fof(f10365,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_690 ),
    inference(resolution,[],[f4382,f5708])).

fof(f5708,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_690 ),
    inference(avatar_component_clause,[],[f5707])).

fof(f10406,plain,
    ( spl15_1248
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_664 ),
    inference(avatar_split_clause,[],[f10364,f5303,f1396,f1146,f193,f179,f10404])).

fof(f10404,plain,
    ( spl15_1248
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1248])])).

fof(f5303,plain,
    ( spl15_664
  <=> m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_664])])).

fof(f10364,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_664 ),
    inference(resolution,[],[f4382,f5304])).

fof(f5304,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_664 ),
    inference(avatar_component_clause,[],[f5303])).

fof(f10399,plain,
    ( spl15_1246
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_468 ),
    inference(avatar_split_clause,[],[f10363,f4103,f1396,f1146,f193,f179,f10397])).

fof(f10397,plain,
    ( spl15_1246
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1246])])).

fof(f4103,plain,
    ( spl15_468
  <=> m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_468])])).

fof(f10363,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_468 ),
    inference(resolution,[],[f4382,f4104])).

fof(f4104,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_468 ),
    inference(avatar_component_clause,[],[f4103])).

fof(f10392,plain,
    ( spl15_1244
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1192 ),
    inference(avatar_split_clause,[],[f10362,f9608,f1396,f1146,f193,f179,f10390])).

fof(f10390,plain,
    ( spl15_1244
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) = k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1244])])).

fof(f9608,plain,
    ( spl15_1192
  <=> m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1192])])).

fof(f10362,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) = k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1192 ),
    inference(resolution,[],[f4382,f9609])).

fof(f9609,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_1192 ),
    inference(avatar_component_clause,[],[f9608])).

fof(f10356,plain,
    ( spl15_1242
    | spl15_157 ),
    inference(avatar_split_clause,[],[f10319,f1184,f10354])).

fof(f10354,plain,
    ( spl15_1242
  <=> g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1242])])).

fof(f1184,plain,
    ( spl15_157
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_157])])).

fof(f10319,plain,
    ( g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),sK10(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))
    | ~ spl15_157 ),
    inference(resolution,[],[f9951,f1185])).

fof(f1185,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_157 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f9951,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X0))
      | g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0))) = g1_orders_2(u1_struct_0(g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0)))),u1_orders_2(g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0))))) ) ),
    inference(subsumption_resolution,[],[f3060,f1800])).

fof(f1800,plain,(
    ! [X2] :
      ( l1_orders_2(g1_orders_2(X2,sK10(k2_zfmisc_1(X2,X2))))
      | v1_xboole_0(k2_zfmisc_1(X2,X2)) ) ),
    inference(resolution,[],[f163,f149])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_g1_orders_2)).

fof(f3060,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X0))
      | ~ l1_orders_2(g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0))))
      | g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0))) = g1_orders_2(u1_struct_0(g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0)))),u1_orders_2(g1_orders_2(X0,sK10(k2_zfmisc_1(X0,X0))))) ) ),
    inference(resolution,[],[f1709,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',abstractness_v1_orders_2)).

fof(f1709,plain,(
    ! [X2] :
      ( v1_orders_2(g1_orders_2(X2,sK10(k2_zfmisc_1(X2,X2))))
      | v1_xboole_0(k2_zfmisc_1(X2,X2)) ) ),
    inference(resolution,[],[f162,f149])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f10349,plain,
    ( spl15_1240
    | spl15_253 ),
    inference(avatar_split_clause,[],[f10318,f1677,f10347])).

fof(f10347,plain,
    ( spl15_1240
  <=> g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))),u1_orders_2(g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1240])])).

fof(f1677,plain,
    ( spl15_253
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_253])])).

fof(f10318,plain,
    ( g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))),u1_orders_2(g1_orders_2(u1_struct_0(sK12),sK10(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))))
    | ~ spl15_253 ),
    inference(resolution,[],[f9951,f1678])).

fof(f1678,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))
    | ~ spl15_253 ),
    inference(avatar_component_clause,[],[f1677])).

fof(f10301,plain,
    ( spl15_1222
    | ~ spl15_1225
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10300,f5185,f4484,f1146,f193,f10078,f10072])).

fof(f10072,plain,
    ( spl15_1222
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1222])])).

fof(f10078,plain,
    ( spl15_1225
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1225])])).

fof(f5185,plain,
    ( spl15_662
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_662])])).

fof(f10300,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10299,f5186])).

fof(f5186,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
    | ~ spl15_662 ),
    inference(avatar_component_clause,[],[f5185])).

fof(f10299,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10298,f4485])).

fof(f10298,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10297,f1147])).

fof(f10297,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10053,f194])).

fof(f10053,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_662 ),
    inference(superposition,[],[f2032,f5186])).

fof(f2032,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_waybel_0(X1,k4_waybel_0(X1,X0)),k4_waybel_0(X1,X0))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(k4_waybel_0(X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f2021])).

fof(f2021,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X1)
      | r1_tarski(k3_waybel_0(X1,k4_waybel_0(X1,X0)),k4_waybel_0(X1,X0))
      | ~ v12_waybel_0(k4_waybel_0(X1,X0),X1) ) ),
    inference(resolution,[],[f140,f129])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_k4_waybel_0)).

fof(f10296,plain,
    ( spl15_1226
    | ~ spl15_1229
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10295,f5185,f4484,f1146,f193,f10093,f10087])).

fof(f10087,plain,
    ( spl15_1226
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1226])])).

fof(f10093,plain,
    ( spl15_1229
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1229])])).

fof(f10295,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10294,f5186])).

fof(f10294,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10293,f4485])).

fof(f10293,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10292,f1147])).

fof(f10292,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10052,f194])).

fof(f10052,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_662 ),
    inference(superposition,[],[f2031,f5186])).

fof(f2031,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_waybel_0(X3,k4_waybel_0(X3,X2)),k4_waybel_0(X3,X2))
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v13_waybel_0(k4_waybel_0(X3,X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f2022])).

fof(f2022,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ l1_orders_2(X3)
      | r1_tarski(k4_waybel_0(X3,k4_waybel_0(X3,X2)),k4_waybel_0(X3,X2))
      | ~ v13_waybel_0(k4_waybel_0(X3,X2),X3) ) ),
    inference(resolution,[],[f140,f127])).

fof(f10291,plain,
    ( spl15_1230
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10290,f5185,f4484,f1146,f193,f10101])).

fof(f10101,plain,
    ( spl15_1230
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1230])])).

fof(f10290,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10289,f4485])).

fof(f10289,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10288,f1147])).

fof(f10288,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10287,f1147])).

fof(f10287,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10051,f194])).

fof(f10051,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_662 ),
    inference(superposition,[],[f2026,f5186])).

fof(f2026,plain,(
    ! [X8,X9] :
      ( r1_tarski(k4_waybel_0(X9,X8),u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(resolution,[],[f140,f139])).

fof(f10286,plain,
    ( spl15_1220
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10285,f5185,f4484,f1146,f193,f10063])).

fof(f10063,plain,
    ( spl15_1220
  <=> m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1220])])).

fof(f10285,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10284,f4485])).

fof(f10284,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10283,f1147])).

fof(f10283,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10282,f1147])).

fof(f10282,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f10049,f194])).

fof(f10049,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_662 ),
    inference(superposition,[],[f140,f5186])).

fof(f10133,plain,
    ( spl15_1236
    | ~ spl15_1239
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10120,f5185,f4484,f1146,f193,f179,f10131,f10125])).

fof(f10125,plain,
    ( spl15_1236
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1236])])).

fof(f10131,plain,
    ( spl15_1239
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1239])])).

fof(f10120,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10119,f5186])).

fof(f10119,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9975,f4485])).

fof(f9975,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2048,f5186])).

fof(f2048,plain,
    ( ! [X3] :
        ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK1,X3)),k4_waybel_0(sK1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK1,X3),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2044,f180])).

fof(f2044,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK1,X3)),k4_waybel_0(sK1,X3))
        | ~ v13_waybel_0(k4_waybel_0(sK1,X3),sK0) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f127])).

fof(f2038,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f2037,f1147])).

fof(f2037,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2029,f194])).

fof(f2029,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_waybel_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1) )
    | ~ spl15_150 ),
    inference(superposition,[],[f140,f1147])).

fof(f10118,plain,
    ( spl15_1232
    | ~ spl15_1235
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10105,f5185,f4484,f1146,f193,f179,f10116,f10110])).

fof(f10110,plain,
    ( spl15_1232
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1232])])).

fof(f10116,plain,
    ( spl15_1235
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1235])])).

fof(f10105,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10104,f5186])).

fof(f10104,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9974,f4485])).

fof(f9974,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2047,f5186])).

fof(f2047,plain,
    ( ! [X2] :
        ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK1,X2)),k4_waybel_0(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK1,X2),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2043,f180])).

fof(f2043,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK1,X2)),k4_waybel_0(sK1,X2))
        | ~ v12_waybel_0(k4_waybel_0(sK1,X2),sK0) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f129])).

fof(f10103,plain,
    ( spl15_1230
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10096,f5185,f4484,f1146,f193,f10101])).

fof(f10096,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9973,f4485])).

fof(f9973,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2046,f5186])).

fof(f2046,plain,
    ( ! [X5] :
        ( r1_tarski(k4_waybel_0(sK1,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f139])).

fof(f10095,plain,
    ( spl15_1226
    | ~ spl15_1229
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10082,f5185,f4484,f1146,f193,f10093,f10087])).

fof(f10082,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10081,f5186])).

fof(f10081,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9972,f4485])).

fof(f9972,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2042,f5186])).

fof(f2042,plain,
    ( ! [X1] :
        ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK1,X1)),k4_waybel_0(sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK1,X1),sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f1202])).

fof(f10080,plain,
    ( spl15_1222
    | ~ spl15_1225
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10067,f5185,f4484,f1146,f193,f10078,f10072])).

fof(f10067,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(forward_demodulation,[],[f10066,f5186])).

fof(f10066,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9971,f4485])).

fof(f9971,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2041,f5186])).

fof(f2041,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK1,X0)),k4_waybel_0(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK1,X0),sK1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f1203])).

fof(f10065,plain,
    ( spl15_1220
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(avatar_split_clause,[],[f10058,f5185,f4484,f1146,f193,f10063])).

fof(f10058,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_492
    | ~ spl15_662 ),
    inference(subsumption_resolution,[],[f9970,f4485])).

fof(f9970,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_662 ),
    inference(superposition,[],[f2038,f5186])).

fof(f9961,plain,
    ( spl15_1218
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1192 ),
    inference(avatar_split_clause,[],[f9952,f9608,f1396,f1146,f193,f179,f9948])).

fof(f9948,plain,
    ( spl15_1218
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) = k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1218])])).

fof(f9952,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) = k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1192 ),
    inference(resolution,[],[f9609,f3584])).

fof(f3584,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = k4_waybel_0(sK1,X0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3554,f180])).

fof(f3554,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | k4_waybel_0(sK0,X0) = k4_waybel_0(sK1,X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(duplicate_literal_removal,[],[f3553])).

fof(f3553,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = k4_waybel_0(sK1,X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(equality_resolution,[],[f2325])).

fof(f2325,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k4_waybel_0(sK1,X3) = k4_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2324,f1147])).

fof(f2324,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k4_waybel_0(sK1,X3) = k4_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2323,f1397])).

fof(f2323,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k4_waybel_0(sK1,X3) = k4_waybel_0(X2,X3) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2304,f194])).

fof(f2304,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | k4_waybel_0(sK1,X3) = k4_waybel_0(X2,X3) )
    | ~ spl15_150 ),
    inference(superposition,[],[f173,f1147])).

fof(f173,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k4_waybel_0(X0,X3) = k4_waybel_0(X1,X3) ) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f9950,plain,
    ( spl15_1218
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1202 ),
    inference(avatar_split_clause,[],[f9936,f9646,f1396,f1146,f193,f179,f9948])).

fof(f9646,plain,
    ( spl15_1202
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1202])])).

fof(f9936,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) = k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1202 ),
    inference(resolution,[],[f9647,f3600])).

fof(f3600,plain,
    ( ! [X6] :
        ( ~ r1_tarski(X6,u1_struct_0(sK0))
        | k4_waybel_0(sK0,X6) = k4_waybel_0(sK1,X6) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f9647,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ spl15_1202 ),
    inference(avatar_component_clause,[],[f9646])).

fof(f9916,plain,
    ( spl15_1212
    | spl15_1216
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f9912,f1853,f1396,f1146,f193,f9914,f9901])).

fof(f9901,plain,
    ( spl15_1212
  <=> ! [X15] : g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1212])])).

fof(f9914,plain,
    ( spl15_1216
  <=> ! [X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1216])])).

fof(f1853,plain,
    ( spl15_272
  <=> u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_272])])).

fof(f9912,plain,
    ( ! [X19,X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19))))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(duplicate_literal_removal,[],[f9911])).

fof(f9911,plain,
    ( ! [X19,X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f9910,f1854])).

fof(f1854,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(avatar_component_clause,[],[f1853])).

fof(f9910,plain,
    ( ! [X19,X20] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(inner_rewriting,[],[f9909])).

fof(f9909,plain,
    ( ! [X19,X20] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19)))))))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19)))),X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f9873,f1802])).

fof(f1802,plain,(
    ! [X5] : l1_orders_2(g1_orders_2(X5,sK5(k1_zfmisc_1(k2_zfmisc_1(X5,X5))))) ),
    inference(resolution,[],[f163,f130])).

fof(f9873,plain,
    ( ! [X19,X20] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19)))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19)))))))
        | k3_waybel_0(sK1,X20) = k3_waybel_0(g1_orders_2(X19,sK5(k1_zfmisc_1(k2_zfmisc_1(X19,X19)))),X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(superposition,[],[f2486,f9510])).

fof(f9510,plain,(
    ! [X0] : g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) = g1_orders_2(u1_struct_0(g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_orders_2(g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))) ),
    inference(subsumption_resolution,[],[f1751,f1802])).

fof(f1751,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))
      | g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) = g1_orders_2(u1_struct_0(g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_orders_2(g1_orders_2(X0,sK5(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))) ) ),
    inference(resolution,[],[f1711,f134])).

fof(f1711,plain,(
    ! [X5] : v1_orders_2(g1_orders_2(X5,sK5(k1_zfmisc_1(k2_zfmisc_1(X5,X5))))) ),
    inference(resolution,[],[f162,f130])).

fof(f9906,plain,
    ( spl15_1212
    | spl15_1214
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f9899,f1853,f1396,f1146,f193,f9904,f9901])).

fof(f9904,plain,
    ( spl15_1214
  <=> ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1214])])).

fof(f9899,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15))))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X16) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(duplicate_literal_removal,[],[f9898])).

fof(f9898,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X16) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f9897,f1854])).

fof(f9897,plain,
    ( ! [X15,X16] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X16) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(inner_rewriting,[],[f9896])).

fof(f9896,plain,
    ( ! [X15,X16] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))))))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))),X16) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f9871,f1802])).

fof(f9871,plain,
    ( ! [X15,X16] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))))))
        | k4_waybel_0(sK1,X16) = k4_waybel_0(g1_orders_2(X15,sK5(k1_zfmisc_1(k2_zfmisc_1(X15,X15)))),X16) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(superposition,[],[f2325,f9510])).

fof(f9846,plain,
    ( spl15_1194
    | ~ spl15_1197
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9845,f5166,f4103,f1146,f193,f9623,f9617])).

fof(f9617,plain,
    ( spl15_1194
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1194])])).

fof(f9623,plain,
    ( spl15_1197
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1197])])).

fof(f5166,plain,
    ( spl15_660
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_660])])).

fof(f9845,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9844,f5167])).

fof(f5167,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK3))
    | ~ spl15_660 ),
    inference(avatar_component_clause,[],[f5166])).

fof(f9844,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9843,f4104])).

fof(f9843,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9842,f1147])).

fof(f9842,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9598,f194])).

fof(f9598,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_660 ),
    inference(superposition,[],[f2032,f5167])).

fof(f9841,plain,
    ( spl15_1198
    | ~ spl15_1201
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9840,f5166,f4103,f1146,f193,f9638,f9632])).

fof(f9632,plain,
    ( spl15_1198
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1198])])).

fof(f9638,plain,
    ( spl15_1201
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1201])])).

fof(f9840,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9839,f5167])).

fof(f9839,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9838,f4104])).

fof(f9838,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9837,f1147])).

fof(f9837,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9597,f194])).

fof(f9597,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_660 ),
    inference(superposition,[],[f2031,f5167])).

fof(f9836,plain,
    ( spl15_1202
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9835,f5166,f4103,f1146,f193,f9646])).

fof(f9835,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9834,f4104])).

fof(f9834,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9833,f1147])).

fof(f9833,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9832,f1147])).

fof(f9832,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9596,f194])).

fof(f9596,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_660 ),
    inference(superposition,[],[f2026,f5167])).

fof(f9831,plain,
    ( spl15_1192
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9830,f5166,f4103,f1146,f193,f9608])).

fof(f9830,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9829,f4104])).

fof(f9829,plain,
    ( ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9828,f1147])).

fof(f9828,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9827,f1147])).

fof(f9827,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9594,f194])).

fof(f9594,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_660 ),
    inference(superposition,[],[f140,f5167])).

fof(f9678,plain,
    ( spl15_1208
    | ~ spl15_1211
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9665,f5166,f4103,f1146,f193,f179,f9676,f9670])).

fof(f9670,plain,
    ( spl15_1208
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1208])])).

fof(f9676,plain,
    ( spl15_1211
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1211])])).

fof(f9665,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9664,f5167])).

fof(f9664,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9520,f4104])).

fof(f9520,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2048,f5167])).

fof(f9663,plain,
    ( spl15_1204
    | ~ spl15_1207
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9650,f5166,f4103,f1146,f193,f179,f9661,f9655])).

fof(f9655,plain,
    ( spl15_1204
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1204])])).

fof(f9661,plain,
    ( spl15_1207
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1207])])).

fof(f9650,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9649,f5167])).

fof(f9649,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9519,f4104])).

fof(f9519,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2047,f5167])).

fof(f9648,plain,
    ( spl15_1202
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9641,f5166,f4103,f1146,f193,f9646])).

fof(f9641,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9518,f4104])).

fof(f9518,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2046,f5167])).

fof(f9640,plain,
    ( spl15_1198
    | ~ spl15_1201
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9627,f5166,f4103,f1146,f193,f9638,f9632])).

fof(f9627,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9626,f5167])).

fof(f9626,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9517,f4104])).

fof(f9517,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2042,f5167])).

fof(f9625,plain,
    ( spl15_1194
    | ~ spl15_1197
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9612,f5166,f4103,f1146,f193,f9623,f9617])).

fof(f9612,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(forward_demodulation,[],[f9611,f5167])).

fof(f9611,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9516,f4104])).

fof(f9516,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))),k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2041,f5167])).

fof(f9610,plain,
    ( spl15_1192
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f9603,f5166,f4103,f1146,f193,f9608])).

fof(f9603,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_468
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f9515,f4104])).

fof(f9515,plain,
    ( m1_subset_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_660 ),
    inference(superposition,[],[f2038,f5167])).

fof(f9507,plain,
    ( spl15_1190
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f9490,f242,f9505])).

fof(f9505,plain,
    ( spl15_1190
  <=> g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))),u1_orders_2(g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1190])])).

fof(f242,plain,
    ( spl15_18
  <=> l1_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f9490,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))),u1_orders_2(g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))))
    | ~ spl15_18 ),
    inference(resolution,[],[f9477,f243])).

fof(f243,plain,
    ( l1_orders_2(sK6)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f9477,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) ) ),
    inference(subsumption_resolution,[],[f1739,f1796])).

fof(f1796,plain,(
    ! [X0] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f163,f135])).

fof(f135,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_u1_orders_2)).

fof(f1739,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) ) ),
    inference(resolution,[],[f1705,f134])).

fof(f1705,plain,(
    ! [X0] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f162,f135])).

fof(f9340,plain,
    ( ~ spl15_1187
    | spl15_1188
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1086 ),
    inference(avatar_split_clause,[],[f9307,f8647,f1146,f193,f9338,f9332])).

fof(f9332,plain,
    ( spl15_1187
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1187])])).

fof(f9338,plain,
    ( spl15_1188
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1188])])).

fof(f9307,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1086 ),
    inference(resolution,[],[f8648,f1202])).

fof(f9327,plain,
    ( ~ spl15_1183
    | spl15_1184
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1086 ),
    inference(avatar_split_clause,[],[f9306,f8647,f1146,f193,f9325,f9319])).

fof(f9319,plain,
    ( spl15_1183
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1183])])).

fof(f9325,plain,
    ( spl15_1184
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1184])])).

fof(f9306,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_1086 ),
    inference(resolution,[],[f8648,f1203])).

fof(f9314,plain,
    ( spl15_1180
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1086 ),
    inference(avatar_split_clause,[],[f9305,f8647,f1396,f1146,f193,f179,f9166])).

fof(f9166,plain,
    ( spl15_1180
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1180])])).

fof(f9305,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1086 ),
    inference(resolution,[],[f8648,f3584])).

fof(f9168,plain,
    ( spl15_1180
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1088 ),
    inference(avatar_split_clause,[],[f9154,f8656,f1396,f1146,f193,f179,f9166])).

fof(f8656,plain,
    ( spl15_1088
  <=> r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1088])])).

fof(f9154,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_1088 ),
    inference(resolution,[],[f8657,f3600])).

fof(f8657,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl15_1088 ),
    inference(avatar_component_clause,[],[f8656])).

fof(f9100,plain,
    ( spl15_1178
    | ~ spl15_1084 ),
    inference(avatar_split_clause,[],[f9071,f8638,f9098])).

fof(f9098,plain,
    ( spl15_1178
  <=> r1_tarski(sK10(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1178])])).

fof(f9071,plain,
    ( r1_tarski(sK10(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1084 ),
    inference(resolution,[],[f8639,f139])).

fof(f9093,plain,
    ( ~ spl15_1177
    | spl15_1082
    | ~ spl15_0
    | ~ spl15_1084 ),
    inference(avatar_split_clause,[],[f9086,f8638,f179,f8631,f9091])).

fof(f9091,plain,
    ( spl15_1177
  <=> ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1177])])).

fof(f8631,plain,
    ( spl15_1082
  <=> r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1082])])).

fof(f9086,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_1084 ),
    inference(subsumption_resolution,[],[f9069,f180])).

fof(f9069,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK0)
    | ~ spl15_1084 ),
    inference(resolution,[],[f8639,f127])).

fof(f9085,plain,
    ( ~ spl15_1173
    | spl15_1174
    | ~ spl15_0
    | ~ spl15_1084 ),
    inference(avatar_split_clause,[],[f9072,f8638,f179,f9083,f9077])).

fof(f9077,plain,
    ( spl15_1173
  <=> ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1173])])).

fof(f9083,plain,
    ( spl15_1174
  <=> r1_tarski(k3_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1174])])).

fof(f9072,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_1084 ),
    inference(subsumption_resolution,[],[f9068,f180])).

fof(f9068,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK0)
    | ~ spl15_1084 ),
    inference(resolution,[],[f8639,f129])).

fof(f9044,plain,
    ( spl15_53
    | spl15_1085 ),
    inference(avatar_contradiction_clause,[],[f9043])).

fof(f9043,plain,
    ( $false
    | ~ spl15_53
    | ~ spl15_1085 ),
    inference(subsumption_resolution,[],[f9041,f391])).

fof(f9041,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_1085 ),
    inference(resolution,[],[f8642,f149])).

fof(f8642,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_1085 ),
    inference(avatar_component_clause,[],[f8641])).

fof(f8641,plain,
    ( spl15_1085
  <=> ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1085])])).

fof(f9016,plain,
    ( spl15_1088
    | ~ spl15_1085
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f9015,f3668,f1146,f193,f8641,f8656])).

fof(f3668,plain,
    ( spl15_410
  <=> k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_410])])).

fof(f9015,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f9014,f1147])).

fof(f9014,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f9013,f1147])).

fof(f9013,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f8625,f194])).

fof(f8625,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_410 ),
    inference(superposition,[],[f2026,f3669])).

fof(f3669,plain,
    ( k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | ~ spl15_410 ),
    inference(avatar_component_clause,[],[f3668])).

fof(f9012,plain,
    ( spl15_1086
    | ~ spl15_1085
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f9011,f3668,f1146,f193,f8641,f8647])).

fof(f9011,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f9010,f1147])).

fof(f9010,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f9009,f1147])).

fof(f9009,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f8623,f194])).

fof(f8623,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_410 ),
    inference(superposition,[],[f140,f3669])).

fof(f9008,plain,
    ( ~ spl15_1083
    | ~ spl15_1085
    | ~ spl15_4
    | ~ spl15_150
    | spl15_189
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f9007,f3668,f1326,f1146,f193,f8641,f8634])).

fof(f8634,plain,
    ( spl15_1083
  <=> ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1083])])).

fof(f1326,plain,
    ( spl15_189
  <=> ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_189])])).

fof(f9007,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_189
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f9006,f1147])).

fof(f9006,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_189
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f9005,f1327])).

fof(f1327,plain,
    ( ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | ~ spl15_189 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f9005,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v13_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f8622,f194])).

fof(f8622,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | ~ spl15_410 ),
    inference(superposition,[],[f126,f3669])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f9004,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1170
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f9000,f3668,f1146,f249,f193,f179,f9002,f8703,f8684,f8641])).

fof(f8684,plain,
    ( spl15_1097
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1097])])).

fof(f8703,plain,
    ( spl15_1101
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1101])])).

fof(f9002,plain,
    ( spl15_1170
  <=> ! [X79] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X79))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1170])])).

fof(f9000,plain,
    ( ! [X79] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X79))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8999,f3669])).

fof(f8999,plain,
    ( ! [X79] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8621,f3669])).

fof(f8621,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2302,f3669])).

fof(f2302,plain,
    ( ! [X35,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X35),sK0)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X35))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X35)),X36))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f888])).

fof(f888,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(X3)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f838,f341])).

fof(f838,plain,(
    ! [X8,X7] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f154,f130])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',cc3_relset_1)).

fof(f2133,plain,
    ( ! [X1] :
        ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK1,X1)))
        | ~ v13_waybel_0(k4_waybel_0(sK1,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2048,f378])).

fof(f378,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | v1_xboole_0(X4)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f148,f138])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',cc1_subset_1)).

fof(f8998,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1168
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8994,f3668,f1146,f249,f193,f179,f8996,f8703,f8684,f8641])).

fof(f8996,plain,
    ( spl15_1168
  <=> ! [X78] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))),X78) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1168])])).

fof(f8994,plain,
    ( ! [X78] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))),X78) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8993,f3669])).

fof(f8993,plain,
    ( ! [X78] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8620,f3669])).

fof(f8620,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2301,f3669])).

fof(f2301,plain,
    ( ! [X33,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X33),sK0)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X33))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X33)))),X34) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f876])).

fof(f876,plain,
    ( ! [X12,X13] :
        ( ~ v1_xboole_0(X12)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(X12)),X13) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f851,f379])).

fof(f379,plain,(
    ! [X5] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X5)))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f148,f130])).

fof(f851,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(X5)
        | k2_zfmisc_1(X5,X6) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f841,f341])).

fof(f841,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k2_zfmisc_1(X2,X3))
      | ~ v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f836,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK10(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f836,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | v1_xboole_0(sK10(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f154,f149])).

fof(f8992,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1166
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8988,f3668,f1146,f249,f193,f179,f8990,f8703,f8684,f8641])).

fof(f8990,plain,
    ( spl15_1166
  <=> ! [X77,X76] : k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))),X77) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1166])])).

fof(f8988,plain,
    ( ! [X76,X77] :
        ( k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))),X77) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8987,f3669])).

fof(f8987,plain,
    ( ! [X76,X77] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8619,f3669])).

fof(f8619,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2300,f3669])).

fof(f2300,plain,
    ( ! [X30,X31,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X30),sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X30))
        | k2_zfmisc_1(k2_zfmisc_1(X31,k4_waybel_0(sK0,k4_waybel_0(sK1,X30))),X32) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f874])).

fof(f874,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_xboole_0(X8)
        | k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f851,f606])).

fof(f606,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k2_zfmisc_1(X3,X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f600,f150])).

fof(f600,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | v1_xboole_0(sK10(k2_zfmisc_1(X3,X2)))
      | v1_xboole_0(k2_zfmisc_1(X3,X2)) ) ),
    inference(resolution,[],[f153,f149])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',cc4_relset_1)).

fof(f8986,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1164
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8982,f3668,f1146,f249,f193,f179,f8984,f8703,f8684,f8641])).

fof(f8984,plain,
    ( spl15_1164
  <=> ! [X75,X74] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X74),X75) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1164])])).

fof(f8982,plain,
    ( ! [X74,X75] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X74),X75) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8981,f3669])).

fof(f8981,plain,
    ( ! [X74,X75] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8618,f3669])).

fof(f8618,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2299,f3669])).

fof(f2299,plain,
    ( ! [X28,X29,X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X27),sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X27))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X27)),X28),X29) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f873])).

fof(f873,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(X4)
        | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f851,f841])).

fof(f8980,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1162
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8976,f3668,f1146,f249,f193,f179,f8978,f8703,f8684,f8641])).

fof(f8978,plain,
    ( spl15_1162
  <=> ! [X73,X72] : k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X73)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1162])])).

fof(f8976,plain,
    ( ! [X72,X73] :
        ( k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X73)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8975,f3669])).

fof(f8975,plain,
    ( ! [X72,X73] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8617,f3669])).

fof(f8617,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2298,f3669])).

fof(f2298,plain,
    ( ! [X26,X24,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X24),sK0)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X24))
        | k2_zfmisc_1(X25,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X24)),X26)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f855])).

fof(f855,plain,
    ( ! [X14,X15,X16] :
        ( ~ v1_xboole_0(X14)
        | k2_zfmisc_1(X15,k2_zfmisc_1(X14,X16)) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f841,f651])).

fof(f651,plain,
    ( ! [X10,X9] :
        ( ~ v1_xboole_0(X9)
        | k2_zfmisc_1(X10,X9) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f606,f341])).

fof(f8974,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1160
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8970,f3668,f1146,f249,f193,f179,f8972,f8703,f8684,f8641])).

fof(f8972,plain,
    ( spl15_1160
  <=> ! [X71] : k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X71) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1160])])).

fof(f8970,plain,
    ( ! [X71] :
        ( k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X71) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8969,f3669])).

fof(f8969,plain,
    ( ! [X71] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8616,f3669])).

fof(f8616,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2297,f3669])).

fof(f2297,plain,
    ( ! [X23,X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X22),sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X22))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X22)),X23) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f851])).

fof(f8968,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1158
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8964,f3668,f1146,f193,f179,f8966,f8703,f8684,f8641])).

fof(f8966,plain,
    ( spl15_1158
  <=> ! [X69,X70] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X69) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1158])])).

fof(f8964,plain,
    ( ! [X70,X69] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8963,f3669])).

fof(f8963,plain,
    ( ! [X70,X69] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8615,f3669])).

fof(f8615,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2296,f3669])).

fof(f2296,plain,
    ( ! [X21,X19,X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X19),sK0)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X19))
        | k2_zfmisc_1(X20,X21) = k4_waybel_0(sK0,k4_waybel_0(sK1,X19))
        | ~ v1_xboole_0(X20) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f850])).

fof(f850,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_xboole_0(X3)
      | k2_zfmisc_1(X2,X4) = X3
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f841,f131])).

fof(f8962,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1156
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8958,f3668,f1146,f249,f193,f179,f8960,f8703,f8684,f8641])).

fof(f8960,plain,
    ( spl15_1156
  <=> ! [X68] : sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1156])])).

fof(f8958,plain,
    ( ! [X68] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8957,f3669])).

fof(f8957,plain,
    ( ! [X68] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8614,f3669])).

fof(f8614,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2295,f3669])).

fof(f2295,plain,
    ( ! [X17,X18] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X17),sK0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X17))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X18,k4_waybel_0(sK0,k4_waybel_0(sK1,X17))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f718])).

fof(f718,plain,
    ( ! [X10,X11] :
        ( ~ v1_xboole_0(X10)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X11,X10))) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f602,f341])).

fof(f602,plain,(
    ! [X8,X7] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(k2_zfmisc_1(X8,X7))))
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f153,f130])).

fof(f8956,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1154
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8952,f3668,f1146,f249,f193,f179,f8954,f8703,f8684,f8641])).

fof(f8954,plain,
    ( spl15_1154
  <=> ! [X67] : k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1154])])).

fof(f8952,plain,
    ( ! [X67] :
        ( k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8951,f3669])).

fof(f8951,plain,
    ( ! [X67] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8613,f3669])).

fof(f8613,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2294,f3669])).

fof(f2294,plain,
    ( ! [X15,X16] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X15),sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X15))
        | k2_zfmisc_1(X16,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X15))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f694])).

fof(f694,plain,
    ( ! [X8,X7] :
        ( ~ v1_xboole_0(X8)
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(X8))) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f651,f379])).

fof(f8950,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1152
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8946,f3668,f1146,f249,f193,f179,f8948,f8703,f8684,f8641])).

fof(f8948,plain,
    ( spl15_1152
  <=> ! [X65,X66] : k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1152])])).

fof(f8946,plain,
    ( ! [X66,X65] :
        ( k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8945,f3669])).

fof(f8945,plain,
    ( ! [X66,X65] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8612,f3669])).

fof(f8612,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2293,f3669])).

fof(f2293,plain,
    ( ! [X14,X12,X13] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X12),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X12))
        | k2_zfmisc_1(X13,k2_zfmisc_1(X14,k4_waybel_0(sK0,k4_waybel_0(sK1,X12)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f692])).

fof(f692,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_xboole_0(X4)
        | k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f651,f606])).

fof(f8944,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1150
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8940,f3668,f1146,f193,f179,f8942,f8703,f8684,f8641])).

fof(f8942,plain,
    ( spl15_1150
  <=> ! [X63,X64] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1150])])).

fof(f8940,plain,
    ( ! [X64,X63] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8939,f3669])).

fof(f8939,plain,
    ( ! [X64,X63] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8611,f3669])).

fof(f8611,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2292,f3669])).

fof(f2292,plain,
    ( ! [X10,X11,X9] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X9),sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X9))
        | k2_zfmisc_1(X10,X11) = k4_waybel_0(sK0,k4_waybel_0(sK1,X9))
        | ~ v1_xboole_0(X11) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f652])).

fof(f652,plain,(
    ! [X12,X13,X11] :
      ( ~ v1_xboole_0(X12)
      | k2_zfmisc_1(X13,X11) = X12
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f606,f131])).

fof(f8938,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1148
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8934,f3668,f1146,f249,f193,f179,f8936,f8703,f8684,f8641])).

fof(f8936,plain,
    ( spl15_1148
  <=> ! [X62] : k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1148])])).

fof(f8934,plain,
    ( ! [X62] :
        ( k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8933,f3669])).

fof(f8933,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8610,f3669])).

fof(f8610,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2291,f3669])).

fof(f2291,plain,
    ( ! [X8,X7] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X7),sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X7))
        | k2_zfmisc_1(X8,k4_waybel_0(sK0,k4_waybel_0(sK1,X7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f651])).

fof(f8932,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1146
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8925,f3668,f1146,f249,f193,f179,f8930,f8703,f8684,f8641])).

fof(f8930,plain,
    ( spl15_1146
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1146])])).

fof(f8925,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8924,f3669])).

fof(f8924,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8609,f3669])).

fof(f8609,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2290,f3669])).

fof(f2290,plain,
    ( ! [X6] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X6),sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X6))
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X6)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f446])).

fof(f446,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(X1)))) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f436,f379])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK5(k1_zfmisc_1(X0)) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f379,f341])).

fof(f8923,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1144
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8919,f3668,f1146,f193,f179,f8921,f8703,f8684,f8641])).

fof(f8921,plain,
    ( spl15_1144
  <=> ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1144])])).

fof(f8919,plain,
    ( ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8918,f3669])).

fof(f8918,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8608,f3669])).

fof(f8608,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2289,f3669])).

fof(f2289,plain,
    ( ! [X4,X5] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X4),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X4))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,X4)) = sK5(k1_zfmisc_1(X5))
        | ~ v1_xboole_0(X5) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f437])).

fof(f437,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | sK5(k1_zfmisc_1(X1)) = X2
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f379,f131])).

fof(f8917,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1142
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8910,f3668,f1146,f249,f193,f179,f8915,f8703,f8684,f8641])).

fof(f8915,plain,
    ( spl15_1142
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1142])])).

fof(f8910,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8909,f3669])).

fof(f8909,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8607,f3669])).

fof(f8607,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2288,f3669])).

fof(f2288,plain,
    ( ! [X3] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X3))
        | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,X3)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f436])).

fof(f8908,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1140
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8901,f3668,f1146,f249,f193,f179,f8906,f8703,f8684,f8641])).

fof(f8906,plain,
    ( spl15_1140
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1140])])).

fof(f8901,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8900,f3669])).

fof(f8900,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8606,f3669])).

fof(f8606,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2287,f3669])).

fof(f2287,plain,
    ( ! [X2] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X2))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,X2)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f341])).

fof(f8899,plain,
    ( ~ spl15_1085
    | ~ spl15_1097
    | ~ spl15_1101
    | spl15_1138
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8895,f3668,f1146,f193,f179,f8897,f8703,f8684,f8641])).

fof(f8897,plain,
    ( spl15_1138
  <=> ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = X60
        | ~ v1_xboole_0(X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1138])])).

fof(f8895,plain,
    ( ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = X60
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8894,f3669])).

fof(f8894,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8605,f3669])).

fof(f8605,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2286,f3669])).

fof(f2286,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X0))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2133,f131])).

fof(f8893,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1136
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8889,f3668,f1146,f249,f193,f179,f8891,f8703,f8670,f8641])).

fof(f8670,plain,
    ( spl15_1093
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1093])])).

fof(f8891,plain,
    ( spl15_1136
  <=> ! [X59] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X59))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1136])])).

fof(f8889,plain,
    ( ! [X59] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X59))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8888,f3669])).

fof(f8888,plain,
    ( ! [X59] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8604,f3669])).

fof(f8604,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2285,f3669])).

fof(f2285,plain,
    ( ! [X35,X36] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X35),sK0)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X35))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X35)),X36))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f888])).

fof(f2131,plain,
    ( ! [X1] :
        ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK1,X1)))
        | ~ v12_waybel_0(k4_waybel_0(sK1,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2047,f378])).

fof(f8887,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1134
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8883,f3668,f1146,f249,f193,f179,f8885,f8703,f8670,f8641])).

fof(f8885,plain,
    ( spl15_1134
  <=> ! [X58] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))),X58) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1134])])).

fof(f8883,plain,
    ( ! [X58] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))),X58) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8882,f3669])).

fof(f8882,plain,
    ( ! [X58] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8603,f3669])).

fof(f8603,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2284,f3669])).

fof(f2284,plain,
    ( ! [X33,X34] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X33),sK0)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X33))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X33)))),X34) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f876])).

fof(f8881,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1132
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8877,f3668,f1146,f249,f193,f179,f8879,f8703,f8670,f8641])).

fof(f8879,plain,
    ( spl15_1132
  <=> ! [X56,X57] : k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))),X57) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1132])])).

fof(f8877,plain,
    ( ! [X57,X56] :
        ( k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))),X57) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8876,f3669])).

fof(f8876,plain,
    ( ! [X57,X56] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8602,f3669])).

fof(f8602,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2283,f3669])).

fof(f2283,plain,
    ( ! [X30,X31,X32] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X30),sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X30))
        | k2_zfmisc_1(k2_zfmisc_1(X31,k3_waybel_0(sK0,k4_waybel_0(sK1,X30))),X32) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f874])).

fof(f8875,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1130
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8871,f3668,f1146,f249,f193,f179,f8873,f8703,f8670,f8641])).

fof(f8873,plain,
    ( spl15_1130
  <=> ! [X55,X54] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X54),X55) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1130])])).

fof(f8871,plain,
    ( ! [X54,X55] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X54),X55) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8870,f3669])).

fof(f8870,plain,
    ( ! [X54,X55] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8601,f3669])).

fof(f8601,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2282,f3669])).

fof(f2282,plain,
    ( ! [X28,X29,X27] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X27),sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X27))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X27)),X28),X29) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f873])).

fof(f8869,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1128
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8865,f3668,f1146,f249,f193,f179,f8867,f8703,f8670,f8641])).

fof(f8867,plain,
    ( spl15_1128
  <=> ! [X53,X52] : k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X53)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1128])])).

fof(f8865,plain,
    ( ! [X52,X53] :
        ( k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X53)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8864,f3669])).

fof(f8864,plain,
    ( ! [X52,X53] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8600,f3669])).

fof(f8600,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2281,f3669])).

fof(f2281,plain,
    ( ! [X26,X24,X25] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X24),sK0)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X24))
        | k2_zfmisc_1(X25,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X24)),X26)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f855])).

fof(f8863,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1126
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8859,f3668,f1146,f249,f193,f179,f8861,f8703,f8670,f8641])).

fof(f8861,plain,
    ( spl15_1126
  <=> ! [X51] : k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X51) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1126])])).

fof(f8859,plain,
    ( ! [X51] :
        ( k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),X51) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8858,f3669])).

fof(f8858,plain,
    ( ! [X51] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8599,f3669])).

fof(f8599,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2280,f3669])).

fof(f2280,plain,
    ( ! [X23,X22] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X22),sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X22))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X22)),X23) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f851])).

fof(f8857,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1124
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8853,f3668,f1146,f193,f179,f8855,f8703,f8670,f8641])).

fof(f8855,plain,
    ( spl15_1124
  <=> ! [X49,X50] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1124])])).

fof(f8853,plain,
    ( ! [X50,X49] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8852,f3669])).

fof(f8852,plain,
    ( ! [X50,X49] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8598,f3669])).

fof(f8598,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2279,f3669])).

fof(f2279,plain,
    ( ! [X21,X19,X20] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X19),sK0)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X19))
        | k2_zfmisc_1(X20,X21) = k3_waybel_0(sK0,k4_waybel_0(sK1,X19))
        | ~ v1_xboole_0(X20) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f850])).

fof(f8851,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1122
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8847,f3668,f1146,f249,f193,f179,f8849,f8703,f8670,f8641])).

fof(f8849,plain,
    ( spl15_1122
  <=> ! [X48] : sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1122])])).

fof(f8847,plain,
    ( ! [X48] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8846,f3669])).

fof(f8846,plain,
    ( ! [X48] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8597,f3669])).

fof(f8597,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2278,f3669])).

fof(f2278,plain,
    ( ! [X17,X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X17),sK0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X17))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X18,k3_waybel_0(sK0,k4_waybel_0(sK1,X17))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f718])).

fof(f8845,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1120
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8841,f3668,f1146,f249,f193,f179,f8843,f8703,f8670,f8641])).

fof(f8843,plain,
    ( spl15_1120
  <=> ! [X47] : k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1120])])).

fof(f8841,plain,
    ( ! [X47] :
        ( k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8840,f3669])).

fof(f8840,plain,
    ( ! [X47] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8596,f3669])).

fof(f8596,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2277,f3669])).

fof(f2277,plain,
    ( ! [X15,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X15),sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X15))
        | k2_zfmisc_1(X16,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X15))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f694])).

fof(f8839,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1118
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8835,f3668,f1146,f249,f193,f179,f8837,f8703,f8670,f8641])).

fof(f8837,plain,
    ( spl15_1118
  <=> ! [X46,X45] : k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1118])])).

fof(f8835,plain,
    ( ! [X45,X46] :
        ( k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8834,f3669])).

fof(f8834,plain,
    ( ! [X45,X46] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8595,f3669])).

fof(f8595,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2276,f3669])).

fof(f2276,plain,
    ( ! [X14,X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X12),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X12))
        | k2_zfmisc_1(X13,k2_zfmisc_1(X14,k3_waybel_0(sK0,k4_waybel_0(sK1,X12)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f692])).

fof(f8833,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1116
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8829,f3668,f1146,f193,f179,f8831,f8703,f8670,f8641])).

fof(f8831,plain,
    ( spl15_1116
  <=> ! [X44,X43] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1116])])).

fof(f8829,plain,
    ( ! [X43,X44] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8828,f3669])).

fof(f8828,plain,
    ( ! [X43,X44] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8594,f3669])).

fof(f8594,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2275,f3669])).

fof(f2275,plain,
    ( ! [X10,X11,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X9),sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X9))
        | k2_zfmisc_1(X10,X11) = k3_waybel_0(sK0,k4_waybel_0(sK1,X9))
        | ~ v1_xboole_0(X11) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f652])).

fof(f8827,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1114
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8823,f3668,f1146,f249,f193,f179,f8825,f8703,f8670,f8641])).

fof(f8825,plain,
    ( spl15_1114
  <=> ! [X42] : k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1114])])).

fof(f8823,plain,
    ( ! [X42] :
        ( k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8822,f3669])).

fof(f8822,plain,
    ( ! [X42] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8593,f3669])).

fof(f8593,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2274,f3669])).

fof(f2274,plain,
    ( ! [X8,X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X7),sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X7))
        | k2_zfmisc_1(X8,k3_waybel_0(sK0,k4_waybel_0(sK1,X7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f651])).

fof(f8821,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1112
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8814,f3668,f1146,f249,f193,f179,f8819,f8703,f8670,f8641])).

fof(f8819,plain,
    ( spl15_1112
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1112])])).

fof(f8814,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8813,f3669])).

fof(f8813,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8592,f3669])).

fof(f8592,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2273,f3669])).

fof(f2273,plain,
    ( ! [X6] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X6),sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X6))
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X6)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f446])).

fof(f8812,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1110
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8808,f3668,f1146,f193,f179,f8810,f8703,f8670,f8641])).

fof(f8810,plain,
    ( spl15_1110
  <=> ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1110])])).

fof(f8808,plain,
    ( ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8807,f3669])).

fof(f8807,plain,
    ( ! [X41] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8591,f3669])).

fof(f8591,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2272,f3669])).

fof(f2272,plain,
    ( ! [X4,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X4),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X4))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,X4)) = sK5(k1_zfmisc_1(X5))
        | ~ v1_xboole_0(X5) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f437])).

fof(f8806,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1108
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8799,f3668,f1146,f249,f193,f179,f8804,f8703,f8670,f8641])).

fof(f8804,plain,
    ( spl15_1108
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1108])])).

fof(f8799,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8798,f3669])).

fof(f8798,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8590,f3669])).

fof(f8590,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2271,f3669])).

fof(f2271,plain,
    ( ! [X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X3))
        | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,X3)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f436])).

fof(f8797,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1106
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8790,f3668,f1146,f249,f193,f179,f8795,f8703,f8670,f8641])).

fof(f8795,plain,
    ( spl15_1106
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1106])])).

fof(f8790,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8789,f3669])).

fof(f8789,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8589,f3669])).

fof(f8589,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2270,f3669])).

fof(f2270,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X2))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,X2)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f341])).

fof(f8788,plain,
    ( ~ spl15_1085
    | ~ spl15_1093
    | ~ spl15_1101
    | spl15_1104
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8784,f3668,f1146,f193,f179,f8786,f8703,f8670,f8641])).

fof(f8786,plain,
    ( spl15_1104
  <=> ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = X40
        | ~ v1_xboole_0(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1104])])).

fof(f8784,plain,
    ( ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) = X40
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8783,f3669])).

fof(f8783,plain,
    ( ! [X40] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8588,f3669])).

fof(f8588,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
        | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2269,f3669])).

fof(f2269,plain,
    ( ! [X0,X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X0))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2131,f131])).

fof(f8714,plain,
    ( ~ spl15_1085
    | spl15_1102
    | ~ spl15_1097
    | ~ spl15_1101
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8707,f3668,f1146,f193,f179,f8703,f8684,f8712,f8641])).

fof(f8712,plain,
    ( spl15_1102
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1102])])).

fof(f8707,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8706,f3669])).

fof(f8706,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8553,f3669])).

fof(f8553,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2133,f3669])).

fof(f8705,plain,
    ( ~ spl15_1085
    | spl15_1098
    | ~ spl15_1093
    | ~ spl15_1101
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8692,f3668,f1146,f193,f179,f8703,f8670,f8697,f8641])).

fof(f8697,plain,
    ( spl15_1098
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1098])])).

fof(f8692,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8691,f3669])).

fof(f8691,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8552,f3669])).

fof(f8552,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2131,f3669])).

fof(f8686,plain,
    ( ~ spl15_1085
    | spl15_1094
    | ~ spl15_1097
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8673,f3668,f1146,f193,f179,f8684,f8678,f8641])).

fof(f8678,plain,
    ( spl15_1094
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1094])])).

fof(f8673,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8549,f3669])).

fof(f8549,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2048,f3669])).

fof(f8672,plain,
    ( ~ spl15_1085
    | spl15_1090
    | ~ spl15_1093
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8659,f3668,f1146,f193,f179,f8670,f8664,f8641])).

fof(f8664,plain,
    ( spl15_1090
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1090])])).

fof(f8659,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(forward_demodulation,[],[f8548,f3669])).

fof(f8548,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK10(u1_struct_0(sK0)))),k4_waybel_0(sK0,sK10(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2047,f3669])).

fof(f8658,plain,
    ( ~ spl15_1085
    | spl15_1088
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8547,f3668,f1146,f193,f8656,f8641])).

fof(f8547,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2046,f3669])).

fof(f8649,plain,
    ( ~ spl15_1085
    | spl15_1086
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8544,f3668,f1146,f193,f8647,f8641])).

fof(f8544,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_410 ),
    inference(superposition,[],[f2038,f3669])).

fof(f8636,plain,
    ( ~ spl15_1083
    | spl15_191
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f8542,f3668,f1329,f8634])).

fof(f1329,plain,
    ( spl15_191
  <=> ~ r1_tarski(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_191])])).

fof(f8542,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_191
    | ~ spl15_410 ),
    inference(backward_demodulation,[],[f3669,f1330])).

fof(f1330,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_191 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f8541,plain,
    ( spl15_410
    | ~ spl15_0
    | ~ spl15_4
    | spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f8540,f1396,f1146,f390,f193,f179,f3668])).

fof(f8540,plain,
    ( k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f8526,f391])).

fof(f8526,plain,
    ( k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3600,f368])).

fof(f368,plain,(
    ! [X0] :
      ( r1_tarski(sK10(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f149,f139])).

fof(f8539,plain,
    ( spl15_412
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f8524,f1396,f1146,f193,f179,f3675])).

fof(f3675,plain,
    ( spl15_412
  <=> k4_waybel_0(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_412])])).

fof(f8524,plain,
    ( k4_waybel_0(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3600,f353])).

fof(f353,plain,(
    ! [X4] : r1_tarski(sK5(k1_zfmisc_1(X4)),X4) ),
    inference(resolution,[],[f139,f130])).

fof(f8538,plain,
    ( spl15_404
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_380 ),
    inference(avatar_split_clause,[],[f8518,f3033,f1396,f1146,f193,f179,f3644])).

fof(f3644,plain,
    ( spl15_404
  <=> k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_404])])).

fof(f3033,plain,
    ( spl15_380
  <=> r1_tarski(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_380])])).

fof(f8518,plain,
    ( k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_380 ),
    inference(resolution,[],[f3600,f3034])).

fof(f3034,plain,
    ( r1_tarski(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | ~ spl15_380 ),
    inference(avatar_component_clause,[],[f3033])).

fof(f8537,plain,
    ( spl15_398
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_284 ),
    inference(avatar_split_clause,[],[f8513,f1914,f1396,f1146,f193,f179,f3622])).

fof(f3622,plain,
    ( spl15_398
  <=> k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_398])])).

fof(f1914,plain,
    ( spl15_284
  <=> r1_tarski(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_284])])).

fof(f8513,plain,
    ( k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_284 ),
    inference(resolution,[],[f3600,f1915])).

fof(f1915,plain,
    ( r1_tarski(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | ~ spl15_284 ),
    inference(avatar_component_clause,[],[f1914])).

fof(f8535,plain,
    ( spl15_1072
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_980 ),
    inference(avatar_split_clause,[],[f8509,f7628,f1396,f1146,f193,f179,f8063])).

fof(f8063,plain,
    ( spl15_1072
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1072])])).

fof(f7628,plain,
    ( spl15_980
  <=> r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_980])])).

fof(f8509,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_980 ),
    inference(resolution,[],[f3600,f7629])).

fof(f7629,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK0))
    | ~ spl15_980 ),
    inference(avatar_component_clause,[],[f7628])).

fof(f8534,plain,
    ( spl15_972
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_800 ),
    inference(avatar_split_clause,[],[f8508,f6399,f1396,f1146,f193,f179,f7385])).

fof(f7385,plain,
    ( spl15_972
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_972])])).

fof(f6399,plain,
    ( spl15_800
  <=> r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_800])])).

fof(f8508,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_800 ),
    inference(resolution,[],[f3600,f6400])).

fof(f6400,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ spl15_800 ),
    inference(avatar_component_clause,[],[f6399])).

fof(f8533,plain,
    ( spl15_662
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_502 ),
    inference(avatar_split_clause,[],[f8507,f4522,f1396,f1146,f193,f179,f5185])).

fof(f4522,plain,
    ( spl15_502
  <=> r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_502])])).

fof(f8507,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_502 ),
    inference(resolution,[],[f3600,f4523])).

fof(f4523,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK0))
    | ~ spl15_502 ),
    inference(avatar_component_clause,[],[f4522])).

fof(f8532,plain,
    ( spl15_780
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_692 ),
    inference(avatar_split_clause,[],[f8506,f5716,f1396,f1146,f193,f179,f6241])).

fof(f6241,plain,
    ( spl15_780
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_780])])).

fof(f5716,plain,
    ( spl15_692
  <=> r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_692])])).

fof(f8506,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_692 ),
    inference(resolution,[],[f3600,f5717])).

fof(f5717,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK0))
    | ~ spl15_692 ),
    inference(avatar_component_clause,[],[f5716])).

fof(f8531,plain,
    ( spl15_684
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_674 ),
    inference(avatar_split_clause,[],[f8505,f5341,f1396,f1146,f193,f179,f5601])).

fof(f5601,plain,
    ( spl15_684
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_684])])).

fof(f5341,plain,
    ( spl15_674
  <=> r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_674])])).

fof(f8505,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_674 ),
    inference(resolution,[],[f3600,f5342])).

fof(f5342,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ spl15_674 ),
    inference(avatar_component_clause,[],[f5341])).

fof(f8530,plain,
    ( spl15_660
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_478 ),
    inference(avatar_split_clause,[],[f8504,f4141,f1396,f1146,f193,f179,f5166])).

fof(f4141,plain,
    ( spl15_478
  <=> r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_478])])).

fof(f8504,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_478 ),
    inference(resolution,[],[f3600,f4142])).

fof(f4142,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ spl15_478 ),
    inference(avatar_component_clause,[],[f4141])).

fof(f8391,plain,
    ( spl15_404
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f8382,f2741,f1396,f1146,f193,f179,f3644])).

fof(f8382,plain,
    ( k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f3584])).

fof(f8091,plain,
    ( ~ spl15_1079
    | spl15_1080
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_978 ),
    inference(avatar_split_clause,[],[f8052,f7619,f1146,f193,f8089,f8083])).

fof(f8083,plain,
    ( spl15_1079
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1079])])).

fof(f8089,plain,
    ( spl15_1080
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1080])])).

fof(f8052,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_978 ),
    inference(resolution,[],[f7620,f1202])).

fof(f8078,plain,
    ( ~ spl15_1075
    | spl15_1076
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_978 ),
    inference(avatar_split_clause,[],[f8051,f7619,f1146,f193,f8076,f8070])).

fof(f8070,plain,
    ( spl15_1075
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1075])])).

fof(f8076,plain,
    ( spl15_1076
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1076])])).

fof(f8051,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_978 ),
    inference(resolution,[],[f7620,f1203])).

fof(f8065,plain,
    ( spl15_1072
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_978 ),
    inference(avatar_split_clause,[],[f8050,f7619,f1396,f1146,f193,f179,f8063])).

fof(f8050,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_978 ),
    inference(resolution,[],[f7620,f3584])).

fof(f8037,plain,
    ( spl15_1070
    | ~ spl15_976 ),
    inference(avatar_split_clause,[],[f8008,f7610,f8035])).

fof(f8035,plain,
    ( spl15_1070
  <=> r1_tarski(sK14(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1070])])).

fof(f8008,plain,
    ( r1_tarski(sK14(sK0),u1_struct_0(sK0))
    | ~ spl15_976 ),
    inference(resolution,[],[f7611,f139])).

fof(f8030,plain,
    ( ~ spl15_1069
    | spl15_974
    | ~ spl15_0
    | ~ spl15_976 ),
    inference(avatar_split_clause,[],[f8023,f7610,f179,f7603,f8028])).

fof(f8028,plain,
    ( spl15_1069
  <=> ~ v13_waybel_0(sK14(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1069])])).

fof(f7603,plain,
    ( spl15_974
  <=> r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_974])])).

fof(f8023,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ v13_waybel_0(sK14(sK0),sK0)
    | ~ spl15_0
    | ~ spl15_976 ),
    inference(subsumption_resolution,[],[f8006,f180])).

fof(f8006,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ v13_waybel_0(sK14(sK0),sK0)
    | ~ spl15_976 ),
    inference(resolution,[],[f7611,f127])).

fof(f8022,plain,
    ( ~ spl15_1065
    | spl15_1066
    | ~ spl15_0
    | ~ spl15_976 ),
    inference(avatar_split_clause,[],[f8009,f7610,f179,f8020,f8014])).

fof(f8014,plain,
    ( spl15_1065
  <=> ~ v12_waybel_0(sK14(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1065])])).

fof(f8020,plain,
    ( spl15_1066
  <=> r1_tarski(k3_waybel_0(sK0,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1066])])).

fof(f8009,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ v12_waybel_0(sK14(sK0),sK0)
    | ~ spl15_0
    | ~ spl15_976 ),
    inference(subsumption_resolution,[],[f8005,f180])).

fof(f8005,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ v12_waybel_0(sK14(sK0),sK0)
    | ~ spl15_976 ),
    inference(resolution,[],[f7611,f129])).

fof(f7999,plain,
    ( ~ spl15_36
    | spl15_57
    | spl15_977 ),
    inference(avatar_contradiction_clause,[],[f7998])).

fof(f7998,plain,
    ( $false
    | ~ spl15_36
    | ~ spl15_57
    | ~ spl15_977 ),
    inference(subsumption_resolution,[],[f7997,f407])).

fof(f7997,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_36
    | ~ spl15_977 ),
    inference(subsumption_resolution,[],[f7995,f311])).

fof(f7995,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_977 ),
    inference(resolution,[],[f7614,f166])).

fof(f7614,plain,
    ( ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_977 ),
    inference(avatar_component_clause,[],[f7613])).

fof(f7613,plain,
    ( spl15_977
  <=> ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_977])])).

fof(f7994,plain,
    ( ~ spl15_975
    | ~ spl15_977
    | ~ spl15_4
    | ~ spl15_150
    | spl15_329
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7993,f3653,f2717,f1146,f193,f7613,f7606])).

fof(f7606,plain,
    ( spl15_975
  <=> ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_975])])).

fof(f2717,plain,
    ( spl15_329
  <=> ~ v13_waybel_0(sK14(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_329])])).

fof(f3653,plain,
    ( spl15_406
  <=> k4_waybel_0(sK0,sK14(sK0)) = k4_waybel_0(sK1,sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_406])])).

fof(f7993,plain,
    ( ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_329
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7992,f1147])).

fof(f7992,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_329
    | ~ spl15_406 ),
    inference(subsumption_resolution,[],[f7991,f2718])).

fof(f2718,plain,
    ( ~ v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_329 ),
    inference(avatar_component_clause,[],[f2717])).

fof(f7991,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_406 ),
    inference(subsumption_resolution,[],[f7601,f194])).

fof(f7601,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_406 ),
    inference(superposition,[],[f126,f3654])).

fof(f3654,plain,
    ( k4_waybel_0(sK0,sK14(sK0)) = k4_waybel_0(sK1,sK14(sK0))
    | ~ spl15_406 ),
    inference(avatar_component_clause,[],[f3653])).

fof(f7990,plain,
    ( spl15_978
    | ~ spl15_977
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7989,f3653,f1146,f193,f7613,f7619])).

fof(f7989,plain,
    ( ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7988,f1147])).

fof(f7988,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7987,f1147])).

fof(f7987,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_406 ),
    inference(subsumption_resolution,[],[f7600,f194])).

fof(f7600,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_406 ),
    inference(superposition,[],[f140,f3654])).

fof(f7986,plain,
    ( spl15_980
    | ~ spl15_977
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7985,f3653,f1146,f193,f7613,f7628])).

fof(f7985,plain,
    ( ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7984,f1147])).

fof(f7984,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7983,f1147])).

fof(f7983,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_406 ),
    inference(subsumption_resolution,[],[f7599,f194])).

fof(f7599,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_406 ),
    inference(superposition,[],[f2026,f3654])).

fof(f7976,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1062
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7972,f3653,f1146,f249,f193,f179,f7974,f7675,f7656,f7613])).

fof(f7656,plain,
    ( spl15_989
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_989])])).

fof(f7675,plain,
    ( spl15_993
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_993])])).

fof(f7974,plain,
    ( spl15_1062
  <=> ! [X79] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X79))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1062])])).

fof(f7972,plain,
    ( ! [X79] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X79))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7971,f3654])).

fof(f7971,plain,
    ( ! [X79] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7595,f3654])).

fof(f7595,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2302,f3654])).

fof(f7970,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1060
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7966,f3653,f1146,f249,f193,f179,f7968,f7675,f7656,f7613])).

fof(f7968,plain,
    ( spl15_1060
  <=> ! [X78] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))),X78) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1060])])).

fof(f7966,plain,
    ( ! [X78] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))),X78) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7965,f3654])).

fof(f7965,plain,
    ( ! [X78] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7594,f3654])).

fof(f7594,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2301,f3654])).

fof(f7964,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1058
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7960,f3653,f1146,f249,f193,f179,f7962,f7675,f7656,f7613])).

fof(f7962,plain,
    ( spl15_1058
  <=> ! [X77,X76] : k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))),X77) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1058])])).

fof(f7960,plain,
    ( ! [X76,X77] :
        ( k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))),X77) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7959,f3654])).

fof(f7959,plain,
    ( ! [X76,X77] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7593,f3654])).

fof(f7593,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2300,f3654])).

fof(f7958,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1056
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7954,f3653,f1146,f249,f193,f179,f7956,f7675,f7656,f7613])).

fof(f7956,plain,
    ( spl15_1056
  <=> ! [X75,X74] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X74),X75) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1056])])).

fof(f7954,plain,
    ( ! [X74,X75] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X74),X75) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7953,f3654])).

fof(f7953,plain,
    ( ! [X74,X75] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7592,f3654])).

fof(f7592,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2299,f3654])).

fof(f7952,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1054
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7948,f3653,f1146,f249,f193,f179,f7950,f7675,f7656,f7613])).

fof(f7950,plain,
    ( spl15_1054
  <=> ! [X73,X72] : k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X73)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1054])])).

fof(f7948,plain,
    ( ! [X72,X73] :
        ( k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X73)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7947,f3654])).

fof(f7947,plain,
    ( ! [X72,X73] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7591,f3654])).

fof(f7591,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2298,f3654])).

fof(f7946,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1052
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7942,f3653,f1146,f249,f193,f179,f7944,f7675,f7656,f7613])).

fof(f7944,plain,
    ( spl15_1052
  <=> ! [X71] : k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X71) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1052])])).

fof(f7942,plain,
    ( ! [X71] :
        ( k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X71) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7941,f3654])).

fof(f7941,plain,
    ( ! [X71] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7590,f3654])).

fof(f7590,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2297,f3654])).

fof(f7940,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1050
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7936,f3653,f1146,f193,f179,f7938,f7675,f7656,f7613])).

fof(f7938,plain,
    ( spl15_1050
  <=> ! [X69,X70] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(X69) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1050])])).

fof(f7936,plain,
    ( ! [X70,X69] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7935,f3654])).

fof(f7935,plain,
    ( ! [X70,X69] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7589,f3654])).

fof(f7589,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2296,f3654])).

fof(f7934,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1048
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7930,f3653,f1146,f249,f193,f179,f7932,f7675,f7656,f7613])).

fof(f7932,plain,
    ( spl15_1048
  <=> ! [X68] : sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1048])])).

fof(f7930,plain,
    ( ! [X68] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7929,f3654])).

fof(f7929,plain,
    ( ! [X68] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7588,f3654])).

fof(f7588,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2295,f3654])).

fof(f7928,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1046
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7924,f3653,f1146,f249,f193,f179,f7926,f7675,f7656,f7613])).

fof(f7926,plain,
    ( spl15_1046
  <=> ! [X67] : k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1046])])).

fof(f7924,plain,
    ( ! [X67] :
        ( k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7923,f3654])).

fof(f7923,plain,
    ( ! [X67] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7587,f3654])).

fof(f7587,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2294,f3654])).

fof(f7922,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1044
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7918,f3653,f1146,f249,f193,f179,f7920,f7675,f7656,f7613])).

fof(f7920,plain,
    ( spl15_1044
  <=> ! [X65,X66] : k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1044])])).

fof(f7918,plain,
    ( ! [X66,X65] :
        ( k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7917,f3654])).

fof(f7917,plain,
    ( ! [X66,X65] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7586,f3654])).

fof(f7586,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2293,f3654])).

fof(f7916,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1042
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7912,f3653,f1146,f193,f179,f7914,f7675,f7656,f7613])).

fof(f7914,plain,
    ( spl15_1042
  <=> ! [X63,X64] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1042])])).

fof(f7912,plain,
    ( ! [X64,X63] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7911,f3654])).

fof(f7911,plain,
    ( ! [X64,X63] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7585,f3654])).

fof(f7585,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2292,f3654])).

fof(f7910,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1040
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7906,f3653,f1146,f249,f193,f179,f7908,f7675,f7656,f7613])).

fof(f7908,plain,
    ( spl15_1040
  <=> ! [X62] : k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1040])])).

fof(f7906,plain,
    ( ! [X62] :
        ( k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7905,f3654])).

fof(f7905,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7584,f3654])).

fof(f7584,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2291,f3654])).

fof(f7904,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1038
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7897,f3653,f1146,f249,f193,f179,f7902,f7675,f7656,f7613])).

fof(f7902,plain,
    ( spl15_1038
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1038])])).

fof(f7897,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7896,f3654])).

fof(f7896,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7583,f3654])).

fof(f7583,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2290,f3654])).

fof(f7895,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1036
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7891,f3653,f1146,f193,f179,f7893,f7675,f7656,f7613])).

fof(f7893,plain,
    ( spl15_1036
  <=> ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1036])])).

fof(f7891,plain,
    ( ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7890,f3654])).

fof(f7890,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7582,f3654])).

fof(f7582,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2289,f3654])).

fof(f7889,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1034
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7882,f3653,f1146,f249,f193,f179,f7887,f7675,f7656,f7613])).

fof(f7887,plain,
    ( spl15_1034
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1034])])).

fof(f7882,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7881,f3654])).

fof(f7881,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7581,f3654])).

fof(f7581,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2288,f3654])).

fof(f7880,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1032
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7873,f3653,f1146,f249,f193,f179,f7878,f7675,f7656,f7613])).

fof(f7878,plain,
    ( spl15_1032
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1032])])).

fof(f7873,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7872,f3654])).

fof(f7872,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7580,f3654])).

fof(f7580,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2287,f3654])).

fof(f7871,plain,
    ( ~ spl15_977
    | ~ spl15_989
    | ~ spl15_993
    | spl15_1030
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7867,f3653,f1146,f193,f179,f7869,f7675,f7656,f7613])).

fof(f7869,plain,
    ( spl15_1030
  <=> ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = X60
        | ~ v1_xboole_0(X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1030])])).

fof(f7867,plain,
    ( ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = X60
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7866,f3654])).

fof(f7866,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7579,f3654])).

fof(f7579,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2286,f3654])).

fof(f7865,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1028
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7861,f3653,f1146,f249,f193,f179,f7863,f7675,f7642,f7613])).

fof(f7642,plain,
    ( spl15_985
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_985])])).

fof(f7863,plain,
    ( spl15_1028
  <=> ! [X59] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X59))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1028])])).

fof(f7861,plain,
    ( ! [X59] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X59))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7860,f3654])).

fof(f7860,plain,
    ( ! [X59] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7578,f3654])).

fof(f7578,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2285,f3654])).

fof(f7859,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1026
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7855,f3653,f1146,f249,f193,f179,f7857,f7675,f7642,f7613])).

fof(f7857,plain,
    ( spl15_1026
  <=> ! [X58] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))),X58) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1026])])).

fof(f7855,plain,
    ( ! [X58] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))),X58) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7854,f3654])).

fof(f7854,plain,
    ( ! [X58] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7577,f3654])).

fof(f7577,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2284,f3654])).

fof(f7853,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1024
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7849,f3653,f1146,f249,f193,f179,f7851,f7675,f7642,f7613])).

fof(f7851,plain,
    ( spl15_1024
  <=> ! [X56,X57] : k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))),X57) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1024])])).

fof(f7849,plain,
    ( ! [X57,X56] :
        ( k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))),X57) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7848,f3654])).

fof(f7848,plain,
    ( ! [X57,X56] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7576,f3654])).

fof(f7576,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2283,f3654])).

fof(f7847,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1022
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7843,f3653,f1146,f249,f193,f179,f7845,f7675,f7642,f7613])).

fof(f7845,plain,
    ( spl15_1022
  <=> ! [X55,X54] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X54),X55) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1022])])).

fof(f7843,plain,
    ( ! [X54,X55] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X54),X55) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7842,f3654])).

fof(f7842,plain,
    ( ! [X54,X55] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7575,f3654])).

fof(f7575,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2282,f3654])).

fof(f7841,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1020
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7837,f3653,f1146,f249,f193,f179,f7839,f7675,f7642,f7613])).

fof(f7839,plain,
    ( spl15_1020
  <=> ! [X53,X52] : k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X53)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1020])])).

fof(f7837,plain,
    ( ! [X52,X53] :
        ( k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X53)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7836,f3654])).

fof(f7836,plain,
    ( ! [X52,X53] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7574,f3654])).

fof(f7574,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2281,f3654])).

fof(f7835,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1018
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7831,f3653,f1146,f249,f193,f179,f7833,f7675,f7642,f7613])).

fof(f7833,plain,
    ( spl15_1018
  <=> ! [X51] : k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X51) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1018])])).

fof(f7831,plain,
    ( ! [X51] :
        ( k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),X51) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7830,f3654])).

fof(f7830,plain,
    ( ! [X51] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7573,f3654])).

fof(f7573,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2280,f3654])).

fof(f7829,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1016
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7825,f3653,f1146,f193,f179,f7827,f7675,f7642,f7613])).

fof(f7827,plain,
    ( spl15_1016
  <=> ! [X49,X50] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1016])])).

fof(f7825,plain,
    ( ! [X50,X49] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7824,f3654])).

fof(f7824,plain,
    ( ! [X50,X49] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7572,f3654])).

fof(f7572,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2279,f3654])).

fof(f7823,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1014
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7819,f3653,f1146,f249,f193,f179,f7821,f7675,f7642,f7613])).

fof(f7821,plain,
    ( spl15_1014
  <=> ! [X48] : sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1014])])).

fof(f7819,plain,
    ( ! [X48] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7818,f3654])).

fof(f7818,plain,
    ( ! [X48] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7571,f3654])).

fof(f7571,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2278,f3654])).

fof(f7817,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1012
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7813,f3653,f1146,f249,f193,f179,f7815,f7675,f7642,f7613])).

fof(f7815,plain,
    ( spl15_1012
  <=> ! [X47] : k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1012])])).

fof(f7813,plain,
    ( ! [X47] :
        ( k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7812,f3654])).

fof(f7812,plain,
    ( ! [X47] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7570,f3654])).

fof(f7570,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2277,f3654])).

fof(f7811,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1010
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7807,f3653,f1146,f249,f193,f179,f7809,f7675,f7642,f7613])).

fof(f7809,plain,
    ( spl15_1010
  <=> ! [X46,X45] : k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1010])])).

fof(f7807,plain,
    ( ! [X45,X46] :
        ( k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7806,f3654])).

fof(f7806,plain,
    ( ! [X45,X46] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7569,f3654])).

fof(f7569,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2276,f3654])).

fof(f7805,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1008
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7801,f3653,f1146,f193,f179,f7803,f7675,f7642,f7613])).

fof(f7803,plain,
    ( spl15_1008
  <=> ! [X44,X43] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1008])])).

fof(f7801,plain,
    ( ! [X43,X44] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7800,f3654])).

fof(f7800,plain,
    ( ! [X43,X44] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7568,f3654])).

fof(f7568,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2275,f3654])).

fof(f7799,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1006
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7795,f3653,f1146,f249,f193,f179,f7797,f7675,f7642,f7613])).

fof(f7797,plain,
    ( spl15_1006
  <=> ! [X42] : k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1006])])).

fof(f7795,plain,
    ( ! [X42] :
        ( k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7794,f3654])).

fof(f7794,plain,
    ( ! [X42] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7567,f3654])).

fof(f7567,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2274,f3654])).

fof(f7793,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1004
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7786,f3653,f1146,f249,f193,f179,f7791,f7675,f7642,f7613])).

fof(f7791,plain,
    ( spl15_1004
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1004])])).

fof(f7786,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7785,f3654])).

fof(f7785,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7566,f3654])).

fof(f7566,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2273,f3654])).

fof(f7784,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1002
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7780,f3653,f1146,f193,f179,f7782,f7675,f7642,f7613])).

fof(f7782,plain,
    ( spl15_1002
  <=> ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1002])])).

fof(f7780,plain,
    ( ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7779,f3654])).

fof(f7779,plain,
    ( ! [X41] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7565,f3654])).

fof(f7565,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2272,f3654])).

fof(f7778,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_1000
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7771,f3653,f1146,f249,f193,f179,f7776,f7675,f7642,f7613])).

fof(f7776,plain,
    ( spl15_1000
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1000])])).

fof(f7771,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7770,f3654])).

fof(f7770,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7564,f3654])).

fof(f7564,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2271,f3654])).

fof(f7769,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_998
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7762,f3653,f1146,f249,f193,f179,f7767,f7675,f7642,f7613])).

fof(f7767,plain,
    ( spl15_998
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_998])])).

fof(f7762,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7761,f3654])).

fof(f7761,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7563,f3654])).

fof(f7563,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2270,f3654])).

fof(f7760,plain,
    ( ~ spl15_977
    | ~ spl15_985
    | ~ spl15_993
    | spl15_996
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7756,f3653,f1146,f193,f179,f7758,f7675,f7642,f7613])).

fof(f7758,plain,
    ( spl15_996
  <=> ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = X40
        | ~ v1_xboole_0(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_996])])).

fof(f7756,plain,
    ( ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))) = X40
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7755,f3654])).

fof(f7755,plain,
    ( ! [X40] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7562,f3654])).

fof(f7562,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
        | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK0))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2269,f3654])).

fof(f7686,plain,
    ( ~ spl15_977
    | spl15_994
    | ~ spl15_989
    | ~ spl15_993
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7679,f3653,f1146,f193,f179,f7675,f7656,f7684,f7613])).

fof(f7684,plain,
    ( spl15_994
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_994])])).

fof(f7679,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7678,f3654])).

fof(f7678,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7527,f3654])).

fof(f7527,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2133,f3654])).

fof(f7677,plain,
    ( ~ spl15_977
    | spl15_990
    | ~ spl15_985
    | ~ spl15_993
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7664,f3653,f1146,f193,f179,f7675,f7642,f7669,f7613])).

fof(f7669,plain,
    ( spl15_990
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_990])])).

fof(f7664,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7663,f3654])).

fof(f7663,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7526,f3654])).

fof(f7526,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK0)),sK0)
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2131,f3654])).

fof(f7658,plain,
    ( ~ spl15_977
    | spl15_986
    | ~ spl15_989
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7645,f3653,f1146,f193,f179,f7656,f7650,f7613])).

fof(f7650,plain,
    ( spl15_986
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_986])])).

fof(f7645,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7523,f3654])).

fof(f7523,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2048,f3654])).

fof(f7644,plain,
    ( ~ spl15_977
    | spl15_982
    | ~ spl15_985
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7631,f3653,f1146,f193,f179,f7642,f7636,f7613])).

fof(f7636,plain,
    ( spl15_982
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_982])])).

fof(f7631,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK0)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(forward_demodulation,[],[f7522,f3654])).

fof(f7522,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK0))),k4_waybel_0(sK0,sK14(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2047,f3654])).

fof(f7630,plain,
    ( ~ spl15_977
    | spl15_980
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7521,f3653,f1146,f193,f7628,f7613])).

fof(f7521,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2046,f3654])).

fof(f7621,plain,
    ( ~ spl15_977
    | spl15_978
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7518,f3653,f1146,f193,f7619,f7613])).

fof(f7518,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK14(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_406 ),
    inference(superposition,[],[f2038,f3654])).

fof(f7608,plain,
    ( ~ spl15_975
    | spl15_331
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f7516,f3653,f2720,f7606])).

fof(f2720,plain,
    ( spl15_331
  <=> ~ r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_331])])).

fof(f7516,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK14(sK0)),sK14(sK0))
    | ~ spl15_331
    | ~ spl15_406 ),
    inference(backward_demodulation,[],[f3654,f2721])).

fof(f2721,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ spl15_331 ),
    inference(avatar_component_clause,[],[f2720])).

fof(f7387,plain,
    ( spl15_972
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_790 ),
    inference(avatar_split_clause,[],[f7372,f6361,f1396,f1146,f193,f179,f7385])).

fof(f7372,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_790 ),
    inference(resolution,[],[f6362,f3584])).

fof(f7198,plain,
    ( spl15_362
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f7196,f2732,f2930])).

fof(f2930,plain,
    ( spl15_362
  <=> r1_tarski(sK14(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_362])])).

fof(f7196,plain,
    ( r1_tarski(sK14(sK1),u1_struct_0(sK0))
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f139])).

fof(f7197,plain,
    ( spl15_402
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f7188,f2732,f1396,f1146,f193,f179,f3637])).

fof(f3637,plain,
    ( spl15_402
  <=> k4_waybel_0(sK0,sK14(sK1)) = k4_waybel_0(sK1,sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_402])])).

fof(f7188,plain,
    ( k4_waybel_0(sK0,sK14(sK1)) = k4_waybel_0(sK1,sK14(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f3584])).

fof(f7187,plain,
    ( ~ spl15_971
    | ~ spl15_150
    | spl15_969 ),
    inference(avatar_split_clause,[],[f7180,f7151,f1146,f7185])).

fof(f7185,plain,
    ( spl15_971
  <=> u1_struct_0(sK0) != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_971])])).

fof(f7151,plain,
    ( spl15_969
  <=> u1_struct_0(sK1) != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_969])])).

fof(f7180,plain,
    ( u1_struct_0(sK0) != sK7
    | ~ spl15_150
    | ~ spl15_969 ),
    inference(superposition,[],[f7152,f1147])).

fof(f7152,plain,
    ( u1_struct_0(sK1) != sK7
    | ~ spl15_969 ),
    inference(avatar_component_clause,[],[f7151])).

fof(f7171,plain,
    ( ~ spl15_53
    | spl15_55
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f7170,f1146,f397,f390])).

fof(f397,plain,
    ( spl15_55
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_55])])).

fof(f7170,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_55
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f398,f1147])).

fof(f398,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_55 ),
    inference(avatar_component_clause,[],[f397])).

fof(f7169,plain,
    ( ~ spl15_209
    | spl15_141
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f7168,f1396,f1101,f1423])).

fof(f1423,plain,
    ( spl15_209
  <=> ~ v1_xboole_0(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_209])])).

fof(f1101,plain,
    ( spl15_141
  <=> ~ v1_xboole_0(u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_141])])).

fof(f7168,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_141
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1102,f1397])).

fof(f1102,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_141 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f7167,plain,
    ( ~ spl15_157
    | spl15_143
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f7166,f1146,f1110,f1184])).

fof(f1110,plain,
    ( spl15_143
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_143])])).

fof(f7166,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_143
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1111,f1147])).

fof(f1111,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_143 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f7165,plain,
    ( ~ spl15_429
    | spl15_199
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f7164,f3615,f1360,f3733])).

fof(f3733,plain,
    ( spl15_429
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_429])])).

fof(f1360,plain,
    ( spl15_199
  <=> ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_199])])).

fof(f3615,plain,
    ( spl15_396
  <=> k4_waybel_0(sK0,sK4(sK1)) = k4_waybel_0(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_396])])).

fof(f7164,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_199
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f1361,f3616])).

fof(f3616,plain,
    ( k4_waybel_0(sK0,sK4(sK1)) = k4_waybel_0(sK1,sK4(sK1))
    | ~ spl15_396 ),
    inference(avatar_component_clause,[],[f3615])).

fof(f1361,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK1)))
    | ~ spl15_199 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f7163,plain,
    ( ~ spl15_15
    | ~ spl15_0
    | ~ spl15_6
    | spl15_489 ),
    inference(avatar_split_clause,[],[f7162,f4350,f200,f179,f224])).

fof(f224,plain,
    ( spl15_15
  <=> ~ v13_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f4350,plain,
    ( spl15_489
  <=> ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_489])])).

fof(f7162,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | ~ spl15_0
    | ~ spl15_6
    | ~ spl15_489 ),
    inference(subsumption_resolution,[],[f7161,f4351])).

fof(f4351,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ spl15_489 ),
    inference(avatar_component_clause,[],[f4350])).

fof(f7161,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ v13_waybel_0(sK3,sK0)
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f723,f180])).

fof(f723,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ v13_waybel_0(sK3,sK0)
    | ~ spl15_6 ),
    inference(resolution,[],[f127,f201])).

fof(f7160,plain,
    ( ~ spl15_15
    | ~ spl15_0
    | ~ spl15_46
    | spl15_489 ),
    inference(avatar_split_clause,[],[f7159,f4350,f358,f179,f224])).

fof(f358,plain,
    ( spl15_46
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f7159,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | ~ spl15_0
    | ~ spl15_46
    | ~ spl15_489 ),
    inference(subsumption_resolution,[],[f7158,f359])).

fof(f359,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl15_46 ),
    inference(avatar_component_clause,[],[f358])).

fof(f7158,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_489 ),
    inference(subsumption_resolution,[],[f4353,f180])).

fof(f4353,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v13_waybel_0(sK3,sK0)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl15_489 ),
    inference(resolution,[],[f4351,f728])).

fof(f728,plain,(
    ! [X4,X3] :
      ( r1_tarski(k4_waybel_0(X3,X4),X4)
      | ~ l1_orders_2(X3)
      | ~ v13_waybel_0(X4,X3)
      | ~ r1_tarski(X4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f127,f138])).

fof(f7157,plain,
    ( ~ spl15_13
    | spl15_120
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f956,f200,f179,f962,f217])).

fof(f217,plain,
    ( spl15_13
  <=> ~ v12_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f956,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ v12_waybel_0(sK3,sK0)
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f947,f180])).

fof(f947,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ v12_waybel_0(sK3,sK0)
    | ~ spl15_6 ),
    inference(resolution,[],[f129,f201])).

fof(f7156,plain,
    ( spl15_968
    | ~ spl15_20
    | ~ spl15_38
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f7149,f430,f317,f249,f7154])).

fof(f7154,plain,
    ( spl15_968
  <=> u1_struct_0(sK1) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_968])])).

fof(f317,plain,
    ( spl15_38
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f430,plain,
    ( spl15_62
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).

fof(f7149,plain,
    ( u1_struct_0(sK1) = sK7
    | ~ spl15_20
    | ~ spl15_38
    | ~ spl15_62 ),
    inference(subsumption_resolution,[],[f7130,f318])).

fof(f318,plain,
    ( l1_struct_0(sK1)
    | ~ spl15_38 ),
    inference(avatar_component_clause,[],[f317])).

fof(f7130,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = sK7
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(resolution,[],[f431,f369])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | u1_struct_0(X0) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f165,f341])).

fof(f165,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',fc1_struct_0)).

fof(f431,plain,
    ( v2_struct_0(sK1)
    | ~ spl15_62 ),
    inference(avatar_component_clause,[],[f430])).

fof(f7148,plain,
    ( spl15_966
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f7141,f430,f249,f193,f7146])).

fof(f7146,plain,
    ( spl15_966
  <=> sK4(sK1) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_966])])).

fof(f7141,plain,
    ( sK4(sK1) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(subsumption_resolution,[],[f7129,f194])).

fof(f7129,plain,
    ( ~ l1_orders_2(sK1)
    | sK4(sK1) = sK7
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(resolution,[],[f431,f460])).

fof(f460,plain,
    ( ! [X1] :
        ( ~ v2_struct_0(X1)
        | ~ l1_orders_2(X1)
        | sK4(X1) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f458,f341])).

fof(f458,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f457,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_l1_orders_2)).

fof(f457,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(resolution,[],[f375,f165])).

fof(f375,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v1_xboole_0(sK4(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f148,f123])).

fof(f7140,plain,
    ( spl15_964
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f7133,f430,f249,f193,f7138])).

fof(f7138,plain,
    ( spl15_964
  <=> u1_orders_2(sK1) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_964])])).

fof(f7133,plain,
    ( u1_orders_2(sK1) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(subsumption_resolution,[],[f7128,f194])).

fof(f7128,plain,
    ( ~ l1_orders_2(sK1)
    | u1_orders_2(sK1) = sK7
    | ~ spl15_20
    | ~ spl15_62 ),
    inference(resolution,[],[f431,f711])).

fof(f711,plain,
    ( ! [X6] :
        ( ~ v2_struct_0(X6)
        | ~ l1_orders_2(X6)
        | u1_orders_2(X6) = sK7 )
    | ~ spl15_20 ),
    inference(resolution,[],[f703,f341])).

fof(f703,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f701,f137])).

fof(f701,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(resolution,[],[f597,f165])).

fof(f597,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f153,f135])).

fof(f7126,plain,
    ( spl15_454
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f7109,f384,f249,f3906])).

fof(f3906,plain,
    ( spl15_454
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_454])])).

fof(f384,plain,
    ( spl15_50
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_50])])).

fof(f7109,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))) = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f446])).

fof(f385,plain,
    ( v1_xboole_0(sK3)
    | ~ spl15_50 ),
    inference(avatar_component_clause,[],[f384])).

fof(f7125,plain,
    ( spl15_452
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f7107,f384,f249,f3899])).

fof(f3899,plain,
    ( spl15_452
  <=> sK5(k1_zfmisc_1(sK3)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_452])])).

fof(f7107,plain,
    ( sK5(k1_zfmisc_1(sK3)) = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f436])).

fof(f7124,plain,
    ( spl15_450
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f7106,f384,f249,f3892])).

fof(f3892,plain,
    ( spl15_450
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_450])])).

fof(f7106,plain,
    ( sK3 = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f341])).

fof(f7104,plain,
    ( ~ spl15_777
    | spl15_704
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(avatar_split_clause,[],[f7103,f6132,f3630,f1296,f1146,f193,f5760,f6090])).

fof(f6090,plain,
    ( spl15_777
  <=> ~ v1_xboole_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_777])])).

fof(f5760,plain,
    ( spl15_704
  <=> v1_xboole_0(k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_704])])).

fof(f1296,plain,
    ( spl15_180
  <=> v13_waybel_0(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_180])])).

fof(f3630,plain,
    ( spl15_400
  <=> k4_waybel_0(sK0,sK4(sK0)) = k4_waybel_0(sK1,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_400])])).

fof(f6132,plain,
    ( spl15_778
  <=> r1_tarski(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_778])])).

fof(f7103,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(forward_demodulation,[],[f7102,f3631])).

fof(f3631,plain,
    ( k4_waybel_0(sK0,sK4(sK0)) = k4_waybel_0(sK1,sK4(sK0))
    | ~ spl15_400 ),
    inference(avatar_component_clause,[],[f3630])).

fof(f7102,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180
    | ~ spl15_778 ),
    inference(subsumption_resolution,[],[f6136,f1297])).

fof(f1297,plain,
    ( v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_180 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f6136,plain,
    ( ~ v13_waybel_0(sK4(sK0),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_778 ),
    inference(resolution,[],[f6133,f1381])).

fof(f1381,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X1,sK1)
        | v1_xboole_0(k4_waybel_0(sK1,X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1279,f378])).

fof(f1279,plain,
    ( ! [X0] :
        ( r1_tarski(k4_waybel_0(sK1,X0),X0)
        | ~ v13_waybel_0(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1202,f138])).

fof(f6133,plain,
    ( r1_tarski(sK4(sK0),u1_struct_0(sK0))
    | ~ spl15_778 ),
    inference(avatar_component_clause,[],[f6132])).

fof(f7101,plain,
    ( ~ spl15_777
    | spl15_704
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f7100,f3630,f1296,f1146,f193,f179,f5760,f6090])).

fof(f7100,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f7099,f3631])).

fof(f7099,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180 ),
    inference(subsumption_resolution,[],[f7098,f180])).

fof(f7098,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_180 ),
    inference(subsumption_resolution,[],[f1530,f1297])).

fof(f1530,plain,
    ( ~ v13_waybel_0(sK4(sK0),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1381,f350])).

fof(f350,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f139,f123])).

fof(f7097,plain,
    ( ~ spl15_777
    | spl15_704
    | ~ spl15_686 ),
    inference(avatar_split_clause,[],[f6224,f5691,f5760,f6090])).

fof(f5691,plain,
    ( spl15_686
  <=> r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_686])])).

fof(f6224,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_686 ),
    inference(resolution,[],[f5692,f378])).

fof(f5692,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ spl15_686 ),
    inference(avatar_component_clause,[],[f5691])).

fof(f7096,plain,
    ( ~ spl15_53
    | spl15_776
    | ~ spl15_778 ),
    inference(avatar_split_clause,[],[f6137,f6132,f6087,f390])).

fof(f6087,plain,
    ( spl15_776
  <=> v1_xboole_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_776])])).

fof(f6137,plain,
    ( v1_xboole_0(sK4(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_778 ),
    inference(resolution,[],[f6133,f378])).

fof(f7095,plain,
    ( spl15_776
    | ~ spl15_53
    | ~ spl15_688 ),
    inference(avatar_split_clause,[],[f6126,f5698,f390,f6087])).

fof(f6126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(sK0))
    | ~ spl15_688 ),
    inference(resolution,[],[f5699,f148])).

fof(f7094,plain,
    ( spl15_706
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f7012,f5707,f179,f390,f5772])).

fof(f5772,plain,
    ( spl15_706
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_706])])).

fof(f7012,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_0
    | ~ spl15_690 ),
    inference(subsumption_resolution,[],[f6232,f180])).

fof(f6232,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f2025])).

fof(f2025,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_orders_2(X7)
      | ~ v1_xboole_0(u1_struct_0(X7))
      | v1_xboole_0(k4_waybel_0(X7,X6)) ) ),
    inference(resolution,[],[f140,f148])).

fof(f7093,plain,
    ( spl15_704
    | ~ spl15_53
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f6235,f5707,f390,f5760])).

fof(f6235,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f148])).

fof(f7092,plain,
    ( ~ spl15_53
    | spl15_704
    | ~ spl15_692 ),
    inference(avatar_split_clause,[],[f6227,f5716,f5760,f390])).

fof(f6227,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_692 ),
    inference(resolution,[],[f5717,f378])).

fof(f7091,plain,
    ( spl15_702
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f7015,f5707,f179,f390,f5757])).

fof(f5757,plain,
    ( spl15_702
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_702])])).

fof(f7015,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_0
    | ~ spl15_690 ),
    inference(subsumption_resolution,[],[f6231,f180])).

fof(f6231,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f2086])).

fof(f2086,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_orders_2(X7)
      | ~ v1_xboole_0(u1_struct_0(X7))
      | v1_xboole_0(k3_waybel_0(X7,X6)) ) ),
    inference(resolution,[],[f143,f148])).

fof(f7090,plain,
    ( spl15_520
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_492 ),
    inference(avatar_split_clause,[],[f7045,f4484,f179,f390,f4598])).

fof(f4598,plain,
    ( spl15_520
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_520])])).

fof(f7045,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_492 ),
    inference(subsumption_resolution,[],[f5176,f180])).

fof(f5176,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_492 ),
    inference(resolution,[],[f4485,f2025])).

fof(f7089,plain,
    ( spl15_518
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_492 ),
    inference(avatar_split_clause,[],[f7048,f4484,f179,f390,f4588])).

fof(f4588,plain,
    ( spl15_518
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_518])])).

fof(f7048,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_492 ),
    inference(subsumption_resolution,[],[f5175,f180])).

fof(f5175,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_492 ),
    inference(resolution,[],[f4485,f2086])).

fof(f7088,plain,
    ( spl15_52
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f7087,f1146,f394,f387])).

fof(f387,plain,
    ( spl15_52
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f394,plain,
    ( spl15_54
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f7087,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f395,f1147])).

fof(f395,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f394])).

fof(f7086,plain,
    ( spl15_208
    | ~ spl15_140
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f7085,f1396,f1104,f1420])).

fof(f1420,plain,
    ( spl15_208
  <=> v1_xboole_0(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_208])])).

fof(f1104,plain,
    ( spl15_140
  <=> v1_xboole_0(u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_140])])).

fof(f7085,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_140
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1105,f1397])).

fof(f1105,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_140 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f7084,plain,
    ( spl15_156
    | ~ spl15_142
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f7083,f1146,f1107,f1181])).

fof(f1181,plain,
    ( spl15_156
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_156])])).

fof(f1107,plain,
    ( spl15_142
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_142])])).

fof(f7083,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_142
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1108,f1147])).

fof(f1108,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_142 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f7082,plain,
    ( spl15_428
    | ~ spl15_198
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f7081,f3615,f1363,f3736])).

fof(f3736,plain,
    ( spl15_428
  <=> v1_xboole_0(k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_428])])).

fof(f1363,plain,
    ( spl15_198
  <=> v1_xboole_0(k4_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_198])])).

fof(f7081,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_198
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f1364,f3616])).

fof(f1364,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK1)))
    | ~ spl15_198 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f7080,plain,
    ( spl15_428
    | ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f7079,f3615,f1146,f193,f390,f3736])).

fof(f7079,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f7078,f1147])).

fof(f7078,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5581,f194])).

fof(f5581,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_396 ),
    inference(superposition,[],[f3252,f3616])).

fof(f3252,plain,(
    ! [X8] :
      ( v1_xboole_0(k4_waybel_0(X8,sK4(X8)))
      | ~ v1_xboole_0(u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) ),
    inference(duplicate_literal_removal,[],[f3239])).

fof(f3239,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_xboole_0(u1_struct_0(X8))
      | v1_xboole_0(k4_waybel_0(X8,sK4(X8)))
      | ~ l1_orders_2(X8) ) ),
    inference(resolution,[],[f2025,f123])).

fof(f7077,plain,
    ( spl15_282
    | spl15_380
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f7076,f1853,f1815,f3033,f1903])).

fof(f1903,plain,
    ( spl15_282
  <=> v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_282])])).

fof(f1815,plain,
    ( spl15_264
  <=> l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_264])])).

fof(f7076,plain,
    ( r1_tarski(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3465,f1816])).

fof(f1816,plain,
    ( l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_264 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f3465,plain,
    ( r1_tarski(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f2690,f1854])).

fof(f2690,plain,(
    ! [X3] :
      ( r1_tarski(sK14(X3),u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f166,f139])).

fof(f7075,plain,
    ( spl15_62
    | spl15_362
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f7074,f1146,f317,f2930,f430])).

fof(f7074,plain,
    ( r1_tarski(sK14(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3464,f318])).

fof(f3464,plain,
    ( r1_tarski(sK14(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f2690,f1147])).

fof(f7073,plain,
    ( ~ spl15_197
    | spl15_428
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f4007,f1254,f3736,f1357])).

fof(f1357,plain,
    ( spl15_197
  <=> ~ v1_xboole_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_197])])).

fof(f1254,plain,
    ( spl15_172
  <=> r1_tarski(k4_waybel_0(sK0,sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_172])])).

fof(f4007,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_172 ),
    inference(resolution,[],[f1255,f378])).

fof(f1255,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ spl15_172 ),
    inference(avatar_component_clause,[],[f1254])).

fof(f7072,plain,
    ( ~ spl15_197
    | spl15_428
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f7071,f3615,f193,f3736,f1357])).

fof(f7071,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5290,f194])).

fof(f5290,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_396 ),
    inference(superposition,[],[f738,f3616])).

fof(f738,plain,(
    ! [X1] :
      ( v1_xboole_0(k4_waybel_0(X1,sK4(X1)))
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(sK4(X1)) ) ),
    inference(resolution,[],[f732,f378])).

fof(f732,plain,(
    ! [X0] :
      ( r1_tarski(k4_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f731,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v13_waybel_0(sK4(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f731,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r1_tarski(k4_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ v13_waybel_0(sK4(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f725])).

fof(f725,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r1_tarski(k4_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ v13_waybel_0(sK4(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f127,f123])).

fof(f7070,plain,
    ( ~ spl15_53
    | spl15_430
    | ~ spl15_478 ),
    inference(avatar_split_clause,[],[f4356,f4141,f3744,f390])).

fof(f3744,plain,
    ( spl15_430
  <=> v1_xboole_0(k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_430])])).

fof(f4356,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK3))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_478 ),
    inference(resolution,[],[f4142,f378])).

fof(f7069,plain,
    ( spl15_514
    | ~ spl15_53
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5114,f3660,f1146,f249,f193,f390,f4565])).

fof(f4565,plain,
    ( spl15_514
  <=> v1_xboole_0(k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_514])])).

fof(f3660,plain,
    ( spl15_408
  <=> k4_waybel_0(sK0,sK7) = k4_waybel_0(sK1,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_408])])).

fof(f5114,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5113,f1147])).

fof(f5113,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4463,f194])).

fof(f4463,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(superposition,[],[f3245,f3661])).

fof(f3661,plain,
    ( k4_waybel_0(sK0,sK7) = k4_waybel_0(sK1,sK7)
    | ~ spl15_408 ),
    inference(avatar_component_clause,[],[f3660])).

fof(f3245,plain,
    ( ! [X10] :
        ( v1_xboole_0(k4_waybel_0(X10,sK7))
        | ~ v1_xboole_0(u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
    | ~ spl15_20 ),
    inference(resolution,[],[f2025,f345])).

fof(f7068,plain,
    ( ~ spl15_53
    | spl15_514
    | ~ spl15_502 ),
    inference(avatar_split_clause,[],[f5149,f4522,f4565,f390])).

fof(f5149,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_502 ),
    inference(resolution,[],[f4523,f378])).

fof(f7067,plain,
    ( spl15_962
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_468 ),
    inference(avatar_split_clause,[],[f7060,f4103,f179,f390,f7065])).

fof(f7065,plain,
    ( spl15_962
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_962])])).

fof(f7060,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_468 ),
    inference(subsumption_resolution,[],[f5156,f180])).

fof(f5156,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_468 ),
    inference(resolution,[],[f4104,f2086])).

fof(f7059,plain,
    ( spl15_960
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_468 ),
    inference(avatar_split_clause,[],[f7052,f4103,f179,f390,f7057])).

fof(f7057,plain,
    ( spl15_960
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_960])])).

fof(f7052,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_0
    | ~ spl15_468 ),
    inference(subsumption_resolution,[],[f5157,f180])).

fof(f5157,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)))
    | ~ spl15_468 ),
    inference(resolution,[],[f4104,f2025])).

fof(f7051,plain,
    ( spl15_430
    | ~ spl15_53
    | ~ spl15_468 ),
    inference(avatar_split_clause,[],[f5160,f4103,f390,f3744])).

fof(f5160,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK3))
    | ~ spl15_468 ),
    inference(resolution,[],[f4104,f148])).

fof(f7050,plain,
    ( ~ spl15_53
    | ~ spl15_0
    | ~ spl15_492
    | spl15_519 ),
    inference(avatar_split_clause,[],[f7049,f4585,f4484,f179,f390])).

fof(f4585,plain,
    ( spl15_519
  <=> ~ v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_519])])).

fof(f7049,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_492
    | ~ spl15_519 ),
    inference(subsumption_resolution,[],[f7048,f4586])).

fof(f4586,plain,
    ( ~ v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_519 ),
    inference(avatar_component_clause,[],[f4585])).

fof(f7047,plain,
    ( ~ spl15_53
    | ~ spl15_0
    | ~ spl15_492
    | spl15_521 ),
    inference(avatar_split_clause,[],[f7046,f4595,f4484,f179,f390])).

fof(f4595,plain,
    ( spl15_521
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_521])])).

fof(f7046,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_492
    | ~ spl15_521 ),
    inference(subsumption_resolution,[],[f7045,f4596])).

fof(f4596,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_521 ),
    inference(avatar_component_clause,[],[f4595])).

fof(f7044,plain,
    ( spl15_514
    | ~ spl15_53
    | ~ spl15_492 ),
    inference(avatar_split_clause,[],[f5179,f4484,f390,f4565])).

fof(f5179,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ spl15_492 ),
    inference(resolution,[],[f4485,f148])).

fof(f7043,plain,
    ( ~ spl15_53
    | spl15_428
    | ~ spl15_674 ),
    inference(avatar_split_clause,[],[f5587,f5341,f3736,f390])).

fof(f5587,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_674 ),
    inference(resolution,[],[f5342,f378])).

fof(f7042,plain,
    ( spl15_958
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_664 ),
    inference(avatar_split_clause,[],[f7035,f5303,f179,f390,f7040])).

fof(f7040,plain,
    ( spl15_958
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_958])])).

fof(f7035,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))))
    | ~ spl15_0
    | ~ spl15_664 ),
    inference(subsumption_resolution,[],[f5591,f180])).

fof(f5591,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))))
    | ~ spl15_664 ),
    inference(resolution,[],[f5304,f2086])).

fof(f7034,plain,
    ( spl15_956
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_664 ),
    inference(avatar_split_clause,[],[f7027,f5303,f179,f390,f7032])).

fof(f7032,plain,
    ( spl15_956
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_956])])).

fof(f7027,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))))
    | ~ spl15_0
    | ~ spl15_664 ),
    inference(subsumption_resolution,[],[f5592,f180])).

fof(f5592,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))))
    | ~ spl15_664 ),
    inference(resolution,[],[f5304,f2025])).

fof(f7026,plain,
    ( spl15_428
    | ~ spl15_53
    | ~ spl15_664 ),
    inference(avatar_split_clause,[],[f5595,f5303,f390,f3736])).

fof(f5595,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_664 ),
    inference(resolution,[],[f5304,f148])).

fof(f7025,plain,
    ( ~ spl15_53
    | ~ spl15_0
    | spl15_705 ),
    inference(avatar_split_clause,[],[f7024,f5763,f179,f390])).

fof(f5763,plain,
    ( spl15_705
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_705])])).

fof(f7024,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_705 ),
    inference(subsumption_resolution,[],[f6083,f180])).

fof(f6083,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_705 ),
    inference(resolution,[],[f5764,f3252])).

fof(f5764,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ spl15_705 ),
    inference(avatar_component_clause,[],[f5763])).

fof(f7023,plain,
    ( ~ spl15_53
    | ~ spl15_688
    | spl15_777 ),
    inference(avatar_split_clause,[],[f7022,f6090,f5698,f390])).

fof(f7022,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_688
    | ~ spl15_777 ),
    inference(subsumption_resolution,[],[f6126,f6091])).

fof(f6091,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_777 ),
    inference(avatar_component_clause,[],[f6090])).

fof(f7021,plain,
    ( ~ spl15_53
    | spl15_777
    | ~ spl15_778 ),
    inference(avatar_split_clause,[],[f7020,f6132,f6090,f390])).

fof(f7020,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_777
    | ~ spl15_778 ),
    inference(subsumption_resolution,[],[f6137,f6091])).

fof(f7019,plain,
    ( ~ spl15_53
    | ~ spl15_692
    | spl15_705 ),
    inference(avatar_split_clause,[],[f7018,f5763,f5716,f390])).

fof(f7018,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_692
    | ~ spl15_705 ),
    inference(subsumption_resolution,[],[f6227,f5764])).

fof(f7017,plain,
    ( ~ spl15_53
    | ~ spl15_0
    | ~ spl15_690
    | spl15_703 ),
    inference(avatar_split_clause,[],[f7016,f5754,f5707,f179,f390])).

fof(f5754,plain,
    ( spl15_703
  <=> ~ v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_703])])).

fof(f7016,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_690
    | ~ spl15_703 ),
    inference(subsumption_resolution,[],[f7015,f5755])).

fof(f5755,plain,
    ( ~ v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_703 ),
    inference(avatar_component_clause,[],[f5754])).

fof(f7014,plain,
    ( ~ spl15_53
    | ~ spl15_0
    | ~ spl15_690
    | spl15_707 ),
    inference(avatar_split_clause,[],[f7013,f5769,f5707,f179,f390])).

fof(f5769,plain,
    ( spl15_707
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_707])])).

fof(f7013,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_690
    | ~ spl15_707 ),
    inference(subsumption_resolution,[],[f7012,f5770])).

fof(f5770,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ spl15_707 ),
    inference(avatar_component_clause,[],[f5769])).

fof(f7011,plain,
    ( ~ spl15_53
    | ~ spl15_690
    | spl15_705 ),
    inference(avatar_split_clause,[],[f7010,f5763,f5707,f390])).

fof(f7010,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_690
    | ~ spl15_705 ),
    inference(subsumption_resolution,[],[f6235,f5764])).

fof(f7009,plain,
    ( spl15_790
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f7008,f3637,f2732,f1146,f193,f6361])).

fof(f7008,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f7007,f2733])).

fof(f7007,plain,
    ( ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f7006,f1147])).

fof(f7006,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f7005,f1147])).

fof(f7005,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6354,f194])).

fof(f6354,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_402 ),
    inference(superposition,[],[f140,f3638])).

fof(f3638,plain,
    ( k4_waybel_0(sK0,sK14(sK1)) = k4_waybel_0(sK1,sK14(sK1))
    | ~ spl15_402 ),
    inference(avatar_component_clause,[],[f3637])).

fof(f7004,plain,
    ( spl15_800
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f7003,f3637,f2732,f1146,f193,f6399])).

fof(f7003,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f7002,f2733])).

fof(f7002,plain,
    ( ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f7001,f1147])).

fof(f7001,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f7000,f1147])).

fof(f7000,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6353,f194])).

fof(f6353,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_402 ),
    inference(superposition,[],[f2026,f3638])).

fof(f6999,plain,
    ( spl15_796
    | ~ spl15_799
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6998,f3637,f2732,f1146,f193,f6391,f6385])).

fof(f6385,plain,
    ( spl15_796
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_796])])).

fof(f6391,plain,
    ( spl15_799
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_799])])).

fof(f6998,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6997,f3638])).

fof(f6997,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6996,f2733])).

fof(f6996,plain,
    ( ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6995,f1147])).

fof(f6995,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6351,f194])).

fof(f6351,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_402 ),
    inference(superposition,[],[f2031,f3638])).

fof(f6994,plain,
    ( spl15_792
    | ~ spl15_795
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6993,f3637,f2732,f1146,f193,f6376,f6370])).

fof(f6370,plain,
    ( spl15_792
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_792])])).

fof(f6376,plain,
    ( spl15_795
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_795])])).

fof(f6993,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6992,f3638])).

fof(f6992,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6991,f2733])).

fof(f6991,plain,
    ( ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6990,f1147])).

fof(f6990,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6350,f194])).

fof(f6350,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_402 ),
    inference(superposition,[],[f2032,f3638])).

fof(f6989,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_954
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6985,f3637,f2732,f1146,f249,f193,f179,f6987,f6445,f6429])).

fof(f6429,plain,
    ( spl15_809
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_809])])).

fof(f6445,plain,
    ( spl15_813
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_813])])).

fof(f6987,plain,
    ( spl15_954
  <=> ! [X79] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X79))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_954])])).

fof(f6985,plain,
    ( ! [X79] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X79))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6984,f3638])).

fof(f6984,plain,
    ( ! [X79] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6983,f3638])).

fof(f6983,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6349,f2733])).

fof(f6349,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2302,f3638])).

fof(f6982,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_952
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6978,f3637,f2732,f1146,f249,f193,f179,f6980,f6445,f6429])).

fof(f6980,plain,
    ( spl15_952
  <=> ! [X78] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))),X78) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_952])])).

fof(f6978,plain,
    ( ! [X78] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))),X78) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6977,f3638])).

fof(f6977,plain,
    ( ! [X78] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6976,f3638])).

fof(f6976,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6348,f2733])).

fof(f6348,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2301,f3638])).

fof(f6975,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_950
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6971,f3637,f2732,f1146,f249,f193,f179,f6973,f6445,f6429])).

fof(f6973,plain,
    ( spl15_950
  <=> ! [X77,X76] : k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))),X77) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_950])])).

fof(f6971,plain,
    ( ! [X76,X77] :
        ( k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))),X77) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6970,f3638])).

fof(f6970,plain,
    ( ! [X76,X77] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6969,f3638])).

fof(f6969,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6347,f2733])).

fof(f6347,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2300,f3638])).

fof(f6968,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_948
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6964,f3637,f2732,f1146,f249,f193,f179,f6966,f6445,f6429])).

fof(f6966,plain,
    ( spl15_948
  <=> ! [X75,X74] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X74),X75) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_948])])).

fof(f6964,plain,
    ( ! [X74,X75] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X74),X75) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6963,f3638])).

fof(f6963,plain,
    ( ! [X74,X75] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6962,f3638])).

fof(f6962,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6346,f2733])).

fof(f6346,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2299,f3638])).

fof(f6961,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_946
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6957,f3637,f2732,f1146,f249,f193,f179,f6959,f6445,f6429])).

fof(f6959,plain,
    ( spl15_946
  <=> ! [X73,X72] : k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X73)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_946])])).

fof(f6957,plain,
    ( ! [X72,X73] :
        ( k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X73)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6956,f3638])).

fof(f6956,plain,
    ( ! [X72,X73] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6955,f3638])).

fof(f6955,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6345,f2733])).

fof(f6345,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2298,f3638])).

fof(f6954,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_944
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6950,f3637,f2732,f1146,f249,f193,f179,f6952,f6445,f6429])).

fof(f6952,plain,
    ( spl15_944
  <=> ! [X71] : k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X71) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_944])])).

fof(f6950,plain,
    ( ! [X71] :
        ( k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X71) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6949,f3638])).

fof(f6949,plain,
    ( ! [X71] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6948,f3638])).

fof(f6948,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6344,f2733])).

fof(f6344,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2297,f3638])).

fof(f6947,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_942
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6943,f3637,f2732,f1146,f193,f179,f6945,f6445,f6429])).

fof(f6945,plain,
    ( spl15_942
  <=> ! [X69,X70] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X69) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_942])])).

fof(f6943,plain,
    ( ! [X70,X69] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6942,f3638])).

fof(f6942,plain,
    ( ! [X70,X69] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6941,f3638])).

fof(f6941,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6343,f2733])).

fof(f6343,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2296,f3638])).

fof(f6940,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_940
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6936,f3637,f2732,f1146,f249,f193,f179,f6938,f6445,f6429])).

fof(f6938,plain,
    ( spl15_940
  <=> ! [X68] : sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_940])])).

fof(f6936,plain,
    ( ! [X68] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6935,f3638])).

fof(f6935,plain,
    ( ! [X68] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6934,f3638])).

fof(f6934,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6342,f2733])).

fof(f6342,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2295,f3638])).

fof(f6933,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_938
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6929,f3637,f2732,f1146,f249,f193,f179,f6931,f6445,f6429])).

fof(f6931,plain,
    ( spl15_938
  <=> ! [X67] : k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_938])])).

fof(f6929,plain,
    ( ! [X67] :
        ( k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6928,f3638])).

fof(f6928,plain,
    ( ! [X67] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6927,f3638])).

fof(f6927,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6341,f2733])).

fof(f6341,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2294,f3638])).

fof(f6926,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_936
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6922,f3637,f2732,f1146,f249,f193,f179,f6924,f6445,f6429])).

fof(f6924,plain,
    ( spl15_936
  <=> ! [X65,X66] : k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_936])])).

fof(f6922,plain,
    ( ! [X66,X65] :
        ( k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6921,f3638])).

fof(f6921,plain,
    ( ! [X66,X65] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6920,f3638])).

fof(f6920,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6340,f2733])).

fof(f6340,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2293,f3638])).

fof(f6919,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_934
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6915,f3637,f2732,f1146,f193,f179,f6917,f6445,f6429])).

fof(f6917,plain,
    ( spl15_934
  <=> ! [X63,X64] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_934])])).

fof(f6915,plain,
    ( ! [X64,X63] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6914,f3638])).

fof(f6914,plain,
    ( ! [X64,X63] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6913,f3638])).

fof(f6913,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6339,f2733])).

fof(f6339,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2292,f3638])).

fof(f6912,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_932
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6908,f3637,f2732,f1146,f249,f193,f179,f6910,f6445,f6429])).

fof(f6910,plain,
    ( spl15_932
  <=> ! [X62] : k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_932])])).

fof(f6908,plain,
    ( ! [X62] :
        ( k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6907,f3638])).

fof(f6907,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6906,f3638])).

fof(f6906,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6338,f2733])).

fof(f6338,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2291,f3638])).

fof(f6905,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_930
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6898,f3637,f2732,f1146,f249,f193,f179,f6903,f6445,f6429])).

fof(f6903,plain,
    ( spl15_930
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_930])])).

fof(f6898,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6897,f3638])).

fof(f6897,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6896,f3638])).

fof(f6896,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6337,f2733])).

fof(f6337,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2290,f3638])).

fof(f6895,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_928
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6891,f3637,f2732,f1146,f193,f179,f6893,f6445,f6429])).

fof(f6893,plain,
    ( spl15_928
  <=> ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_928])])).

fof(f6891,plain,
    ( ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6890,f3638])).

fof(f6890,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6889,f3638])).

fof(f6889,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6336,f2733])).

fof(f6336,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2289,f3638])).

fof(f6888,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_926
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6881,f3637,f2732,f1146,f249,f193,f179,f6886,f6445,f6429])).

fof(f6886,plain,
    ( spl15_926
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_926])])).

fof(f6881,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6880,f3638])).

fof(f6880,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6879,f3638])).

fof(f6879,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6335,f2733])).

fof(f6335,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2288,f3638])).

fof(f6878,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_924
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6871,f3637,f2732,f1146,f249,f193,f179,f6876,f6445,f6429])).

fof(f6876,plain,
    ( spl15_924
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_924])])).

fof(f6871,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6870,f3638])).

fof(f6870,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6869,f3638])).

fof(f6869,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6334,f2733])).

fof(f6334,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2287,f3638])).

fof(f6868,plain,
    ( ~ spl15_809
    | ~ spl15_813
    | spl15_922
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6864,f3637,f2732,f1146,f193,f179,f6866,f6445,f6429])).

fof(f6866,plain,
    ( spl15_922
  <=> ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = X60
        | ~ v1_xboole_0(X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_922])])).

fof(f6864,plain,
    ( ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = X60
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6863,f3638])).

fof(f6863,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6862,f3638])).

fof(f6862,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6333,f2733])).

fof(f6333,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2286,f3638])).

fof(f6861,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_920
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6857,f3637,f2732,f1146,f249,f193,f179,f6859,f6445,f6414])).

fof(f6414,plain,
    ( spl15_805
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_805])])).

fof(f6859,plain,
    ( spl15_920
  <=> ! [X59] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X59))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_920])])).

fof(f6857,plain,
    ( ! [X59] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X59))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6856,f3638])).

fof(f6856,plain,
    ( ! [X59] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6855,f3638])).

fof(f6855,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6332,f2733])).

fof(f6332,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2285,f3638])).

fof(f6854,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_918
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6850,f3637,f2732,f1146,f249,f193,f179,f6852,f6445,f6414])).

fof(f6852,plain,
    ( spl15_918
  <=> ! [X58] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))),X58) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_918])])).

fof(f6850,plain,
    ( ! [X58] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))),X58) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6849,f3638])).

fof(f6849,plain,
    ( ! [X58] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6848,f3638])).

fof(f6848,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6331,f2733])).

fof(f6331,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2284,f3638])).

fof(f6847,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_916
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6843,f3637,f2732,f1146,f249,f193,f179,f6845,f6445,f6414])).

fof(f6845,plain,
    ( spl15_916
  <=> ! [X56,X57] : k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))),X57) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_916])])).

fof(f6843,plain,
    ( ! [X57,X56] :
        ( k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))),X57) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6842,f3638])).

fof(f6842,plain,
    ( ! [X57,X56] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6841,f3638])).

fof(f6841,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6330,f2733])).

fof(f6330,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2283,f3638])).

fof(f6840,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_914
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6836,f3637,f2732,f1146,f249,f193,f179,f6838,f6445,f6414])).

fof(f6838,plain,
    ( spl15_914
  <=> ! [X55,X54] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X54),X55) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_914])])).

fof(f6836,plain,
    ( ! [X54,X55] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X54),X55) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6835,f3638])).

fof(f6835,plain,
    ( ! [X54,X55] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6834,f3638])).

fof(f6834,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6329,f2733])).

fof(f6329,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2282,f3638])).

fof(f6833,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_912
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6829,f3637,f2732,f1146,f249,f193,f179,f6831,f6445,f6414])).

fof(f6831,plain,
    ( spl15_912
  <=> ! [X53,X52] : k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X53)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_912])])).

fof(f6829,plain,
    ( ! [X52,X53] :
        ( k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X53)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6828,f3638])).

fof(f6828,plain,
    ( ! [X52,X53] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6827,f3638])).

fof(f6827,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6328,f2733])).

fof(f6328,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2281,f3638])).

fof(f6826,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_910
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6822,f3637,f2732,f1146,f249,f193,f179,f6824,f6445,f6414])).

fof(f6824,plain,
    ( spl15_910
  <=> ! [X51] : k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X51) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_910])])).

fof(f6822,plain,
    ( ! [X51] :
        ( k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),X51) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6821,f3638])).

fof(f6821,plain,
    ( ! [X51] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6820,f3638])).

fof(f6820,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6327,f2733])).

fof(f6327,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2280,f3638])).

fof(f6819,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_908
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6815,f3637,f2732,f1146,f193,f179,f6817,f6445,f6414])).

fof(f6817,plain,
    ( spl15_908
  <=> ! [X49,X50] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_908])])).

fof(f6815,plain,
    ( ! [X50,X49] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6814,f3638])).

fof(f6814,plain,
    ( ! [X50,X49] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6813,f3638])).

fof(f6813,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6326,f2733])).

fof(f6326,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2279,f3638])).

fof(f6812,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_906
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6808,f3637,f2732,f1146,f249,f193,f179,f6810,f6445,f6414])).

fof(f6810,plain,
    ( spl15_906
  <=> ! [X48] : sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_906])])).

fof(f6808,plain,
    ( ! [X48] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6807,f3638])).

fof(f6807,plain,
    ( ! [X48] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6806,f3638])).

fof(f6806,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6325,f2733])).

fof(f6325,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2278,f3638])).

fof(f6805,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_904
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6801,f3637,f2732,f1146,f249,f193,f179,f6803,f6445,f6414])).

fof(f6803,plain,
    ( spl15_904
  <=> ! [X47] : k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_904])])).

fof(f6801,plain,
    ( ! [X47] :
        ( k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6800,f3638])).

fof(f6800,plain,
    ( ! [X47] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6799,f3638])).

fof(f6799,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6324,f2733])).

fof(f6324,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2277,f3638])).

fof(f6798,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_902
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6794,f3637,f2732,f1146,f249,f193,f179,f6796,f6445,f6414])).

fof(f6796,plain,
    ( spl15_902
  <=> ! [X46,X45] : k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_902])])).

fof(f6794,plain,
    ( ! [X45,X46] :
        ( k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6793,f3638])).

fof(f6793,plain,
    ( ! [X45,X46] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6792,f3638])).

fof(f6792,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6323,f2733])).

fof(f6323,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2276,f3638])).

fof(f6791,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_900
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6787,f3637,f2732,f1146,f193,f179,f6789,f6445,f6414])).

fof(f6789,plain,
    ( spl15_900
  <=> ! [X44,X43] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_900])])).

fof(f6787,plain,
    ( ! [X43,X44] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6786,f3638])).

fof(f6786,plain,
    ( ! [X43,X44] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6785,f3638])).

fof(f6785,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6322,f2733])).

fof(f6322,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2275,f3638])).

fof(f6784,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_898
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6780,f3637,f2732,f1146,f249,f193,f179,f6782,f6445,f6414])).

fof(f6782,plain,
    ( spl15_898
  <=> ! [X42] : k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_898])])).

fof(f6780,plain,
    ( ! [X42] :
        ( k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6779,f3638])).

fof(f6779,plain,
    ( ! [X42] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6778,f3638])).

fof(f6778,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6321,f2733])).

fof(f6321,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2274,f3638])).

fof(f6777,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_896
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6770,f3637,f2732,f1146,f249,f193,f179,f6775,f6445,f6414])).

fof(f6775,plain,
    ( spl15_896
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_896])])).

fof(f6770,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6769,f3638])).

fof(f6769,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6768,f3638])).

fof(f6768,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6320,f2733])).

fof(f6320,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2273,f3638])).

fof(f6767,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_894
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6763,f3637,f2732,f1146,f193,f179,f6765,f6445,f6414])).

fof(f6765,plain,
    ( spl15_894
  <=> ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_894])])).

fof(f6763,plain,
    ( ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6762,f3638])).

fof(f6762,plain,
    ( ! [X41] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6761,f3638])).

fof(f6761,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6319,f2733])).

fof(f6319,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2272,f3638])).

fof(f6760,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_892
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6753,f3637,f2732,f1146,f249,f193,f179,f6758,f6445,f6414])).

fof(f6758,plain,
    ( spl15_892
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_892])])).

fof(f6753,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6752,f3638])).

fof(f6752,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6751,f3638])).

fof(f6751,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6318,f2733])).

fof(f6318,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2271,f3638])).

fof(f6750,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_890
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6743,f3637,f2732,f1146,f249,f193,f179,f6748,f6445,f6414])).

fof(f6748,plain,
    ( spl15_890
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_890])])).

fof(f6743,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6742,f3638])).

fof(f6742,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6741,f3638])).

fof(f6741,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6317,f2733])).

fof(f6317,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2270,f3638])).

fof(f6740,plain,
    ( ~ spl15_805
    | ~ spl15_813
    | spl15_888
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6736,f3637,f2732,f1146,f193,f179,f6738,f6445,f6414])).

fof(f6738,plain,
    ( spl15_888
  <=> ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = X40
        | ~ v1_xboole_0(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_888])])).

fof(f6736,plain,
    ( ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))) = X40
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6735,f3638])).

fof(f6735,plain,
    ( ! [X40] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6734,f3638])).

fof(f6734,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6316,f2733])).

fof(f6316,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK14(sK1))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2269,f3638])).

fof(f6733,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_886
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6729,f3637,f2732,f1146,f249,f193,f6731,f6445,f6391])).

fof(f6731,plain,
    ( spl15_886
  <=> ! [X39] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X39))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_886])])).

fof(f6729,plain,
    ( ! [X39] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X39))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6728,f3638])).

fof(f6728,plain,
    ( ! [X39] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6727,f3638])).

fof(f6727,plain,
    ( ! [X39] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6315,f2733])).

fof(f6315,plain,
    ( ! [X39] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2268,f3638])).

fof(f2268,plain,
    ( ! [X35,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X35),sK1)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X35))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X35)),X36))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f888])).

fof(f2129,plain,
    ( ! [X1] :
        ( v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK1,X1)))
        | ~ v13_waybel_0(k4_waybel_0(sK1,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2042,f378])).

fof(f6726,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_884
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6722,f3637,f2732,f1146,f249,f193,f6724,f6445,f6391])).

fof(f6724,plain,
    ( spl15_884
  <=> ! [X38] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))),X38) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_884])])).

fof(f6722,plain,
    ( ! [X38] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))),X38) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6721,f3638])).

fof(f6721,plain,
    ( ! [X38] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6720,f3638])).

fof(f6720,plain,
    ( ! [X38] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6314,f2733])).

fof(f6314,plain,
    ( ! [X38] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2267,f3638])).

fof(f2267,plain,
    ( ! [X33,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X33),sK1)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X33))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X33)))),X34) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f876])).

fof(f6719,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_882
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6715,f3637,f2732,f1146,f249,f193,f6717,f6445,f6391])).

fof(f6717,plain,
    ( spl15_882
  <=> ! [X36,X37] : k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))),X37) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_882])])).

fof(f6715,plain,
    ( ! [X37,X36] :
        ( k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))),X37) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6714,f3638])).

fof(f6714,plain,
    ( ! [X37,X36] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6713,f3638])).

fof(f6713,plain,
    ( ! [X37,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6313,f2733])).

fof(f6313,plain,
    ( ! [X37,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2266,f3638])).

fof(f2266,plain,
    ( ! [X30,X31,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X30),sK1)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X30))
        | k2_zfmisc_1(k2_zfmisc_1(X31,k4_waybel_0(sK1,k4_waybel_0(sK1,X30))),X32) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f874])).

fof(f6712,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_880
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6708,f3637,f2732,f1146,f249,f193,f6710,f6445,f6391])).

fof(f6710,plain,
    ( spl15_880
  <=> ! [X34,X35] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X34),X35) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_880])])).

fof(f6708,plain,
    ( ! [X35,X34] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X34),X35) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6707,f3638])).

fof(f6707,plain,
    ( ! [X35,X34] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6706,f3638])).

fof(f6706,plain,
    ( ! [X35,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6312,f2733])).

fof(f6312,plain,
    ( ! [X35,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2265,f3638])).

fof(f2265,plain,
    ( ! [X28,X29,X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X27),sK1)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X27))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X27)),X28),X29) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f873])).

fof(f6705,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_878
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6701,f3637,f2732,f1146,f249,f193,f6703,f6445,f6391])).

fof(f6703,plain,
    ( spl15_878
  <=> ! [X32,X33] : k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X33)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_878])])).

fof(f6701,plain,
    ( ! [X33,X32] :
        ( k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X33)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6700,f3638])).

fof(f6700,plain,
    ( ! [X33,X32] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6699,f3638])).

fof(f6699,plain,
    ( ! [X33,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6311,f2733])).

fof(f6311,plain,
    ( ! [X33,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2264,f3638])).

fof(f2264,plain,
    ( ! [X26,X24,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X24),sK1)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X24))
        | k2_zfmisc_1(X25,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X24)),X26)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f855])).

fof(f6698,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_876
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6694,f3637,f2732,f1146,f249,f193,f6696,f6445,f6391])).

fof(f6696,plain,
    ( spl15_876
  <=> ! [X31] : k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X31) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_876])])).

fof(f6694,plain,
    ( ! [X31] :
        ( k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X31) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6693,f3638])).

fof(f6693,plain,
    ( ! [X31] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6692,f3638])).

fof(f6692,plain,
    ( ! [X31] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6310,f2733])).

fof(f6310,plain,
    ( ! [X31] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2263,f3638])).

fof(f2263,plain,
    ( ! [X23,X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X22),sK1)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X22))
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X22)),X23) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f851])).

fof(f6691,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_874
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6687,f3637,f2732,f1146,f193,f6689,f6445,f6391])).

fof(f6689,plain,
    ( spl15_874
  <=> ! [X29,X30] :
        ( k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X29) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_874])])).

fof(f6687,plain,
    ( ! [X30,X29] :
        ( k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6686,f3638])).

fof(f6686,plain,
    ( ! [X30,X29] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6685,f3638])).

fof(f6685,plain,
    ( ! [X30,X29] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6309,f2733])).

fof(f6309,plain,
    ( ! [X30,X29] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2262,f3638])).

fof(f2262,plain,
    ( ! [X21,X19,X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X19),sK1)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X19))
        | k2_zfmisc_1(X20,X21) = k4_waybel_0(sK1,k4_waybel_0(sK1,X19))
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f850])).

fof(f6684,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_872
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6680,f3637,f2732,f1146,f249,f193,f6682,f6445,f6391])).

fof(f6682,plain,
    ( spl15_872
  <=> ! [X28] : sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_872])])).

fof(f6680,plain,
    ( ! [X28] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6679,f3638])).

fof(f6679,plain,
    ( ! [X28] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6678,f3638])).

fof(f6678,plain,
    ( ! [X28] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6308,f2733])).

fof(f6308,plain,
    ( ! [X28] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2261,f3638])).

fof(f2261,plain,
    ( ! [X17,X18] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X17),sK1)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X17))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X18,k4_waybel_0(sK1,k4_waybel_0(sK1,X17))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f718])).

fof(f6677,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_870
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6673,f3637,f2732,f1146,f249,f193,f6675,f6445,f6391])).

fof(f6675,plain,
    ( spl15_870
  <=> ! [X27] : k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_870])])).

fof(f6673,plain,
    ( ! [X27] :
        ( k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6672,f3638])).

fof(f6672,plain,
    ( ! [X27] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6671,f3638])).

fof(f6671,plain,
    ( ! [X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6307,f2733])).

fof(f6307,plain,
    ( ! [X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2260,f3638])).

fof(f2260,plain,
    ( ! [X15,X16] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X15),sK1)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X15))
        | k2_zfmisc_1(X16,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X15))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f694])).

fof(f6670,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_868
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6666,f3637,f2732,f1146,f249,f193,f6668,f6445,f6391])).

fof(f6668,plain,
    ( spl15_868
  <=> ! [X25,X26] : k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_868])])).

fof(f6666,plain,
    ( ! [X26,X25] :
        ( k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6665,f3638])).

fof(f6665,plain,
    ( ! [X26,X25] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6664,f3638])).

fof(f6664,plain,
    ( ! [X26,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6306,f2733])).

fof(f6306,plain,
    ( ! [X26,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2259,f3638])).

fof(f2259,plain,
    ( ! [X14,X12,X13] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X12),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X12))
        | k2_zfmisc_1(X13,k2_zfmisc_1(X14,k4_waybel_0(sK1,k4_waybel_0(sK1,X12)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f692])).

fof(f6663,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_866
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6659,f3637,f2732,f1146,f193,f6661,f6445,f6391])).

fof(f6661,plain,
    ( spl15_866
  <=> ! [X23,X24] :
        ( k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X24) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_866])])).

fof(f6659,plain,
    ( ! [X24,X23] :
        ( k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6658,f3638])).

fof(f6658,plain,
    ( ! [X24,X23] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6657,f3638])).

fof(f6657,plain,
    ( ! [X24,X23] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6305,f2733])).

fof(f6305,plain,
    ( ! [X24,X23] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2258,f3638])).

fof(f2258,plain,
    ( ! [X10,X11,X9] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X9),sK1)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X9))
        | k2_zfmisc_1(X10,X11) = k4_waybel_0(sK1,k4_waybel_0(sK1,X9))
        | ~ v1_xboole_0(X11) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f652])).

fof(f6656,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_864
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6652,f3637,f2732,f1146,f249,f193,f6654,f6445,f6391])).

fof(f6654,plain,
    ( spl15_864
  <=> ! [X22] : k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_864])])).

fof(f6652,plain,
    ( ! [X22] :
        ( k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6651,f3638])).

fof(f6651,plain,
    ( ! [X22] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6650,f3638])).

fof(f6650,plain,
    ( ! [X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6304,f2733])).

fof(f6304,plain,
    ( ! [X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2257,f3638])).

fof(f2257,plain,
    ( ! [X8,X7] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X7),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X7))
        | k2_zfmisc_1(X8,k4_waybel_0(sK1,k4_waybel_0(sK1,X7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f651])).

fof(f6649,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_862
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6642,f3637,f2732,f1146,f249,f193,f6647,f6445,f6391])).

fof(f6647,plain,
    ( spl15_862
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_862])])).

fof(f6642,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6641,f3638])).

fof(f6641,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6640,f3638])).

fof(f6640,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6303,f2733])).

fof(f6303,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2256,f3638])).

fof(f2256,plain,
    ( ! [X6] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X6),sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X6))
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X6)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f446])).

fof(f6639,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_860
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6635,f3637,f2732,f1146,f193,f6637,f6445,f6391])).

fof(f6637,plain,
    ( spl15_860
  <=> ! [X21] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_860])])).

fof(f6635,plain,
    ( ! [X21] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6634,f3638])).

fof(f6634,plain,
    ( ! [X21] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6633,f3638])).

fof(f6633,plain,
    ( ! [X21] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6302,f2733])).

fof(f6302,plain,
    ( ! [X21] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2255,f3638])).

fof(f2255,plain,
    ( ! [X4,X5] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X4))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,X4)) = sK5(k1_zfmisc_1(X5))
        | ~ v1_xboole_0(X5) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f437])).

fof(f6632,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_858
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6625,f3637,f2732,f1146,f249,f193,f6630,f6445,f6391])).

fof(f6630,plain,
    ( spl15_858
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_858])])).

fof(f6625,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6624,f3638])).

fof(f6624,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6623,f3638])).

fof(f6623,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6301,f2733])).

fof(f6301,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2254,f3638])).

fof(f2254,plain,
    ( ! [X3] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X3))
        | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,X3)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f436])).

fof(f6622,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_856
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6615,f3637,f2732,f1146,f249,f193,f6620,f6445,f6391])).

fof(f6620,plain,
    ( spl15_856
  <=> k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_856])])).

fof(f6615,plain,
    ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6614,f3638])).

fof(f6614,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6613,f3638])).

fof(f6613,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6300,f2733])).

fof(f6300,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2253,f3638])).

fof(f2253,plain,
    ( ! [X2] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X2))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,X2)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f341])).

fof(f6612,plain,
    ( ~ spl15_799
    | ~ spl15_813
    | spl15_854
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6608,f3637,f2732,f1146,f193,f6610,f6445,f6391])).

fof(f6610,plain,
    ( spl15_854
  <=> ! [X20] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = X20
        | ~ v1_xboole_0(X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_854])])).

fof(f6608,plain,
    ( ! [X20] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = X20
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6607,f3638])).

fof(f6607,plain,
    ( ! [X20] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6606,f3638])).

fof(f6606,plain,
    ( ! [X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6299,f2733])).

fof(f6299,plain,
    ( ! [X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2252,f3638])).

fof(f2252,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(k4_waybel_0(sK1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X0))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2129,f131])).

fof(f6605,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_852
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6601,f3637,f2732,f1146,f249,f193,f6603,f6445,f6376])).

fof(f6603,plain,
    ( spl15_852
  <=> ! [X19] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X19))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_852])])).

fof(f6601,plain,
    ( ! [X19] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X19))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6600,f3638])).

fof(f6600,plain,
    ( ! [X19] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6599,f3638])).

fof(f6599,plain,
    ( ! [X19] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6298,f2733])).

fof(f6298,plain,
    ( ! [X19] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2250,f3638])).

fof(f2250,plain,
    ( ! [X35,X36] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X35),sK1)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X35))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X35)),X36))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f888])).

fof(f2127,plain,
    ( ! [X1] :
        ( v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK1,X1)))
        | ~ v12_waybel_0(k4_waybel_0(sK1,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2041,f378])).

fof(f6598,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_850
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6594,f3637,f2732,f1146,f249,f193,f6596,f6445,f6376])).

fof(f6596,plain,
    ( spl15_850
  <=> ! [X18] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))),X18) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_850])])).

fof(f6594,plain,
    ( ! [X18] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))),X18) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6593,f3638])).

fof(f6593,plain,
    ( ! [X18] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6592,f3638])).

fof(f6592,plain,
    ( ! [X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6297,f2733])).

fof(f6297,plain,
    ( ! [X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2249,f3638])).

fof(f2249,plain,
    ( ! [X33,X34] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X33),sK1)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X33))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X33)))),X34) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f876])).

fof(f6591,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_848
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6587,f3637,f2732,f1146,f249,f193,f6589,f6445,f6376])).

fof(f6589,plain,
    ( spl15_848
  <=> ! [X16,X17] : k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))),X17) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_848])])).

fof(f6587,plain,
    ( ! [X17,X16] :
        ( k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))),X17) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6586,f3638])).

fof(f6586,plain,
    ( ! [X17,X16] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6585,f3638])).

fof(f6585,plain,
    ( ! [X17,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6296,f2733])).

fof(f6296,plain,
    ( ! [X17,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2248,f3638])).

fof(f2248,plain,
    ( ! [X30,X31,X32] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X30),sK1)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X30))
        | k2_zfmisc_1(k2_zfmisc_1(X31,k3_waybel_0(sK1,k4_waybel_0(sK1,X30))),X32) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f874])).

fof(f6584,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_846
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6580,f3637,f2732,f1146,f249,f193,f6582,f6445,f6376])).

fof(f6582,plain,
    ( spl15_846
  <=> ! [X15,X14] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X14),X15) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_846])])).

fof(f6580,plain,
    ( ! [X14,X15] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X14),X15) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6579,f3638])).

fof(f6579,plain,
    ( ! [X14,X15] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6578,f3638])).

fof(f6578,plain,
    ( ! [X14,X15] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6295,f2733])).

fof(f6295,plain,
    ( ! [X14,X15] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2247,f3638])).

fof(f2247,plain,
    ( ! [X28,X29,X27] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X27),sK1)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X27))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X27)),X28),X29) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f873])).

fof(f6577,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_844
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6573,f3637,f2732,f1146,f249,f193,f6575,f6445,f6376])).

fof(f6575,plain,
    ( spl15_844
  <=> ! [X13,X12] : k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X13)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_844])])).

fof(f6573,plain,
    ( ! [X12,X13] :
        ( k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X13)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6572,f3638])).

fof(f6572,plain,
    ( ! [X12,X13] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6571,f3638])).

fof(f6571,plain,
    ( ! [X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6294,f2733])).

fof(f6294,plain,
    ( ! [X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2246,f3638])).

fof(f2246,plain,
    ( ! [X26,X24,X25] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X24),sK1)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X24))
        | k2_zfmisc_1(X25,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X24)),X26)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f855])).

fof(f6570,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_842
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6566,f3637,f2732,f1146,f249,f193,f6568,f6445,f6376])).

fof(f6568,plain,
    ( spl15_842
  <=> ! [X11] : k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X11) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_842])])).

fof(f6566,plain,
    ( ! [X11] :
        ( k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),X11) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6565,f3638])).

fof(f6565,plain,
    ( ! [X11] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6564,f3638])).

fof(f6564,plain,
    ( ! [X11] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6293,f2733])).

fof(f6293,plain,
    ( ! [X11] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2245,f3638])).

fof(f2245,plain,
    ( ! [X23,X22] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X22),sK1)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X22))
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X22)),X23) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f851])).

fof(f6563,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_840
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6559,f3637,f2732,f1146,f193,f6561,f6445,f6376])).

fof(f6561,plain,
    ( spl15_840
  <=> ! [X9,X10] :
        ( k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_840])])).

fof(f6559,plain,
    ( ! [X10,X9] :
        ( k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6558,f3638])).

fof(f6558,plain,
    ( ! [X10,X9] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6557,f3638])).

fof(f6557,plain,
    ( ! [X10,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6292,f2733])).

fof(f6292,plain,
    ( ! [X10,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2244,f3638])).

fof(f2244,plain,
    ( ! [X21,X19,X20] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X19),sK1)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X19))
        | k2_zfmisc_1(X20,X21) = k3_waybel_0(sK1,k4_waybel_0(sK1,X19))
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f850])).

fof(f6556,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_838
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6552,f3637,f2732,f1146,f249,f193,f6554,f6445,f6376])).

fof(f6554,plain,
    ( spl15_838
  <=> ! [X8] : sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_838])])).

fof(f6552,plain,
    ( ! [X8] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6551,f3638])).

fof(f6551,plain,
    ( ! [X8] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6550,f3638])).

fof(f6550,plain,
    ( ! [X8] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6291,f2733])).

fof(f6291,plain,
    ( ! [X8] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2243,f3638])).

fof(f2243,plain,
    ( ! [X17,X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X17),sK1)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X17))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X18,k3_waybel_0(sK1,k4_waybel_0(sK1,X17))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f718])).

fof(f6549,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_836
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6545,f3637,f2732,f1146,f249,f193,f6547,f6445,f6376])).

fof(f6547,plain,
    ( spl15_836
  <=> ! [X7] : k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_836])])).

fof(f6545,plain,
    ( ! [X7] :
        ( k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6544,f3638])).

fof(f6544,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6543,f3638])).

fof(f6543,plain,
    ( ! [X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6290,f2733])).

fof(f6290,plain,
    ( ! [X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2242,f3638])).

fof(f2242,plain,
    ( ! [X15,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X15),sK1)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X15))
        | k2_zfmisc_1(X16,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X15))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f694])).

fof(f6542,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_834
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6538,f3637,f2732,f1146,f249,f193,f6540,f6445,f6376])).

fof(f6540,plain,
    ( spl15_834
  <=> ! [X5,X6] : k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_834])])).

fof(f6538,plain,
    ( ! [X6,X5] :
        ( k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6537,f3638])).

fof(f6537,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6536,f3638])).

fof(f6536,plain,
    ( ! [X6,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6289,f2733])).

fof(f6289,plain,
    ( ! [X6,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2241,f3638])).

fof(f2241,plain,
    ( ! [X14,X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X12),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X12))
        | k2_zfmisc_1(X13,k2_zfmisc_1(X14,k3_waybel_0(sK1,k4_waybel_0(sK1,X12)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f692])).

fof(f6535,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_832
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6531,f3637,f2732,f1146,f193,f6533,f6445,f6376])).

fof(f6533,plain,
    ( spl15_832
  <=> ! [X3,X4] :
        ( k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_832])])).

fof(f6531,plain,
    ( ! [X4,X3] :
        ( k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6530,f3638])).

fof(f6530,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6529,f3638])).

fof(f6529,plain,
    ( ! [X4,X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6288,f2733])).

fof(f6288,plain,
    ( ! [X4,X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2240,f3638])).

fof(f2240,plain,
    ( ! [X10,X11,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X9),sK1)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X9))
        | k2_zfmisc_1(X10,X11) = k3_waybel_0(sK1,k4_waybel_0(sK1,X9))
        | ~ v1_xboole_0(X11) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f652])).

fof(f6528,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_830
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6524,f3637,f2732,f1146,f249,f193,f6526,f6445,f6376])).

fof(f6526,plain,
    ( spl15_830
  <=> ! [X2] : k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_830])])).

fof(f6524,plain,
    ( ! [X2] :
        ( k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6523,f3638])).

fof(f6523,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6522,f3638])).

fof(f6522,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6287,f2733])).

fof(f6287,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2239,f3638])).

fof(f2239,plain,
    ( ! [X8,X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X7),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X7))
        | k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,X7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f651])).

fof(f6521,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_828
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6514,f3637,f2732,f1146,f249,f193,f6519,f6445,f6376])).

fof(f6519,plain,
    ( spl15_828
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_828])])).

fof(f6514,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6513,f3638])).

fof(f6513,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6512,f3638])).

fof(f6512,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6286,f2733])).

fof(f6286,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2238,f3638])).

fof(f2238,plain,
    ( ! [X6] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X6),sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X6))
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X6)))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f446])).

fof(f6511,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_826
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6507,f3637,f2732,f1146,f193,f6509,f6445,f6376])).

fof(f6509,plain,
    ( spl15_826
  <=> ! [X1] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_826])])).

fof(f6507,plain,
    ( ! [X1] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6506,f3638])).

fof(f6506,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6505,f3638])).

fof(f6505,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6285,f2733])).

fof(f6285,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2237,f3638])).

fof(f2237,plain,
    ( ! [X4,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X4))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,X4)) = sK5(k1_zfmisc_1(X5))
        | ~ v1_xboole_0(X5) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f437])).

fof(f6504,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_824
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6497,f3637,f2732,f1146,f249,f193,f6502,f6445,f6376])).

fof(f6502,plain,
    ( spl15_824
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_824])])).

fof(f6497,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6496,f3638])).

fof(f6496,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6495,f3638])).

fof(f6495,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6284,f2733])).

fof(f6284,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2236,f3638])).

fof(f2236,plain,
    ( ! [X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X3))
        | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,X3)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f436])).

fof(f6494,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_822
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6487,f3637,f2732,f1146,f249,f193,f6492,f6445,f6376])).

fof(f6492,plain,
    ( spl15_822
  <=> k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_822])])).

fof(f6487,plain,
    ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6486,f3638])).

fof(f6486,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6485,f3638])).

fof(f6485,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6283,f2733])).

fof(f6283,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2235,f3638])).

fof(f2235,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X2))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,X2)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f341])).

fof(f6484,plain,
    ( ~ spl15_795
    | ~ spl15_813
    | spl15_820
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6480,f3637,f2732,f1146,f193,f6482,f6445,f6376])).

fof(f6482,plain,
    ( spl15_820
  <=> ! [X0] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_820])])).

fof(f6480,plain,
    ( ! [X0] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))) = X0
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6479,f3638])).

fof(f6479,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6478,f3638])).

fof(f6478,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6282,f2733])).

fof(f6282,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
        | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK14(sK1))) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2234,f3638])).

fof(f2234,plain,
    ( ! [X0,X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,X0))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2127,f131])).

fof(f6477,plain,
    ( spl15_818
    | ~ spl15_809
    | ~ spl15_813
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6470,f3637,f2732,f1146,f193,f179,f6445,f6429,f6475])).

fof(f6475,plain,
    ( spl15_818
  <=> v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_818])])).

fof(f6470,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6469,f3638])).

fof(f6469,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6468,f3638])).

fof(f6468,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6281,f2733])).

fof(f6281,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2133,f3638])).

fof(f6467,plain,
    ( spl15_816
    | ~ spl15_805
    | ~ spl15_813
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6460,f3637,f2732,f1146,f193,f179,f6445,f6414,f6465])).

fof(f6465,plain,
    ( spl15_816
  <=> v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_816])])).

fof(f6460,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6459,f3638])).

fof(f6459,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6458,f3638])).

fof(f6458,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6280,f2733])).

fof(f6280,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2131,f3638])).

fof(f6457,plain,
    ( spl15_814
    | ~ spl15_799
    | ~ spl15_813
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6450,f3637,f2732,f1146,f193,f6445,f6391,f6455])).

fof(f6455,plain,
    ( spl15_814
  <=> v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_814])])).

fof(f6450,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6449,f3638])).

fof(f6449,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6448,f3638])).

fof(f6448,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6279,f2733])).

fof(f6279,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2129,f3638])).

fof(f6447,plain,
    ( spl15_810
    | ~ spl15_795
    | ~ spl15_813
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6434,f3637,f2732,f1146,f193,f6445,f6376,f6439])).

fof(f6439,plain,
    ( spl15_810
  <=> v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_810])])).

fof(f6434,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6433,f3638])).

fof(f6433,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6432,f3638])).

fof(f6432,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6278,f2733])).

fof(f6278,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2127,f3638])).

fof(f6431,plain,
    ( spl15_806
    | ~ spl15_809
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6418,f3637,f2732,f1146,f193,f179,f6429,f6423])).

fof(f6423,plain,
    ( spl15_806
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_806])])).

fof(f6418,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6417,f3638])).

fof(f6417,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6277,f2733])).

fof(f6277,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2048,f3638])).

fof(f6416,plain,
    ( spl15_802
    | ~ spl15_805
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6403,f3637,f2732,f1146,f193,f179,f6414,f6408])).

fof(f6408,plain,
    ( spl15_802
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_802])])).

fof(f6403,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6402,f3638])).

fof(f6402,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6276,f2733])).

fof(f6276,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2047,f3638])).

fof(f6401,plain,
    ( spl15_800
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6394,f3637,f2732,f1146,f193,f6399])).

fof(f6394,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6275,f2733])).

fof(f6275,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2046,f3638])).

fof(f6393,plain,
    ( spl15_796
    | ~ spl15_799
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6380,f3637,f2732,f1146,f193,f6391,f6385])).

fof(f6380,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6379,f3638])).

fof(f6379,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6274,f2733])).

fof(f6274,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2042,f3638])).

fof(f6378,plain,
    ( spl15_792
    | ~ spl15_795
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6365,f3637,f2732,f1146,f193,f6376,f6370])).

fof(f6365,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK14(sK1)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(forward_demodulation,[],[f6364,f3638])).

fof(f6364,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6273,f2733])).

fof(f6273,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK14(sK1))),k4_waybel_0(sK0,sK14(sK1)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK14(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2041,f3638])).

fof(f6363,plain,
    ( spl15_790
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f6356,f3637,f2732,f1146,f193,f6361])).

fof(f6356,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332
    | ~ spl15_402 ),
    inference(subsumption_resolution,[],[f6272,f2733])).

fof(f6272,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK14(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_402 ),
    inference(superposition,[],[f2038,f3638])).

fof(f6269,plain,
    ( ~ spl15_787
    | spl15_788
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f6230,f5707,f1146,f193,f6267,f6261])).

fof(f6261,plain,
    ( spl15_787
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_787])])).

fof(f6267,plain,
    ( spl15_788
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_788])])).

fof(f6230,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f1202])).

fof(f6256,plain,
    ( ~ spl15_783
    | spl15_784
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f6229,f5707,f1146,f193,f6254,f6248])).

fof(f6248,plain,
    ( spl15_783
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_783])])).

fof(f6254,plain,
    ( spl15_784
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_784])])).

fof(f6229,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f1203])).

fof(f6243,plain,
    ( spl15_780
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_690 ),
    inference(avatar_split_clause,[],[f6228,f5707,f1396,f1146,f193,f179,f6241])).

fof(f6228,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_690 ),
    inference(resolution,[],[f5708,f3584])).

fof(f6189,plain,
    ( spl15_686
    | ~ spl15_182
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6188,f3630,f1305,f5691])).

fof(f1305,plain,
    ( spl15_182
  <=> r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_182])])).

fof(f6188,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ spl15_182
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f1306,f3631])).

fof(f1306,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ spl15_182 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f6187,plain,
    ( ~ spl15_181
    | spl15_686
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(avatar_split_clause,[],[f6186,f6132,f3630,f1146,f193,f5691,f1299])).

fof(f1299,plain,
    ( spl15_181
  <=> ~ v13_waybel_0(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_181])])).

fof(f6186,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(subsumption_resolution,[],[f5605,f6133])).

fof(f5605,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ r1_tarski(sK4(sK0),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f1279,f3631])).

fof(f6185,plain,
    ( ~ spl15_181
    | spl15_686
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(avatar_split_clause,[],[f6184,f6132,f3630,f1146,f193,f5691,f1299])).

fof(f6184,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_778 ),
    inference(subsumption_resolution,[],[f6183,f6133])).

fof(f6183,plain,
    ( ~ r1_tarski(sK4(sK0),u1_struct_0(sK0))
    | r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6182,f1147])).

fof(f6182,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ r1_tarski(sK4(sK0),u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_400 ),
    inference(subsumption_resolution,[],[f5686,f194])).

fof(f5686,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ l1_orders_2(sK1)
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ r1_tarski(sK4(sK0),u1_struct_0(sK1))
    | ~ spl15_400 ),
    inference(superposition,[],[f728,f3631])).

fof(f6181,plain,
    ( spl15_180
    | ~ spl15_687
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_688 ),
    inference(avatar_split_clause,[],[f6180,f5698,f3630,f1146,f193,f5694,f1296])).

fof(f5694,plain,
    ( spl15_687
  <=> ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_687])])).

fof(f6180,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_688 ),
    inference(subsumption_resolution,[],[f6179,f5699])).

fof(f6179,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6079,f1147])).

fof(f6079,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_400 ),
    inference(subsumption_resolution,[],[f5689,f194])).

fof(f5689,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_400 ),
    inference(superposition,[],[f126,f3631])).

fof(f6178,plain,
    ( ~ spl15_181
    | spl15_686
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_688 ),
    inference(avatar_split_clause,[],[f6177,f5698,f3630,f1146,f193,f5691,f1299])).

fof(f6177,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400
    | ~ spl15_688 ),
    inference(forward_demodulation,[],[f6121,f3631])).

fof(f6121,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_688 ),
    inference(resolution,[],[f5699,f1202])).

fof(f6174,plain,
    ( ~ spl15_0
    | spl15_687 ),
    inference(avatar_contradiction_clause,[],[f6173])).

fof(f6173,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_687 ),
    inference(subsumption_resolution,[],[f6171,f180])).

fof(f6171,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_687 ),
    inference(resolution,[],[f5695,f732])).

fof(f5695,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ spl15_687 ),
    inference(avatar_component_clause,[],[f5694])).

fof(f6134,plain,
    ( spl15_778
    | ~ spl15_688 ),
    inference(avatar_split_clause,[],[f6127,f5698,f6132])).

fof(f6127,plain,
    ( r1_tarski(sK4(sK0),u1_struct_0(sK0))
    | ~ spl15_688 ),
    inference(resolution,[],[f5699,f139])).

fof(f6118,plain,
    ( ~ spl15_0
    | spl15_689 ),
    inference(avatar_contradiction_clause,[],[f6117])).

fof(f6117,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_689 ),
    inference(subsumption_resolution,[],[f6115,f180])).

fof(f6115,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_689 ),
    inference(resolution,[],[f5702,f123])).

fof(f5702,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_689 ),
    inference(avatar_component_clause,[],[f5701])).

fof(f5701,plain,
    ( spl15_689
  <=> ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_689])])).

fof(f6092,plain,
    ( ~ spl15_777
    | ~ spl15_0
    | spl15_705 ),
    inference(avatar_split_clause,[],[f6085,f5763,f179,f6090])).

fof(f6085,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_0
    | ~ spl15_705 ),
    inference(subsumption_resolution,[],[f6084,f180])).

fof(f6084,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(sK4(sK0))
    | ~ spl15_705 ),
    inference(resolution,[],[f5764,f738])).

fof(f6082,plain,
    ( ~ spl15_687
    | ~ spl15_689
    | ~ spl15_4
    | ~ spl15_150
    | spl15_181
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6081,f3630,f1299,f1146,f193,f5701,f5694])).

fof(f6081,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_181
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6080,f1147])).

fof(f6080,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_181
    | ~ spl15_400 ),
    inference(subsumption_resolution,[],[f6079,f1300])).

fof(f1300,plain,
    ( ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_181 ),
    inference(avatar_component_clause,[],[f1299])).

fof(f6078,plain,
    ( spl15_690
    | ~ spl15_689
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6077,f3630,f1146,f193,f5701,f5707])).

fof(f6077,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6076,f1147])).

fof(f6076,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6075,f1147])).

fof(f6075,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_400 ),
    inference(subsumption_resolution,[],[f5688,f194])).

fof(f5688,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_400 ),
    inference(superposition,[],[f140,f3631])).

fof(f6074,plain,
    ( spl15_692
    | ~ spl15_689
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6073,f3630,f1146,f193,f5701,f5716])).

fof(f6073,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6072,f1147])).

fof(f6072,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6071,f1147])).

fof(f6071,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_400 ),
    inference(subsumption_resolution,[],[f5687,f194])).

fof(f5687,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_400 ),
    inference(superposition,[],[f2026,f3631])).

fof(f6064,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_774
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6060,f3630,f1146,f249,f193,f179,f6062,f5763,f5744,f5701])).

fof(f5744,plain,
    ( spl15_701
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_701])])).

fof(f6062,plain,
    ( spl15_774
  <=> ! [X79] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X79))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_774])])).

fof(f6060,plain,
    ( ! [X79] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X79))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6059,f3631])).

fof(f6059,plain,
    ( ! [X79] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5683,f3631])).

fof(f5683,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2302,f3631])).

fof(f6058,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_772
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6054,f3630,f1146,f249,f193,f179,f6056,f5763,f5744,f5701])).

fof(f6056,plain,
    ( spl15_772
  <=> ! [X78] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))),X78) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_772])])).

fof(f6054,plain,
    ( ! [X78] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))),X78) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6053,f3631])).

fof(f6053,plain,
    ( ! [X78] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5682,f3631])).

fof(f5682,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2301,f3631])).

fof(f6052,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_770
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6048,f3630,f1146,f249,f193,f179,f6050,f5763,f5744,f5701])).

fof(f6050,plain,
    ( spl15_770
  <=> ! [X77,X76] : k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))),X77) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_770])])).

fof(f6048,plain,
    ( ! [X76,X77] :
        ( k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))),X77) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6047,f3631])).

fof(f6047,plain,
    ( ! [X76,X77] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5681,f3631])).

fof(f5681,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2300,f3631])).

fof(f6046,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_768
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6042,f3630,f1146,f249,f193,f179,f6044,f5763,f5744,f5701])).

fof(f6044,plain,
    ( spl15_768
  <=> ! [X75,X74] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X74),X75) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_768])])).

fof(f6042,plain,
    ( ! [X74,X75] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X74),X75) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6041,f3631])).

fof(f6041,plain,
    ( ! [X74,X75] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5680,f3631])).

fof(f5680,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2299,f3631])).

fof(f6040,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_766
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6036,f3630,f1146,f249,f193,f179,f6038,f5763,f5744,f5701])).

fof(f6038,plain,
    ( spl15_766
  <=> ! [X73,X72] : k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X73)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_766])])).

fof(f6036,plain,
    ( ! [X72,X73] :
        ( k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X73)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6035,f3631])).

fof(f6035,plain,
    ( ! [X72,X73] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5679,f3631])).

fof(f5679,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2298,f3631])).

fof(f6034,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_764
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6030,f3630,f1146,f249,f193,f179,f6032,f5763,f5744,f5701])).

fof(f6032,plain,
    ( spl15_764
  <=> ! [X71] : k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X71) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_764])])).

fof(f6030,plain,
    ( ! [X71] :
        ( k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X71) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6029,f3631])).

fof(f6029,plain,
    ( ! [X71] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5678,f3631])).

fof(f5678,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2297,f3631])).

fof(f6028,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_762
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6024,f3630,f1146,f193,f179,f6026,f5763,f5744,f5701])).

fof(f6026,plain,
    ( spl15_762
  <=> ! [X69,X70] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(X69) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_762])])).

fof(f6024,plain,
    ( ! [X70,X69] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6023,f3631])).

fof(f6023,plain,
    ( ! [X70,X69] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5677,f3631])).

fof(f5677,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2296,f3631])).

fof(f6022,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_760
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6018,f3630,f1146,f249,f193,f179,f6020,f5763,f5744,f5701])).

fof(f6020,plain,
    ( spl15_760
  <=> ! [X68] : sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_760])])).

fof(f6018,plain,
    ( ! [X68] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6017,f3631])).

fof(f6017,plain,
    ( ! [X68] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5676,f3631])).

fof(f5676,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2295,f3631])).

fof(f6016,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_758
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6012,f3630,f1146,f249,f193,f179,f6014,f5763,f5744,f5701])).

fof(f6014,plain,
    ( spl15_758
  <=> ! [X67] : k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_758])])).

fof(f6012,plain,
    ( ! [X67] :
        ( k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6011,f3631])).

fof(f6011,plain,
    ( ! [X67] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5675,f3631])).

fof(f5675,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2294,f3631])).

fof(f6010,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_756
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6006,f3630,f1146,f249,f193,f179,f6008,f5763,f5744,f5701])).

fof(f6008,plain,
    ( spl15_756
  <=> ! [X65,X66] : k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_756])])).

fof(f6006,plain,
    ( ! [X66,X65] :
        ( k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f6005,f3631])).

fof(f6005,plain,
    ( ! [X66,X65] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5674,f3631])).

fof(f5674,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2293,f3631])).

fof(f6004,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_754
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f6000,f3630,f1146,f193,f179,f6002,f5763,f5744,f5701])).

fof(f6002,plain,
    ( spl15_754
  <=> ! [X63,X64] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_754])])).

fof(f6000,plain,
    ( ! [X64,X63] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5999,f3631])).

fof(f5999,plain,
    ( ! [X64,X63] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5673,f3631])).

fof(f5673,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2292,f3631])).

fof(f5998,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_752
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5994,f3630,f1146,f249,f193,f179,f5996,f5763,f5744,f5701])).

fof(f5996,plain,
    ( spl15_752
  <=> ! [X62] : k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_752])])).

fof(f5994,plain,
    ( ! [X62] :
        ( k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5993,f3631])).

fof(f5993,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5672,f3631])).

fof(f5672,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2291,f3631])).

fof(f5992,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_750
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5985,f3630,f1146,f249,f193,f179,f5990,f5763,f5744,f5701])).

fof(f5990,plain,
    ( spl15_750
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_750])])).

fof(f5985,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5984,f3631])).

fof(f5984,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5671,f3631])).

fof(f5671,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2290,f3631])).

fof(f5983,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_748
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5979,f3630,f1146,f193,f179,f5981,f5763,f5744,f5701])).

fof(f5981,plain,
    ( spl15_748
  <=> ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_748])])).

fof(f5979,plain,
    ( ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5978,f3631])).

fof(f5978,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5670,f3631])).

fof(f5670,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2289,f3631])).

fof(f5977,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_746
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5970,f3630,f1146,f249,f193,f179,f5975,f5763,f5744,f5701])).

fof(f5975,plain,
    ( spl15_746
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_746])])).

fof(f5970,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5969,f3631])).

fof(f5969,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5669,f3631])).

fof(f5669,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2288,f3631])).

fof(f5968,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_744
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5961,f3630,f1146,f249,f193,f179,f5966,f5763,f5744,f5701])).

fof(f5966,plain,
    ( spl15_744
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_744])])).

fof(f5961,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5960,f3631])).

fof(f5960,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5668,f3631])).

fof(f5668,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2287,f3631])).

fof(f5959,plain,
    ( ~ spl15_689
    | ~ spl15_701
    | ~ spl15_705
    | spl15_742
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5955,f3630,f1146,f193,f179,f5957,f5763,f5744,f5701])).

fof(f5957,plain,
    ( spl15_742
  <=> ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = X60
        | ~ v1_xboole_0(X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_742])])).

fof(f5955,plain,
    ( ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = X60
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5954,f3631])).

fof(f5954,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5667,f3631])).

fof(f5667,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2286,f3631])).

fof(f5953,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_740
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5949,f3630,f1146,f249,f193,f179,f5951,f5763,f5730,f5701])).

fof(f5730,plain,
    ( spl15_697
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_697])])).

fof(f5951,plain,
    ( spl15_740
  <=> ! [X59] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X59))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_740])])).

fof(f5949,plain,
    ( ! [X59] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X59))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5948,f3631])).

fof(f5948,plain,
    ( ! [X59] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5666,f3631])).

fof(f5666,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2285,f3631])).

fof(f5947,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_738
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5943,f3630,f1146,f249,f193,f179,f5945,f5763,f5730,f5701])).

fof(f5945,plain,
    ( spl15_738
  <=> ! [X58] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))),X58) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_738])])).

fof(f5943,plain,
    ( ! [X58] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))),X58) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5942,f3631])).

fof(f5942,plain,
    ( ! [X58] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5665,f3631])).

fof(f5665,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2284,f3631])).

fof(f5941,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_736
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5937,f3630,f1146,f249,f193,f179,f5939,f5763,f5730,f5701])).

fof(f5939,plain,
    ( spl15_736
  <=> ! [X56,X57] : k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))),X57) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_736])])).

fof(f5937,plain,
    ( ! [X57,X56] :
        ( k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))),X57) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5936,f3631])).

fof(f5936,plain,
    ( ! [X57,X56] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5664,f3631])).

fof(f5664,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2283,f3631])).

fof(f5935,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_734
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5931,f3630,f1146,f249,f193,f179,f5933,f5763,f5730,f5701])).

fof(f5933,plain,
    ( spl15_734
  <=> ! [X55,X54] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X54),X55) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_734])])).

fof(f5931,plain,
    ( ! [X54,X55] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X54),X55) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5930,f3631])).

fof(f5930,plain,
    ( ! [X54,X55] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5663,f3631])).

fof(f5663,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2282,f3631])).

fof(f5929,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_732
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5925,f3630,f1146,f249,f193,f179,f5927,f5763,f5730,f5701])).

fof(f5927,plain,
    ( spl15_732
  <=> ! [X53,X52] : k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X53)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_732])])).

fof(f5925,plain,
    ( ! [X52,X53] :
        ( k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X53)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5924,f3631])).

fof(f5924,plain,
    ( ! [X52,X53] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5662,f3631])).

fof(f5662,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2281,f3631])).

fof(f5923,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_730
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5919,f3630,f1146,f249,f193,f179,f5921,f5763,f5730,f5701])).

fof(f5921,plain,
    ( spl15_730
  <=> ! [X51] : k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X51) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_730])])).

fof(f5919,plain,
    ( ! [X51] :
        ( k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),X51) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5918,f3631])).

fof(f5918,plain,
    ( ! [X51] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5661,f3631])).

fof(f5661,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2280,f3631])).

fof(f5917,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_728
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5913,f3630,f1146,f193,f179,f5915,f5763,f5730,f5701])).

fof(f5915,plain,
    ( spl15_728
  <=> ! [X49,X50] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_728])])).

fof(f5913,plain,
    ( ! [X50,X49] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5912,f3631])).

fof(f5912,plain,
    ( ! [X50,X49] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5660,f3631])).

fof(f5660,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2279,f3631])).

fof(f5911,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_726
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5907,f3630,f1146,f249,f193,f179,f5909,f5763,f5730,f5701])).

fof(f5909,plain,
    ( spl15_726
  <=> ! [X48] : sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_726])])).

fof(f5907,plain,
    ( ! [X48] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5906,f3631])).

fof(f5906,plain,
    ( ! [X48] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5659,f3631])).

fof(f5659,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2278,f3631])).

fof(f5905,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_724
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5901,f3630,f1146,f249,f193,f179,f5903,f5763,f5730,f5701])).

fof(f5903,plain,
    ( spl15_724
  <=> ! [X47] : k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_724])])).

fof(f5901,plain,
    ( ! [X47] :
        ( k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5900,f3631])).

fof(f5900,plain,
    ( ! [X47] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5658,f3631])).

fof(f5658,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2277,f3631])).

fof(f5899,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_722
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5895,f3630,f1146,f249,f193,f179,f5897,f5763,f5730,f5701])).

fof(f5897,plain,
    ( spl15_722
  <=> ! [X46,X45] : k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_722])])).

fof(f5895,plain,
    ( ! [X45,X46] :
        ( k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5894,f3631])).

fof(f5894,plain,
    ( ! [X45,X46] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5657,f3631])).

fof(f5657,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2276,f3631])).

fof(f5893,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_720
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5889,f3630,f1146,f193,f179,f5891,f5763,f5730,f5701])).

fof(f5891,plain,
    ( spl15_720
  <=> ! [X44,X43] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_720])])).

fof(f5889,plain,
    ( ! [X43,X44] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5888,f3631])).

fof(f5888,plain,
    ( ! [X43,X44] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5656,f3631])).

fof(f5656,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2275,f3631])).

fof(f5887,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_718
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5883,f3630,f1146,f249,f193,f179,f5885,f5763,f5730,f5701])).

fof(f5885,plain,
    ( spl15_718
  <=> ! [X42] : k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_718])])).

fof(f5883,plain,
    ( ! [X42] :
        ( k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5882,f3631])).

fof(f5882,plain,
    ( ! [X42] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5655,f3631])).

fof(f5655,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2274,f3631])).

fof(f5881,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_716
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5874,f3630,f1146,f249,f193,f179,f5879,f5763,f5730,f5701])).

fof(f5879,plain,
    ( spl15_716
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_716])])).

fof(f5874,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5873,f3631])).

fof(f5873,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5654,f3631])).

fof(f5654,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2273,f3631])).

fof(f5872,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_714
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5868,f3630,f1146,f193,f179,f5870,f5763,f5730,f5701])).

fof(f5870,plain,
    ( spl15_714
  <=> ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_714])])).

fof(f5868,plain,
    ( ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5867,f3631])).

fof(f5867,plain,
    ( ! [X41] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5653,f3631])).

fof(f5653,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2272,f3631])).

fof(f5866,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_712
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5859,f3630,f1146,f249,f193,f179,f5864,f5763,f5730,f5701])).

fof(f5864,plain,
    ( spl15_712
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_712])])).

fof(f5859,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5858,f3631])).

fof(f5858,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5652,f3631])).

fof(f5652,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2271,f3631])).

fof(f5857,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_710
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5850,f3630,f1146,f249,f193,f179,f5855,f5763,f5730,f5701])).

fof(f5855,plain,
    ( spl15_710
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_710])])).

fof(f5850,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5849,f3631])).

fof(f5849,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5651,f3631])).

fof(f5651,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2270,f3631])).

fof(f5848,plain,
    ( ~ spl15_689
    | ~ spl15_697
    | ~ spl15_705
    | spl15_708
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5844,f3630,f1146,f193,f179,f5846,f5763,f5730,f5701])).

fof(f5846,plain,
    ( spl15_708
  <=> ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = X40
        | ~ v1_xboole_0(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_708])])).

fof(f5844,plain,
    ( ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))) = X40
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5843,f3631])).

fof(f5843,plain,
    ( ! [X40] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5650,f3631])).

fof(f5650,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
        | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK4(sK0))) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2269,f3631])).

fof(f5774,plain,
    ( ~ spl15_689
    | spl15_706
    | ~ spl15_701
    | ~ spl15_705
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5767,f3630,f1146,f193,f179,f5763,f5744,f5772,f5701])).

fof(f5767,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5766,f3631])).

fof(f5766,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5615,f3631])).

fof(f5615,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2133,f3631])).

fof(f5765,plain,
    ( ~ spl15_689
    | spl15_702
    | ~ spl15_697
    | ~ spl15_705
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5752,f3630,f1146,f193,f179,f5763,f5730,f5757,f5701])).

fof(f5752,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK4(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5751,f3631])).

fof(f5751,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5614,f3631])).

fof(f5614,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK0)),sK0)
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK4(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2131,f3631])).

fof(f5746,plain,
    ( ~ spl15_689
    | spl15_698
    | ~ spl15_701
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5733,f3630,f1146,f193,f179,f5744,f5738,f5701])).

fof(f5738,plain,
    ( spl15_698
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_698])])).

fof(f5733,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5611,f3631])).

fof(f5611,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2048,f3631])).

fof(f5732,plain,
    ( ~ spl15_689
    | spl15_694
    | ~ spl15_697
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5719,f3630,f1146,f193,f179,f5730,f5724,f5701])).

fof(f5724,plain,
    ( spl15_694
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_694])])).

fof(f5719,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK0)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(forward_demodulation,[],[f5610,f3631])).

fof(f5610,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK0))),k4_waybel_0(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK0)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2047,f3631])).

fof(f5718,plain,
    ( ~ spl15_689
    | spl15_692
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5609,f3630,f1146,f193,f5716,f5701])).

fof(f5609,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2046,f3631])).

fof(f5709,plain,
    ( ~ spl15_689
    | spl15_690
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5606,f3630,f1146,f193,f5707,f5701])).

fof(f5606,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_400 ),
    inference(superposition,[],[f2038,f3631])).

fof(f5696,plain,
    ( ~ spl15_687
    | spl15_183
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f5604,f3630,f1302,f5694])).

fof(f1302,plain,
    ( spl15_183
  <=> ~ r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_183])])).

fof(f5604,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK4(sK0)),sK4(sK0))
    | ~ spl15_183
    | ~ spl15_400 ),
    inference(backward_demodulation,[],[f3631,f1303])).

fof(f1303,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ spl15_183 ),
    inference(avatar_component_clause,[],[f1302])).

fof(f5603,plain,
    ( spl15_684
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_664 ),
    inference(avatar_split_clause,[],[f5588,f5303,f1396,f1146,f193,f179,f5601])).

fof(f5588,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_664 ),
    inference(resolution,[],[f5304,f3584])).

fof(f5541,plain,
    ( spl15_664
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5540,f3615,f1199,f1146,f193,f5303])).

fof(f5540,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5539,f1200])).

fof(f5539,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5538,f1147])).

fof(f5538,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5537,f1147])).

fof(f5537,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5296,f194])).

fof(f5296,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_396 ),
    inference(superposition,[],[f140,f3616])).

fof(f5536,plain,
    ( spl15_674
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5535,f3615,f1199,f1146,f193,f5341])).

fof(f5535,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5534,f1200])).

fof(f5534,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5533,f1147])).

fof(f5533,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5532,f1147])).

fof(f5532,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5295,f194])).

fof(f5295,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_396 ),
    inference(superposition,[],[f2026,f3616])).

fof(f5531,plain,
    ( spl15_670
    | ~ spl15_673
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5530,f3615,f1199,f1146,f193,f5333,f5327])).

fof(f5327,plain,
    ( spl15_670
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_670])])).

fof(f5333,plain,
    ( spl15_673
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_673])])).

fof(f5530,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5529,f3616])).

fof(f5529,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5528,f1200])).

fof(f5528,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5527,f1147])).

fof(f5527,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5293,f194])).

fof(f5293,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_396 ),
    inference(superposition,[],[f2031,f3616])).

fof(f5526,plain,
    ( spl15_666
    | ~ spl15_669
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5525,f3615,f1199,f1146,f193,f5318,f5312])).

fof(f5312,plain,
    ( spl15_666
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_666])])).

fof(f5318,plain,
    ( spl15_669
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_669])])).

fof(f5525,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5524,f3616])).

fof(f5524,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5523,f1200])).

fof(f5523,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5522,f1147])).

fof(f5522,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5292,f194])).

fof(f5292,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_396 ),
    inference(superposition,[],[f2032,f3616])).

fof(f5373,plain,
    ( spl15_680
    | ~ spl15_683
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5360,f3615,f1199,f1146,f193,f179,f5371,f5365])).

fof(f5365,plain,
    ( spl15_680
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_680])])).

fof(f5371,plain,
    ( spl15_683
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_683])])).

fof(f5360,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5359,f3616])).

fof(f5359,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5217,f1200])).

fof(f5217,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2048,f3616])).

fof(f5358,plain,
    ( spl15_676
    | ~ spl15_679
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5345,f3615,f1199,f1146,f193,f179,f5356,f5350])).

fof(f5350,plain,
    ( spl15_676
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_676])])).

fof(f5356,plain,
    ( spl15_679
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_679])])).

fof(f5345,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5344,f3616])).

fof(f5344,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5216,f1200])).

fof(f5216,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2047,f3616])).

fof(f5343,plain,
    ( spl15_674
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5336,f3615,f1199,f1146,f193,f5341])).

fof(f5336,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5215,f1200])).

fof(f5215,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2046,f3616])).

fof(f5335,plain,
    ( spl15_670
    | ~ spl15_673
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5322,f3615,f1199,f1146,f193,f5333,f5327])).

fof(f5322,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5321,f3616])).

fof(f5321,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5214,f1200])).

fof(f5214,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2042,f3616])).

fof(f5320,plain,
    ( spl15_666
    | ~ spl15_669
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5307,f3615,f1199,f1146,f193,f5318,f5312])).

fof(f5307,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK4(sK1)),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(forward_demodulation,[],[f5306,f3616])).

fof(f5306,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5213,f1200])).

fof(f5213,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK4(sK1))),k4_waybel_0(sK0,sK4(sK1)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK4(sK1)),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2041,f3616])).

fof(f5305,plain,
    ( spl15_664
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f5298,f3615,f1199,f1146,f193,f5303])).

fof(f5298,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f5212,f1200])).

fof(f5212,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_396 ),
    inference(superposition,[],[f2038,f3616])).

fof(f5187,plain,
    ( spl15_662
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_492 ),
    inference(avatar_split_clause,[],[f5172,f4484,f1396,f1146,f193,f179,f5185])).

fof(f5172,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_492 ),
    inference(resolution,[],[f4485,f3584])).

fof(f5168,plain,
    ( spl15_660
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_468 ),
    inference(avatar_split_clause,[],[f5153,f4103,f1396,f1146,f193,f179,f5166])).

fof(f5153,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_468 ),
    inference(resolution,[],[f4104,f3584])).

fof(f5144,plain,
    ( ~ spl15_659
    | ~ spl15_0
    | ~ spl15_20
    | spl15_515 ),
    inference(avatar_split_clause,[],[f5137,f4568,f249,f179,f5142])).

fof(f5142,plain,
    ( spl15_659
  <=> ~ v13_waybel_0(sK7,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_659])])).

fof(f4568,plain,
    ( spl15_515
  <=> ~ v1_xboole_0(k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_515])])).

fof(f5137,plain,
    ( ~ v13_waybel_0(sK7,sK0)
    | ~ spl15_0
    | ~ spl15_20
    | ~ spl15_515 ),
    inference(subsumption_resolution,[],[f5136,f180])).

fof(f5136,plain,
    ( ~ v13_waybel_0(sK7,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl15_20
    | ~ spl15_515 ),
    inference(resolution,[],[f4569,f2967])).

fof(f2967,plain,
    ( ! [X2] :
        ( v1_xboole_0(k4_waybel_0(X2,sK7))
        | ~ v13_waybel_0(sK7,X2)
        | ~ l1_orders_2(X2) )
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f2964,f250])).

fof(f2964,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(X2)
        | ~ v13_waybel_0(sK7,X2)
        | v1_xboole_0(k4_waybel_0(X2,sK7))
        | ~ v1_xboole_0(sK7) )
    | ~ spl15_20 ),
    inference(resolution,[],[f726,f378])).

fof(f726,plain,
    ( ! [X1] :
        ( r1_tarski(k4_waybel_0(X1,sK7),sK7)
        | ~ l1_orders_2(X1)
        | ~ v13_waybel_0(sK7,X1) )
    | ~ spl15_20 ),
    inference(resolution,[],[f127,f345])).

fof(f4569,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ spl15_515 ),
    inference(avatar_component_clause,[],[f4568])).

fof(f5134,plain,
    ( ~ spl15_491
    | ~ spl15_4
    | ~ spl15_20
    | spl15_185
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5133,f3660,f1312,f249,f193,f4476])).

fof(f4476,plain,
    ( spl15_491
  <=> ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_491])])).

fof(f1312,plain,
    ( spl15_185
  <=> ~ v13_waybel_0(sK7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_185])])).

fof(f5133,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_185
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5132,f1313])).

fof(f1313,plain,
    ( ~ v13_waybel_0(sK7,sK1)
    | ~ spl15_185 ),
    inference(avatar_component_clause,[],[f1312])).

fof(f5132,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7)
    | v13_waybel_0(sK7,sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5131,f194])).

fof(f5131,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7)
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK7,sK1)
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4471,f345])).

fof(f4471,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK7,sK1)
    | ~ spl15_408 ),
    inference(superposition,[],[f126,f3661])).

fof(f5130,plain,
    ( spl15_492
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5129,f3660,f1146,f249,f193,f4484])).

fof(f5129,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5128,f1147])).

fof(f5128,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5127,f194])).

fof(f5127,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4470,f345])).

fof(f4470,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_408 ),
    inference(superposition,[],[f140,f3661])).

fof(f5126,plain,
    ( spl15_502
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5125,f3660,f1146,f249,f193,f4522])).

fof(f5125,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5124,f1147])).

fof(f5124,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5123,f345])).

fof(f5123,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4469,f194])).

fof(f4469,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_408 ),
    inference(superposition,[],[f2026,f3661])).

fof(f5122,plain,
    ( spl15_498
    | ~ spl15_501
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5121,f3660,f249,f193,f4514,f4508])).

fof(f4508,plain,
    ( spl15_498
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_498])])).

fof(f4514,plain,
    ( spl15_501
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_501])])).

fof(f5121,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5120,f3661])).

fof(f5120,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5119,f345])).

fof(f5119,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4467,f194])).

fof(f4467,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_408 ),
    inference(superposition,[],[f2031,f3661])).

fof(f5118,plain,
    ( spl15_494
    | ~ spl15_497
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5117,f3660,f249,f193,f4499,f4493])).

fof(f4493,plain,
    ( spl15_494
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_494])])).

fof(f4499,plain,
    ( spl15_497
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_497])])).

fof(f5117,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5116,f3661])).

fof(f5116,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f5115,f345])).

fof(f5115,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4466,f194])).

fof(f4466,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_408 ),
    inference(superposition,[],[f2032,f3661])).

fof(f5112,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_656
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5108,f3660,f1146,f249,f193,f179,f5110,f4568,f4552])).

fof(f4552,plain,
    ( spl15_511
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_511])])).

fof(f5110,plain,
    ( spl15_656
  <=> ! [X79] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X79))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_656])])).

fof(f5108,plain,
    ( ! [X79] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X79))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5107,f3661])).

fof(f5107,plain,
    ( ! [X79] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5106,f3661])).

fof(f5106,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4462,f345])).

fof(f4462,plain,
    ( ! [X79] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X79))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2302,f3661])).

fof(f5105,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_654
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5101,f3660,f1146,f249,f193,f179,f5103,f4568,f4552])).

fof(f5103,plain,
    ( spl15_654
  <=> ! [X78] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))),X78) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_654])])).

fof(f5101,plain,
    ( ! [X78] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))),X78) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5100,f3661])).

fof(f5100,plain,
    ( ! [X78] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5099,f3661])).

fof(f5099,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4461,f345])).

fof(f4461,plain,
    ( ! [X78] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X78) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2301,f3661])).

fof(f5098,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_652
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5094,f3660,f1146,f249,f193,f179,f5096,f4568,f4552])).

fof(f5096,plain,
    ( spl15_652
  <=> ! [X77,X76] : k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),X77) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_652])])).

fof(f5094,plain,
    ( ! [X76,X77] :
        ( k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))),X77) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5093,f3661])).

fof(f5093,plain,
    ( ! [X76,X77] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5092,f3661])).

fof(f5092,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4460,f345])).

fof(f4460,plain,
    ( ! [X76,X77] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X76,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X77) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2300,f3661])).

fof(f5091,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_650
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5087,f3660,f1146,f249,f193,f179,f5089,f4568,f4552])).

fof(f5089,plain,
    ( spl15_650
  <=> ! [X75,X74] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X74),X75) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_650])])).

fof(f5087,plain,
    ( ! [X74,X75] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X74),X75) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5086,f3661])).

fof(f5086,plain,
    ( ! [X74,X75] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5085,f3661])).

fof(f5085,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4459,f345])).

fof(f4459,plain,
    ( ! [X74,X75] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X74),X75) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2299,f3661])).

fof(f5084,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_648
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5080,f3660,f1146,f249,f193,f179,f5082,f4568,f4552])).

fof(f5082,plain,
    ( spl15_648
  <=> ! [X73,X72] : k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X73)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_648])])).

fof(f5080,plain,
    ( ! [X72,X73] :
        ( k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X73)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5079,f3661])).

fof(f5079,plain,
    ( ! [X72,X73] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5078,f3661])).

fof(f5078,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4458,f345])).

fof(f4458,plain,
    ( ! [X72,X73] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X72,k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X73)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2298,f3661])).

fof(f5077,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_646
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5073,f3660,f1146,f249,f193,f179,f5075,f4568,f4552])).

fof(f5075,plain,
    ( spl15_646
  <=> ! [X71] : k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X71) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_646])])).

fof(f5073,plain,
    ( ! [X71] :
        ( k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X71) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5072,f3661])).

fof(f5072,plain,
    ( ! [X71] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5071,f3661])).

fof(f5071,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4457,f345])).

fof(f4457,plain,
    ( ! [X71] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X71) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2297,f3661])).

fof(f5070,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_644
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5066,f3660,f1146,f249,f193,f179,f5068,f4568,f4552])).

fof(f5068,plain,
    ( spl15_644
  <=> ! [X69,X70] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X69) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_644])])).

fof(f5066,plain,
    ( ! [X70,X69] :
        ( k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5065,f3661])).

fof(f5065,plain,
    ( ! [X70,X69] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5064,f3661])).

fof(f5064,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4456,f345])).

fof(f4456,plain,
    ( ! [X70,X69] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X69,X70) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X69) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2296,f3661])).

fof(f5063,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_642
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5059,f3660,f1146,f249,f193,f179,f5061,f4568,f4552])).

fof(f5061,plain,
    ( spl15_642
  <=> ! [X68] : sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_642])])).

fof(f5059,plain,
    ( ! [X68] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5058,f3661])).

fof(f5058,plain,
    ( ! [X68] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5057,f3661])).

fof(f5057,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4455,f345])).

fof(f4455,plain,
    ( ! [X68] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X68,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2295,f3661])).

fof(f5056,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_640
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5052,f3660,f1146,f249,f193,f179,f5054,f4568,f4552])).

fof(f5054,plain,
    ( spl15_640
  <=> ! [X67] : k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_640])])).

fof(f5052,plain,
    ( ! [X67] :
        ( k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5051,f3661])).

fof(f5051,plain,
    ( ! [X67] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5050,f3661])).

fof(f5050,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4454,f345])).

fof(f4454,plain,
    ( ! [X67] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X67,sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2294,f3661])).

fof(f5049,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_638
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5045,f3660,f1146,f249,f193,f179,f5047,f4568,f4552])).

fof(f5047,plain,
    ( spl15_638
  <=> ! [X65,X66] : k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_638])])).

fof(f5045,plain,
    ( ! [X66,X65] :
        ( k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5044,f3661])).

fof(f5044,plain,
    ( ! [X66,X65] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5043,f3661])).

fof(f5043,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4453,f345])).

fof(f4453,plain,
    ( ! [X66,X65] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X65,k2_zfmisc_1(X66,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2293,f3661])).

fof(f5042,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_636
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5038,f3660,f1146,f249,f193,f179,f5040,f4568,f4552])).

fof(f5040,plain,
    ( spl15_636
  <=> ! [X63,X64] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_636])])).

fof(f5038,plain,
    ( ! [X64,X63] :
        ( k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5037,f3661])).

fof(f5037,plain,
    ( ! [X64,X63] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5036,f3661])).

fof(f5036,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4452,f345])).

fof(f4452,plain,
    ( ! [X64,X63] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X63,X64) = k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X64) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2292,f3661])).

fof(f5035,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_634
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5031,f3660,f1146,f249,f193,f179,f5033,f4568,f4552])).

fof(f5033,plain,
    ( spl15_634
  <=> ! [X62] : k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_634])])).

fof(f5031,plain,
    ( ! [X62] :
        ( k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK0,sK7))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5030,f3661])).

fof(f5030,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5029,f3661])).

fof(f5029,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4451,f345])).

fof(f4451,plain,
    ( ! [X62] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X62,k4_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2291,f3661])).

fof(f5028,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_632
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5021,f3660,f1146,f249,f193,f179,f5026,f4568,f4552])).

fof(f5026,plain,
    ( spl15_632
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_632])])).

fof(f5021,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5020,f3661])).

fof(f5020,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5019,f3661])).

fof(f5019,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4450,f345])).

fof(f4450,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2290,f3661])).

fof(f5018,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_630
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5014,f3660,f1146,f249,f193,f179,f5016,f4568,f4552])).

fof(f5016,plain,
    ( spl15_630
  <=> ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_630])])).

fof(f5014,plain,
    ( ! [X61] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5013,f3661])).

fof(f5013,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5012,f3661])).

fof(f5012,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4449,f345])).

fof(f4449,plain,
    ( ! [X61] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X61))
        | ~ v1_xboole_0(X61) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2289,f3661])).

fof(f5011,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_628
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f5004,f3660,f1146,f249,f193,f179,f5009,f4568,f4552])).

fof(f5009,plain,
    ( spl15_628
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_628])])).

fof(f5004,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5003,f3661])).

fof(f5003,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f5002,f3661])).

fof(f5002,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4448,f345])).

fof(f4448,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2288,f3661])).

fof(f5001,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_626
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4994,f3660,f1146,f249,f193,f179,f4999,f4568,f4552])).

fof(f4999,plain,
    ( spl15_626
  <=> k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_626])])).

fof(f4994,plain,
    ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4993,f3661])).

fof(f4993,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4992,f3661])).

fof(f4992,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4447,f345])).

fof(f4447,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2287,f3661])).

fof(f4991,plain,
    ( ~ spl15_511
    | ~ spl15_515
    | spl15_624
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4987,f3660,f1146,f249,f193,f179,f4989,f4568,f4552])).

fof(f4989,plain,
    ( spl15_624
  <=> ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = X60
        | ~ v1_xboole_0(X60) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_624])])).

fof(f4987,plain,
    ( ! [X60] :
        ( k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = X60
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4986,f3661])).

fof(f4986,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4985,f3661])).

fof(f4985,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4446,f345])).

fof(f4446,plain,
    ( ! [X60] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X60
        | ~ v1_xboole_0(X60) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2286,f3661])).

fof(f4984,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_622
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4980,f3660,f1146,f249,f193,f179,f4982,f4568,f4537])).

fof(f4537,plain,
    ( spl15_507
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_507])])).

fof(f4982,plain,
    ( spl15_622
  <=> ! [X59] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X59))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_622])])).

fof(f4980,plain,
    ( ! [X59] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X59))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4979,f3661])).

fof(f4979,plain,
    ( ! [X59] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4978,f3661])).

fof(f4978,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4445,f345])).

fof(f4445,plain,
    ( ! [X59] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X59))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2285,f3661])).

fof(f4977,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_620
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4973,f3660,f1146,f249,f193,f179,f4975,f4568,f4537])).

fof(f4975,plain,
    ( spl15_620
  <=> ! [X58] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))),X58) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_620])])).

fof(f4973,plain,
    ( ! [X58] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))),X58) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4972,f3661])).

fof(f4972,plain,
    ( ! [X58] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4971,f3661])).

fof(f4971,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4444,f345])).

fof(f4444,plain,
    ( ! [X58] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))),X58) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2284,f3661])).

fof(f4970,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_618
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4966,f3660,f1146,f249,f193,f179,f4968,f4568,f4537])).

fof(f4968,plain,
    ( spl15_618
  <=> ! [X56,X57] : k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))),X57) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_618])])).

fof(f4966,plain,
    ( ! [X57,X56] :
        ( k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))),X57) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4965,f3661])).

fof(f4965,plain,
    ( ! [X57,X56] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4964,f3661])).

fof(f4964,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4443,f345])).

fof(f4443,plain,
    ( ! [X57,X56] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X56,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))),X57) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2283,f3661])).

fof(f4963,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_616
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4959,f3660,f1146,f249,f193,f179,f4961,f4568,f4537])).

fof(f4961,plain,
    ( spl15_616
  <=> ! [X55,X54] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X54),X55) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_616])])).

fof(f4959,plain,
    ( ! [X54,X55] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X54),X55) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4958,f3661])).

fof(f4958,plain,
    ( ! [X54,X55] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4957,f3661])).

fof(f4957,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4442,f345])).

fof(f4442,plain,
    ( ! [X54,X55] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X54),X55) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2282,f3661])).

fof(f4956,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_614
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4952,f3660,f1146,f249,f193,f179,f4954,f4568,f4537])).

fof(f4954,plain,
    ( spl15_614
  <=> ! [X53,X52] : k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X53)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_614])])).

fof(f4952,plain,
    ( ! [X52,X53] :
        ( k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X53)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4951,f3661])).

fof(f4951,plain,
    ( ! [X52,X53] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4950,f3661])).

fof(f4950,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4441,f345])).

fof(f4441,plain,
    ( ! [X52,X53] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X52,k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X53)) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2281,f3661])).

fof(f4949,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_612
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4945,f3660,f1146,f249,f193,f179,f4947,f4568,f4537])).

fof(f4947,plain,
    ( spl15_612
  <=> ! [X51] : k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X51) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_612])])).

fof(f4945,plain,
    ( ! [X51] :
        ( k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),X51) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4944,f3661])).

fof(f4944,plain,
    ( ! [X51] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4943,f3661])).

fof(f4943,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4440,f345])).

fof(f4440,plain,
    ( ! [X51] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)),X51) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2280,f3661])).

fof(f4942,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_610
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4938,f3660,f1146,f249,f193,f179,f4940,f4568,f4537])).

fof(f4940,plain,
    ( spl15_610
  <=> ! [X49,X50] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_610])])).

fof(f4938,plain,
    ( ! [X50,X49] :
        ( k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4937,f3661])).

fof(f4937,plain,
    ( ! [X50,X49] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4936,f3661])).

fof(f4936,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4439,f345])).

fof(f4439,plain,
    ( ! [X50,X49] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X49,X50) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X49) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2279,f3661])).

fof(f4935,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_608
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4931,f3660,f1146,f249,f193,f179,f4933,f4568,f4537])).

fof(f4933,plain,
    ( spl15_608
  <=> ! [X48] : sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_608])])).

fof(f4931,plain,
    ( ! [X48] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4930,f3661])).

fof(f4930,plain,
    ( ! [X48] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4929,f3661])).

fof(f4929,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4438,f345])).

fof(f4438,plain,
    ( ! [X48] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X48,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2278,f3661])).

fof(f4928,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_606
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4924,f3660,f1146,f249,f193,f179,f4926,f4568,f4537])).

fof(f4926,plain,
    ( spl15_606
  <=> ! [X47] : k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_606])])).

fof(f4924,plain,
    ( ! [X47] :
        ( k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4923,f3661])).

fof(f4923,plain,
    ( ! [X47] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4922,f3661])).

fof(f4922,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4437,f345])).

fof(f4437,plain,
    ( ! [X47] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X47,sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2277,f3661])).

fof(f4921,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_604
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4917,f3660,f1146,f249,f193,f179,f4919,f4568,f4537])).

fof(f4919,plain,
    ( spl15_604
  <=> ! [X46,X45] : k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_604])])).

fof(f4917,plain,
    ( ! [X45,X46] :
        ( k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4916,f3661])).

fof(f4916,plain,
    ( ! [X45,X46] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4915,f3661])).

fof(f4915,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4436,f345])).

fof(f4436,plain,
    ( ! [X45,X46] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X45,k2_zfmisc_1(X46,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2276,f3661])).

fof(f4914,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_602
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4910,f3660,f1146,f249,f193,f179,f4912,f4568,f4537])).

fof(f4912,plain,
    ( spl15_602
  <=> ! [X44,X43] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_602])])).

fof(f4910,plain,
    ( ! [X43,X44] :
        ( k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4909,f3661])).

fof(f4909,plain,
    ( ! [X43,X44] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4908,f3661])).

fof(f4908,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4435,f345])).

fof(f4435,plain,
    ( ! [X43,X44] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X43,X44) = k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X44) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2275,f3661])).

fof(f4907,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_600
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4903,f3660,f1146,f249,f193,f179,f4905,f4568,f4537])).

fof(f4905,plain,
    ( spl15_600
  <=> ! [X42] : k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_600])])).

fof(f4903,plain,
    ( ! [X42] :
        ( k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK0,sK7))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4902,f3661])).

fof(f4902,plain,
    ( ! [X42] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4901,f3661])).

fof(f4901,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4434,f345])).

fof(f4434,plain,
    ( ! [X42] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X42,k3_waybel_0(sK0,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2274,f3661])).

fof(f4900,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_598
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4893,f3660,f1146,f249,f193,f179,f4898,f4568,f4537])).

fof(f4898,plain,
    ( spl15_598
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_598])])).

fof(f4893,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4892,f3661])).

fof(f4892,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4891,f3661])).

fof(f4891,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4433,f345])).

fof(f4433,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2273,f3661])).

fof(f4890,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_596
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4886,f3660,f1146,f249,f193,f179,f4888,f4568,f4537])).

fof(f4888,plain,
    ( spl15_596
  <=> ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_596])])).

fof(f4886,plain,
    ( ! [X41] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4885,f3661])).

fof(f4885,plain,
    ( ! [X41] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4884,f3661])).

fof(f4884,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4432,f345])).

fof(f4432,plain,
    ( ! [X41] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X41))
        | ~ v1_xboole_0(X41) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2272,f3661])).

fof(f4883,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_594
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4876,f3660,f1146,f249,f193,f179,f4881,f4568,f4537])).

fof(f4881,plain,
    ( spl15_594
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_594])])).

fof(f4876,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4875,f3661])).

fof(f4875,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4874,f3661])).

fof(f4874,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4431,f345])).

fof(f4431,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2271,f3661])).

fof(f4873,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_592
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4866,f3660,f1146,f249,f193,f179,f4871,f4568,f4537])).

fof(f4871,plain,
    ( spl15_592
  <=> k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_592])])).

fof(f4866,plain,
    ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4865,f3661])).

fof(f4865,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4864,f3661])).

fof(f4864,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4430,f345])).

fof(f4430,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2270,f3661])).

fof(f4863,plain,
    ( ~ spl15_507
    | ~ spl15_515
    | spl15_590
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4859,f3660,f1146,f249,f193,f179,f4861,f4568,f4537])).

fof(f4861,plain,
    ( spl15_590
  <=> ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = X40
        | ~ v1_xboole_0(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_590])])).

fof(f4859,plain,
    ( ! [X40] :
        ( k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)) = X40
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4858,f3661])).

fof(f4858,plain,
    ( ! [X40] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4857,f3661])).

fof(f4857,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4429,f345])).

fof(f4429,plain,
    ( ! [X40] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK0,k4_waybel_0(sK1,sK7)) = X40
        | ~ v1_xboole_0(X40) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2269,f3661])).

fof(f4856,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_588
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4852,f3660,f1146,f249,f193,f4854,f4568,f4514])).

fof(f4854,plain,
    ( spl15_588
  <=> ! [X39] : sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X39))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_588])])).

fof(f4852,plain,
    ( ! [X39] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X39))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4851,f3661])).

fof(f4851,plain,
    ( ! [X39] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4850,f3661])).

fof(f4850,plain,
    ( ! [X39] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4428,f345])).

fof(f4428,plain,
    ( ! [X39] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X39))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2268,f3661])).

fof(f4849,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_586
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4845,f3660,f1146,f249,f193,f4847,f4568,f4514])).

fof(f4847,plain,
    ( spl15_586
  <=> ! [X38] : k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))),X38) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_586])])).

fof(f4845,plain,
    ( ! [X38] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))),X38) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4844,f3661])).

fof(f4844,plain,
    ( ! [X38] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4843,f3661])).

fof(f4843,plain,
    ( ! [X38] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4427,f345])).

fof(f4427,plain,
    ( ! [X38] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X38) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2267,f3661])).

fof(f4842,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_584
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4838,f3660,f1146,f249,f193,f4840,f4568,f4514])).

fof(f4840,plain,
    ( spl15_584
  <=> ! [X36,X37] : k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))),X37) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_584])])).

fof(f4838,plain,
    ( ! [X37,X36] :
        ( k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))),X37) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4837,f3661])).

fof(f4837,plain,
    ( ! [X37,X36] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4836,f3661])).

fof(f4836,plain,
    ( ! [X37,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4426,f345])).

fof(f4426,plain,
    ( ! [X37,X36] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X36,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X37) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2266,f3661])).

fof(f4835,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_582
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4831,f3660,f1146,f249,f193,f4833,f4568,f4514])).

fof(f4833,plain,
    ( spl15_582
  <=> ! [X34,X35] : k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X34),X35) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_582])])).

fof(f4831,plain,
    ( ! [X35,X34] :
        ( k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X34),X35) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4830,f3661])).

fof(f4830,plain,
    ( ! [X35,X34] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4829,f3661])).

fof(f4829,plain,
    ( ! [X35,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4425,f345])).

fof(f4425,plain,
    ( ! [X35,X34] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X34),X35) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2265,f3661])).

fof(f4828,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_580
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4824,f3660,f1146,f249,f193,f4826,f4568,f4514])).

fof(f4826,plain,
    ( spl15_580
  <=> ! [X32,X33] : k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X33)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_580])])).

fof(f4824,plain,
    ( ! [X33,X32] :
        ( k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X33)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4823,f3661])).

fof(f4823,plain,
    ( ! [X33,X32] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4822,f3661])).

fof(f4822,plain,
    ( ! [X33,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4424,f345])).

fof(f4424,plain,
    ( ! [X33,X32] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X32,k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X33)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2264,f3661])).

fof(f4821,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_578
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4817,f3660,f1146,f249,f193,f4819,f4568,f4514])).

fof(f4819,plain,
    ( spl15_578
  <=> ! [X31] : k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X31) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_578])])).

fof(f4817,plain,
    ( ! [X31] :
        ( k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X31) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4816,f3661])).

fof(f4816,plain,
    ( ! [X31] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4815,f3661])).

fof(f4815,plain,
    ( ! [X31] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4423,f345])).

fof(f4423,plain,
    ( ! [X31] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X31) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2263,f3661])).

fof(f4814,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_576
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4810,f3660,f1146,f249,f193,f4812,f4568,f4514])).

fof(f4812,plain,
    ( spl15_576
  <=> ! [X29,X30] :
        ( k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X29) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_576])])).

fof(f4810,plain,
    ( ! [X30,X29] :
        ( k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4809,f3661])).

fof(f4809,plain,
    ( ! [X30,X29] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4808,f3661])).

fof(f4808,plain,
    ( ! [X30,X29] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4422,f345])).

fof(f4422,plain,
    ( ! [X30,X29] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X29,X30) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X29) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2262,f3661])).

fof(f4807,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_574
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4803,f3660,f1146,f249,f193,f4805,f4568,f4514])).

fof(f4805,plain,
    ( spl15_574
  <=> ! [X28] : sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_574])])).

fof(f4803,plain,
    ( ! [X28] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4802,f3661])).

fof(f4802,plain,
    ( ! [X28] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4801,f3661])).

fof(f4801,plain,
    ( ! [X28] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4421,f345])).

fof(f4421,plain,
    ( ! [X28] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X28,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2261,f3661])).

fof(f4800,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_572
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4796,f3660,f1146,f249,f193,f4798,f4568,f4514])).

fof(f4798,plain,
    ( spl15_572
  <=> ! [X27] : k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_572])])).

fof(f4796,plain,
    ( ! [X27] :
        ( k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4795,f3661])).

fof(f4795,plain,
    ( ! [X27] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4794,f3661])).

fof(f4794,plain,
    ( ! [X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4420,f345])).

fof(f4420,plain,
    ( ! [X27] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X27,sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2260,f3661])).

fof(f4793,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_570
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4789,f3660,f1146,f249,f193,f4791,f4568,f4514])).

fof(f4791,plain,
    ( spl15_570
  <=> ! [X25,X26] : k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_570])])).

fof(f4789,plain,
    ( ! [X26,X25] :
        ( k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4788,f3661])).

fof(f4788,plain,
    ( ! [X26,X25] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4787,f3661])).

fof(f4787,plain,
    ( ! [X26,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4419,f345])).

fof(f4419,plain,
    ( ! [X26,X25] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X25,k2_zfmisc_1(X26,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2259,f3661])).

fof(f4786,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_568
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4782,f3660,f1146,f249,f193,f4784,f4568,f4514])).

fof(f4784,plain,
    ( spl15_568
  <=> ! [X23,X24] :
        ( k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X24) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_568])])).

fof(f4782,plain,
    ( ! [X24,X23] :
        ( k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4781,f3661])).

fof(f4781,plain,
    ( ! [X24,X23] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4780,f3661])).

fof(f4780,plain,
    ( ! [X24,X23] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4418,f345])).

fof(f4418,plain,
    ( ! [X24,X23] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X23,X24) = k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X24) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2258,f3661])).

fof(f4779,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_566
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4775,f3660,f1146,f249,f193,f4777,f4568,f4514])).

fof(f4777,plain,
    ( spl15_566
  <=> ! [X22] : k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_566])])).

fof(f4775,plain,
    ( ! [X22] :
        ( k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4774,f3661])).

fof(f4774,plain,
    ( ! [X22] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4773,f3661])).

fof(f4773,plain,
    ( ! [X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4417,f345])).

fof(f4417,plain,
    ( ! [X22] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X22,k4_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2257,f3661])).

fof(f4772,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_564
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4765,f3660,f1146,f249,f193,f4770,f4568,f4514])).

fof(f4770,plain,
    ( spl15_564
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_564])])).

fof(f4765,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4764,f3661])).

fof(f4764,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4763,f3661])).

fof(f4763,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4416,f345])).

fof(f4416,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2256,f3661])).

fof(f4762,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_562
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4758,f3660,f1146,f249,f193,f4760,f4568,f4514])).

fof(f4760,plain,
    ( spl15_562
  <=> ! [X21] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_562])])).

fof(f4758,plain,
    ( ! [X21] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4757,f3661])).

fof(f4757,plain,
    ( ! [X21] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4756,f3661])).

fof(f4756,plain,
    ( ! [X21] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4415,f345])).

fof(f4415,plain,
    ( ! [X21] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X21))
        | ~ v1_xboole_0(X21) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2255,f3661])).

fof(f4755,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_560
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4748,f3660,f1146,f249,f193,f4753,f4568,f4514])).

fof(f4753,plain,
    ( spl15_560
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_560])])).

fof(f4748,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4747,f3661])).

fof(f4747,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4746,f3661])).

fof(f4746,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4414,f345])).

fof(f4414,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2254,f3661])).

fof(f4745,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_558
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4738,f3660,f1146,f249,f193,f4743,f4568,f4514])).

fof(f4743,plain,
    ( spl15_558
  <=> k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_558])])).

fof(f4738,plain,
    ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4737,f3661])).

fof(f4737,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4736,f3661])).

fof(f4736,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4413,f345])).

fof(f4413,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2253,f3661])).

fof(f4735,plain,
    ( ~ spl15_501
    | ~ spl15_515
    | spl15_556
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4731,f3660,f1146,f249,f193,f4733,f4568,f4514])).

fof(f4733,plain,
    ( spl15_556
  <=> ! [X20] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = X20
        | ~ v1_xboole_0(X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_556])])).

fof(f4731,plain,
    ( ! [X20] :
        ( k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = X20
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4730,f3661])).

fof(f4730,plain,
    ( ! [X20] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4729,f3661])).

fof(f4729,plain,
    ( ! [X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4412,f345])).

fof(f4412,plain,
    ( ! [X20] :
        ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k4_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X20
        | ~ v1_xboole_0(X20) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2252,f3661])).

fof(f4728,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_554
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4724,f3660,f1146,f249,f193,f4726,f4568,f4499])).

fof(f4726,plain,
    ( spl15_554
  <=> ! [X19] : sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X19))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_554])])).

fof(f4724,plain,
    ( ! [X19] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X19))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4723,f3661])).

fof(f4723,plain,
    ( ! [X19] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4722,f3661])).

fof(f4722,plain,
    ( ! [X19] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4411,f345])).

fof(f4411,plain,
    ( ! [X19] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X19))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2250,f3661])).

fof(f4721,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_552
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4717,f3660,f1146,f249,f193,f4719,f4568,f4499])).

fof(f4719,plain,
    ( spl15_552
  <=> ! [X18] : k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))),X18) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_552])])).

fof(f4717,plain,
    ( ! [X18] :
        ( k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))),X18) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4716,f3661])).

fof(f4716,plain,
    ( ! [X18] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4715,f3661])).

fof(f4715,plain,
    ( ! [X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4410,f345])).

fof(f4410,plain,
    ( ! [X18] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))),X18) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2249,f3661])).

fof(f4714,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_550
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4710,f3660,f1146,f249,f193,f4712,f4568,f4499])).

fof(f4712,plain,
    ( spl15_550
  <=> ! [X16,X17] : k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))),X17) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_550])])).

fof(f4710,plain,
    ( ! [X17,X16] :
        ( k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))),X17) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4709,f3661])).

fof(f4709,plain,
    ( ! [X17,X16] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4708,f3661])).

fof(f4708,plain,
    ( ! [X17,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4409,f345])).

fof(f4409,plain,
    ( ! [X17,X16] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(X16,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))),X17) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2248,f3661])).

fof(f4707,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_548
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4703,f3660,f1146,f249,f193,f4705,f4568,f4499])).

fof(f4705,plain,
    ( spl15_548
  <=> ! [X15,X14] : k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X14),X15) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_548])])).

fof(f4703,plain,
    ( ! [X14,X15] :
        ( k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X14),X15) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4702,f3661])).

fof(f4702,plain,
    ( ! [X14,X15] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4701,f3661])).

fof(f4701,plain,
    ( ! [X14,X15] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4408,f345])).

fof(f4408,plain,
    ( ! [X14,X15] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X14),X15) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2247,f3661])).

fof(f4700,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_546
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4696,f3660,f1146,f249,f193,f4698,f4568,f4499])).

fof(f4698,plain,
    ( spl15_546
  <=> ! [X13,X12] : k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X13)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_546])])).

fof(f4696,plain,
    ( ! [X12,X13] :
        ( k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X13)) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4695,f3661])).

fof(f4695,plain,
    ( ! [X12,X13] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4694,f3661])).

fof(f4694,plain,
    ( ! [X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4407,f345])).

fof(f4407,plain,
    ( ! [X12,X13] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X12,k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X13)) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2246,f3661])).

fof(f4693,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_544
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4689,f3660,f1146,f249,f193,f4691,f4568,f4499])).

fof(f4691,plain,
    ( spl15_544
  <=> ! [X11] : k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X11) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_544])])).

fof(f4689,plain,
    ( ! [X11] :
        ( k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),X11) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4688,f3661])).

fof(f4688,plain,
    ( ! [X11] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4687,f3661])).

fof(f4687,plain,
    ( ! [X11] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4406,f345])).

fof(f4406,plain,
    ( ! [X11] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)),X11) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2245,f3661])).

fof(f4686,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_542
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4682,f3660,f1146,f249,f193,f4684,f4568,f4499])).

fof(f4684,plain,
    ( spl15_542
  <=> ! [X9,X10] :
        ( k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_542])])).

fof(f4682,plain,
    ( ! [X10,X9] :
        ( k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4681,f3661])).

fof(f4681,plain,
    ( ! [X10,X9] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4680,f3661])).

fof(f4680,plain,
    ( ! [X10,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4405,f345])).

fof(f4405,plain,
    ( ! [X10,X9] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X9,X10) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X9) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2244,f3661])).

fof(f4679,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_540
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4675,f3660,f1146,f249,f193,f4677,f4568,f4499])).

fof(f4677,plain,
    ( spl15_540
  <=> ! [X8] : sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_540])])).

fof(f4675,plain,
    ( ! [X8] :
        ( sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4674,f3661])).

fof(f4674,plain,
    ( ! [X8] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4673,f3661])).

fof(f4673,plain,
    ( ! [X8] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4404,f345])).

fof(f4404,plain,
    ( ! [X8] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | sK5(k1_zfmisc_1(k2_zfmisc_1(X8,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2243,f3661])).

fof(f4672,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_538
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4668,f3660,f1146,f249,f193,f4670,f4568,f4499])).

fof(f4670,plain,
    ( spl15_538
  <=> ! [X7] : k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_538])])).

fof(f4668,plain,
    ( ! [X7] :
        ( k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4667,f3661])).

fof(f4667,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4666,f3661])).

fof(f4666,plain,
    ( ! [X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4403,f345])).

fof(f4403,plain,
    ( ! [X7] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X7,sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2242,f3661])).

fof(f4665,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_536
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4661,f3660,f1146,f249,f193,f4663,f4568,f4499])).

fof(f4663,plain,
    ( spl15_536
  <=> ! [X5,X6] : k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_536])])).

fof(f4661,plain,
    ( ! [X6,X5] :
        ( k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4660,f3661])).

fof(f4660,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4659,f3661])).

fof(f4659,plain,
    ( ! [X6,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4402,f345])).

fof(f4402,plain,
    ( ! [X6,X5] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X5,k2_zfmisc_1(X6,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2241,f3661])).

fof(f4658,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_534
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4654,f3660,f1146,f249,f193,f4656,f4568,f4499])).

fof(f4656,plain,
    ( spl15_534
  <=> ! [X3,X4] :
        ( k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_534])])).

fof(f4654,plain,
    ( ! [X4,X3] :
        ( k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4653,f3661])).

fof(f4653,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4652,f3661])).

fof(f4652,plain,
    ( ! [X4,X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4401,f345])).

fof(f4401,plain,
    ( ! [X4,X3] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X3,X4) = k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))
        | ~ v1_xboole_0(X4) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2240,f3661])).

fof(f4651,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_532
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4647,f3660,f1146,f249,f193,f4649,f4568,f4499])).

fof(f4649,plain,
    ( spl15_532
  <=> ! [X2] : k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_532])])).

fof(f4647,plain,
    ( ! [X2] :
        ( k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))) = sK7
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4646,f3661])).

fof(f4646,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4645,f3661])).

fof(f4645,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4400,f345])).

fof(f4400,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k2_zfmisc_1(X2,k3_waybel_0(sK1,k4_waybel_0(sK1,sK7))) = sK7 )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2239,f3661])).

fof(f4644,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_530
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4637,f3660,f1146,f249,f193,f4642,f4568,f4499])).

fof(f4642,plain,
    ( spl15_530
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_530])])).

fof(f4637,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4636,f3661])).

fof(f4636,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4635,f3661])).

fof(f4635,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4399,f345])).

fof(f4399,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2238,f3661])).

fof(f4634,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_528
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4630,f3660,f1146,f249,f193,f4632,f4568,f4499])).

fof(f4632,plain,
    ( spl15_528
  <=> ! [X1] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_528])])).

fof(f4630,plain,
    ( ! [X1] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4629,f3661])).

fof(f4629,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4628,f3661])).

fof(f4628,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4398,f345])).

fof(f4398,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK5(k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2237,f3661])).

fof(f4627,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_526
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4620,f3660,f1146,f249,f193,f4625,f4568,f4499])).

fof(f4625,plain,
    ( spl15_526
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_526])])).

fof(f4620,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4619,f3661])).

fof(f4619,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4618,f3661])).

fof(f4618,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4397,f345])).

fof(f4397,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | sK5(k1_zfmisc_1(k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)))) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2236,f3661])).

fof(f4617,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_524
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4610,f3660,f1146,f249,f193,f4615,f4568,f4499])).

fof(f4615,plain,
    ( spl15_524
  <=> k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_524])])).

fof(f4610,plain,
    ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = sK7
    | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4609,f3661])).

fof(f4609,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4608,f3661])).

fof(f4608,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4396,f345])).

fof(f4396,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = sK7
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2235,f3661])).

fof(f4607,plain,
    ( ~ spl15_497
    | ~ spl15_515
    | spl15_522
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4603,f3660,f1146,f249,f193,f4605,f4568,f4499])).

fof(f4605,plain,
    ( spl15_522
  <=> ! [X0] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_522])])).

fof(f4603,plain,
    ( ! [X0] :
        ( k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)) = X0
        | ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4602,f3661])).

fof(f4602,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
        | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4601,f3661])).

fof(f4601,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4395,f345])).

fof(f4395,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
        | k3_waybel_0(sK1,k4_waybel_0(sK1,sK7)) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2234,f3661])).

fof(f4600,plain,
    ( spl15_520
    | ~ spl15_511
    | ~ spl15_515
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4593,f3660,f1146,f249,f193,f179,f4568,f4552,f4598])).

fof(f4593,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4592,f3661])).

fof(f4592,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4591,f3661])).

fof(f4591,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4394,f345])).

fof(f4394,plain,
    ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2133,f3661])).

fof(f4590,plain,
    ( spl15_518
    | ~ spl15_507
    | ~ spl15_515
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4583,f3660,f1146,f249,f193,f179,f4568,f4537,f4588])).

fof(f4583,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4582,f3661])).

fof(f4582,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4581,f3661])).

fof(f4581,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4393,f345])).

fof(f4393,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2131,f3661])).

fof(f4580,plain,
    ( spl15_516
    | ~ spl15_501
    | ~ spl15_515
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4573,f3660,f1146,f249,f193,f4568,f4514,f4578])).

fof(f4578,plain,
    ( spl15_516
  <=> v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_516])])).

fof(f4573,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4572,f3661])).

fof(f4572,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4571,f3661])).

fof(f4571,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4392,f345])).

fof(f4392,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2129,f3661])).

fof(f4570,plain,
    ( spl15_512
    | ~ spl15_497
    | ~ spl15_515
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4557,f3660,f1146,f249,f193,f4568,f4499,f4562])).

fof(f4562,plain,
    ( spl15_512
  <=> v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_512])])).

fof(f4557,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4556,f3661])).

fof(f4556,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4555,f3661])).

fof(f4555,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4391,f345])).

fof(f4391,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k4_waybel_0(sK1,sK7))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2127,f3661])).

fof(f4554,plain,
    ( spl15_508
    | ~ spl15_511
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4541,f3660,f1146,f249,f193,f179,f4552,f4546])).

fof(f4546,plain,
    ( spl15_508
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_508])])).

fof(f4541,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4540,f3661])).

fof(f4540,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4390,f345])).

fof(f4390,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2048,f3661])).

fof(f4539,plain,
    ( spl15_504
    | ~ spl15_507
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4526,f3660,f1146,f249,f193,f179,f4537,f4531])).

fof(f4531,plain,
    ( spl15_504
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_504])])).

fof(f4526,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4525,f3661])).

fof(f4525,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4389,f345])).

fof(f4389,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2047,f3661])).

fof(f4524,plain,
    ( spl15_502
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4517,f3660,f1146,f249,f193,f4522])).

fof(f4517,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4388,f345])).

fof(f4388,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK7),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2046,f3661])).

fof(f4516,plain,
    ( spl15_498
    | ~ spl15_501
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4503,f3660,f1146,f249,f193,f4514,f4508])).

fof(f4503,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4502,f3661])).

fof(f4502,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4387,f345])).

fof(f4387,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2042,f3661])).

fof(f4501,plain,
    ( spl15_494
    | ~ spl15_497
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4488,f3660,f1146,f249,f193,f4499,f4493])).

fof(f4488,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK7),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(forward_demodulation,[],[f4487,f3661])).

fof(f4487,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4386,f345])).

fof(f4386,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK7)),k4_waybel_0(sK0,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK7),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2041,f3661])).

fof(f4486,plain,
    ( spl15_492
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4479,f3660,f1146,f249,f193,f4484])).

fof(f4479,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f4385,f345])).

fof(f4385,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK7),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_408 ),
    inference(superposition,[],[f2038,f3661])).

fof(f4478,plain,
    ( ~ spl15_491
    | spl15_187
    | ~ spl15_408 ),
    inference(avatar_split_clause,[],[f4383,f3660,f1315,f4476])).

fof(f1315,plain,
    ( spl15_187
  <=> ~ r1_tarski(k4_waybel_0(sK1,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_187])])).

fof(f4383,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK7),sK7)
    | ~ spl15_187
    | ~ spl15_408 ),
    inference(backward_demodulation,[],[f3661,f1316])).

fof(f1316,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK7),sK7)
    | ~ spl15_187 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f4352,plain,
    ( ~ spl15_489
    | ~ spl15_4
    | ~ spl15_6
    | spl15_11
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4345,f3608,f1146,f214,f200,f193,f4350])).

fof(f214,plain,
    ( spl15_11
  <=> ~ v13_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f3608,plain,
    ( spl15_394
  <=> k4_waybel_0(sK0,sK3) = k4_waybel_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_394])])).

fof(f4345,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_11
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4344,f201])).

fof(f4344,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ spl15_4
    | ~ spl15_11
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4343,f1147])).

fof(f4343,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_11
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4342,f215])).

fof(f215,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f4342,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v13_waybel_0(sK3,sK1)
    | ~ spl15_4
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4097,f194])).

fof(f4097,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(sK3,sK1)
    | ~ spl15_394 ),
    inference(superposition,[],[f126,f3609])).

fof(f3609,plain,
    ( k4_waybel_0(sK0,sK3) = k4_waybel_0(sK1,sK3)
    | ~ spl15_394 ),
    inference(avatar_component_clause,[],[f3608])).

fof(f4341,plain,
    ( spl15_468
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4340,f3608,f1146,f200,f193,f4103])).

fof(f4340,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4339,f201])).

fof(f4339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4338,f1147])).

fof(f4338,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4337,f1147])).

fof(f4337,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4096,f194])).

fof(f4096,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_394 ),
    inference(superposition,[],[f140,f3609])).

fof(f4336,plain,
    ( spl15_478
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4335,f3608,f1146,f200,f193,f4141])).

fof(f4335,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4334,f201])).

fof(f4334,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4333,f1147])).

fof(f4333,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4332,f1147])).

fof(f4332,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4095,f194])).

fof(f4095,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_394 ),
    inference(superposition,[],[f2026,f3609])).

fof(f4331,plain,
    ( spl15_474
    | ~ spl15_477
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4330,f3608,f1146,f200,f193,f4133,f4127])).

fof(f4127,plain,
    ( spl15_474
  <=> r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_474])])).

fof(f4133,plain,
    ( spl15_477
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_477])])).

fof(f4330,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4329,f3609])).

fof(f4329,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4328,f201])).

fof(f4328,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4327,f1147])).

fof(f4327,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4093,f194])).

fof(f4093,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_394 ),
    inference(superposition,[],[f2031,f3609])).

fof(f4326,plain,
    ( spl15_470
    | ~ spl15_473
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4325,f3608,f1146,f200,f193,f4118,f4112])).

fof(f4112,plain,
    ( spl15_470
  <=> r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_470])])).

fof(f4118,plain,
    ( spl15_473
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_473])])).

fof(f4325,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4324,f3609])).

fof(f4324,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4323,f201])).

fof(f4323,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4322,f1147])).

fof(f4322,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4092,f194])).

fof(f4092,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_394 ),
    inference(superposition,[],[f2032,f3609])).

fof(f4173,plain,
    ( spl15_484
    | ~ spl15_487
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4160,f3608,f1146,f200,f193,f179,f4171,f4165])).

fof(f4165,plain,
    ( spl15_484
  <=> r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_484])])).

fof(f4171,plain,
    ( spl15_487
  <=> ~ v13_waybel_0(k4_waybel_0(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_487])])).

fof(f4160,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK3),sK0)
    | r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4159,f3609])).

fof(f4159,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4019,f201])).

fof(f4019,plain,
    ( r1_tarski(k4_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2048,f3609])).

fof(f4158,plain,
    ( spl15_480
    | ~ spl15_483
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4145,f3608,f1146,f200,f193,f179,f4156,f4150])).

fof(f4150,plain,
    ( spl15_480
  <=> r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_480])])).

fof(f4156,plain,
    ( spl15_483
  <=> ~ v12_waybel_0(k4_waybel_0(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_483])])).

fof(f4145,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK3),sK0)
    | r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4144,f3609])).

fof(f4144,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4018,f201])).

fof(f4018,plain,
    ( r1_tarski(k3_waybel_0(sK0,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2047,f3609])).

fof(f4143,plain,
    ( spl15_478
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4136,f3608,f1146,f200,f193,f4141])).

fof(f4136,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4017,f201])).

fof(f4017,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2046,f3609])).

fof(f4135,plain,
    ( spl15_474
    | ~ spl15_477
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4122,f3608,f1146,f200,f193,f4133,f4127])).

fof(f4122,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4121,f3609])).

fof(f4121,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4016,f201])).

fof(f4016,plain,
    ( r1_tarski(k4_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2042,f3609])).

fof(f4120,plain,
    ( spl15_470
    | ~ spl15_473
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4107,f3608,f1146,f200,f193,f4118,f4112])).

fof(f4107,plain,
    ( ~ v12_waybel_0(k4_waybel_0(sK0,sK3),sK1)
    | r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f4106,f3609])).

fof(f4106,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4015,f201])).

fof(f4015,plain,
    ( r1_tarski(k3_waybel_0(sK1,k4_waybel_0(sK0,sK3)),k4_waybel_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k4_waybel_0(sK1,sK3),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2041,f3609])).

fof(f4105,plain,
    ( spl15_468
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f4098,f3608,f1146,f200,f193,f4103])).

fof(f4098,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(subsumption_resolution,[],[f4014,f201])).

fof(f4014,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_394 ),
    inference(superposition,[],[f2038,f3609])).

fof(f4012,plain,
    ( spl15_170
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f4009,f1254,f1199,f179,f1245])).

fof(f1245,plain,
    ( spl15_170
  <=> v13_waybel_0(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_170])])).

fof(f4009,plain,
    ( v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_172 ),
    inference(subsumption_resolution,[],[f4008,f180])).

fof(f4008,plain,
    ( ~ l1_orders_2(sK0)
    | v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_160
    | ~ spl15_172 ),
    inference(subsumption_resolution,[],[f4006,f1200])).

fof(f4006,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_172 ),
    inference(resolution,[],[f1255,f126])).

fof(f4011,plain,
    ( ~ spl15_0
    | ~ spl15_160
    | spl15_171
    | ~ spl15_172 ),
    inference(avatar_contradiction_clause,[],[f4010])).

fof(f4010,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_160
    | ~ spl15_171
    | ~ spl15_172 ),
    inference(subsumption_resolution,[],[f4009,f1249])).

fof(f1249,plain,
    ( ~ v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_171 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f1248,plain,
    ( spl15_171
  <=> ~ v13_waybel_0(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_171])])).

fof(f4005,plain,
    ( spl15_402
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f3996,f2732,f1396,f1146,f193,f179,f3637])).

fof(f3996,plain,
    ( k4_waybel_0(sK0,sK14(sK1)) = k4_waybel_0(sK1,sK14(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f3584])).

fof(f3995,plain,
    ( spl15_466
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(avatar_split_clause,[],[f3962,f2748,f249,f3993])).

fof(f3993,plain,
    ( spl15_466
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,sK3))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_466])])).

fof(f2748,plain,
    ( spl15_336
  <=> v1_xboole_0(k3_waybel_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_336])])).

fof(f3962,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK0,sK3))))) = sK7
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(resolution,[],[f2749,f446])).

fof(f2749,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,sK3))
    | ~ spl15_336 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f3988,plain,
    ( spl15_464
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(avatar_split_clause,[],[f3960,f2748,f249,f3986])).

fof(f3986,plain,
    ( spl15_464
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK0,sK3))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_464])])).

fof(f3960,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK0,sK3))) = sK7
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(resolution,[],[f2749,f436])).

fof(f3981,plain,
    ( spl15_462
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(avatar_split_clause,[],[f3959,f2748,f249,f3979])).

fof(f3979,plain,
    ( spl15_462
  <=> k3_waybel_0(sK0,sK3) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_462])])).

fof(f3959,plain,
    ( k3_waybel_0(sK0,sK3) = sK7
    | ~ spl15_20
    | ~ spl15_336 ),
    inference(resolution,[],[f2749,f341])).

fof(f3953,plain,
    ( ~ spl15_209
    | spl15_141
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3952,f1396,f1101,f1423])).

fof(f3952,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_141
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1102,f1397])).

fof(f3951,plain,
    ( ~ spl15_157
    | spl15_143
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3950,f1146,f1110,f1184])).

fof(f3950,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_143
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1111,f1147])).

fof(f3949,plain,
    ( spl15_460
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(avatar_split_clause,[],[f3916,f1420,f249,f3947])).

fof(f3947,plain,
    ( spl15_460
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(u1_orders_2(sK0))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_460])])).

fof(f3916,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(u1_orders_2(sK0))))) = sK7
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(resolution,[],[f1421,f446])).

fof(f1421,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_208 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f3942,plain,
    ( spl15_458
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(avatar_split_clause,[],[f3914,f1420,f249,f3940])).

fof(f3940,plain,
    ( spl15_458
  <=> sK5(k1_zfmisc_1(u1_orders_2(sK0))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_458])])).

fof(f3914,plain,
    ( sK5(k1_zfmisc_1(u1_orders_2(sK0))) = sK7
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(resolution,[],[f1421,f436])).

fof(f3935,plain,
    ( spl15_456
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(avatar_split_clause,[],[f3913,f1420,f249,f3933])).

fof(f3933,plain,
    ( spl15_456
  <=> u1_orders_2(sK0) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_456])])).

fof(f3913,plain,
    ( u1_orders_2(sK0) = sK7
    | ~ spl15_20
    | ~ spl15_208 ),
    inference(resolution,[],[f1421,f341])).

fof(f3911,plain,
    ( ~ spl15_57
    | ~ spl15_36
    | spl15_53 ),
    inference(avatar_split_clause,[],[f3910,f390,f310,f406])).

fof(f3910,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_36
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f3909,f311])).

fof(f3909,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl15_53 ),
    inference(resolution,[],[f391,f165])).

fof(f3908,plain,
    ( spl15_454
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f3875,f384,f249,f3906])).

fof(f3875,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))) = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f446])).

fof(f3901,plain,
    ( spl15_452
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f3873,f384,f249,f3899])).

fof(f3873,plain,
    ( sK5(k1_zfmisc_1(sK3)) = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f436])).

fof(f3894,plain,
    ( spl15_450
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f3872,f384,f249,f3892])).

fof(f3872,plain,
    ( sK3 = sK7
    | ~ spl15_20
    | ~ spl15_50 ),
    inference(resolution,[],[f385,f341])).

fof(f3870,plain,
    ( ~ spl15_53
    | spl15_55
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3869,f1146,f397,f390])).

fof(f3869,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_55
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f398,f1147])).

fof(f3868,plain,
    ( spl15_52
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3867,f1146,f394,f387])).

fof(f3867,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f395,f1147])).

fof(f3866,plain,
    ( spl15_208
    | ~ spl15_140
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3865,f1396,f1104,f1420])).

fof(f3865,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_140
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1105,f1397])).

fof(f3864,plain,
    ( spl15_156
    | ~ spl15_142
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3863,f1146,f1107,f1181])).

fof(f3863,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_142
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1108,f1147])).

fof(f3862,plain,
    ( spl15_288
    | ~ spl15_53
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f1985,f1887,f390,f1949])).

fof(f1949,plain,
    ( spl15_288
  <=> v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_288])])).

fof(f1985,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_278 ),
    inference(resolution,[],[f1888,f148])).

fof(f3861,plain,
    ( ~ spl15_53
    | spl15_288
    | ~ spl15_284 ),
    inference(avatar_split_clause,[],[f1947,f1914,f1949,f390])).

fof(f1947,plain,
    ( v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_284 ),
    inference(resolution,[],[f1915,f378])).

fof(f3860,plain,
    ( spl15_288
    | ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3859,f1853,f1731,f390,f1949])).

fof(f1731,plain,
    ( spl15_262
  <=> l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_262])])).

fof(f3859,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1872,f1732])).

fof(f1732,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f1872,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f375,f1854])).

fof(f3858,plain,
    ( spl15_448
    | ~ spl15_289
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f3851,f1887,f1853,f1731,f249,f1952,f3856])).

fof(f3856,plain,
    ( spl15_448
  <=> k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_448])])).

fof(f1952,plain,
    ( spl15_289
  <=> ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_289])])).

fof(f3851,plain,
    ( ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3850,f1732])).

fof(f3850,plain,
    ( ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3122,f1888])).

fof(f3122,plain,
    ( ~ m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2597,f125])).

fof(f2597,plain,
    ( ! [X2] :
        ( ~ v13_waybel_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X2)
        | k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2) = sK7 )
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2525,f341])).

fof(f2525,plain,
    ( ! [X1] :
        ( v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X1))
        | ~ v13_waybel_0(X1,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f1890,f378])).

fof(f1890,plain,
    ( ! [X0] :
        ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1866,f1732])).

fof(f1866,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0),X0)
        | ~ v13_waybel_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_272 ),
    inference(superposition,[],[f127,f1854])).

fof(f3849,plain,
    ( spl15_446
    | ~ spl15_289
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f3842,f1887,f1853,f1731,f249,f1952,f3847])).

fof(f3847,plain,
    ( spl15_446
  <=> k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_446])])).

fof(f3842,plain,
    ( ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3841,f1732])).

fof(f3841,plain,
    ( ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3123,f1888])).

fof(f3123,plain,
    ( ~ m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = sK7
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2615,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v12_waybel_0(sK4(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2615,plain,
    ( ! [X2] :
        ( ~ v12_waybel_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X2)
        | k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2) = sK7 )
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2548,f341])).

fof(f2548,plain,
    ( ! [X1] :
        ( v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X1))
        | ~ v12_waybel_0(X1,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f1891,f378])).

fof(f1891,plain,
    ( ! [X1] :
        ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X1,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1867,f1732])).

fof(f1867,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X1),X1)
        | ~ v12_waybel_0(X1,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_272 ),
    inference(superposition,[],[f129,f1854])).

fof(f3840,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3839,f1396,f1146,f193,f387,f1906])).

fof(f1906,plain,
    ( spl15_283
  <=> ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_283])])).

fof(f3839,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3087,f1147])).

fof(f3087,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3086,f1397])).

fof(f3086,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3075,f194])).

fof(f3075,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f1932,f1147])).

fof(f1932,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f160,f135])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_xboole_0(X0)
      | ~ v2_struct_0(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( v1_orders_2(g1_orders_2(X0,X1))
        & ~ v2_struct_0(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ( v1_orders_2(g1_orders_2(X0,X1))
        & ~ v2_struct_0(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & ~ v1_xboole_0(X0) )
     => ( v1_orders_2(g1_orders_2(X0,X1))
        & ~ v2_struct_0(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',fc1_orders_2)).

fof(f3838,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f3837,f1861,f1853,f1731,f387,f1906])).

fof(f1861,plain,
    ( spl15_274
  <=> u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_274])])).

fof(f3837,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f3089,f1854])).

fof(f3089,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f3088,f1862])).

fof(f1862,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_274 ),
    inference(avatar_component_clause,[],[f1861])).

fof(f3088,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3076,f1732])).

fof(f3076,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f1932,f1854])).

fof(f3836,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3835,f1396,f1146,f193,f387,f1906])).

fof(f3835,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3091,f1147])).

fof(f3091,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3090,f1147])).

fof(f3090,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_4
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3078,f194])).

fof(f3078,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_202 ),
    inference(superposition,[],[f1932,f1397])).

fof(f3834,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f3833,f1861,f1853,f1731,f387,f1906])).

fof(f3833,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f3093,f1854])).

fof(f3093,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f3092,f1854])).

fof(f3092,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_274 ),
    inference(subsumption_resolution,[],[f3079,f1732])).

fof(f3079,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_274 ),
    inference(superposition,[],[f1932,f1862])).

fof(f3832,plain,
    ( spl15_52
    | ~ spl15_283
    | ~ spl15_206 ),
    inference(avatar_split_clause,[],[f3094,f1416,f1906,f387])).

fof(f1416,plain,
    ( spl15_206
  <=> r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_206])])).

fof(f3094,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_206 ),
    inference(resolution,[],[f1937,f1417])).

fof(f1417,plain,
    ( r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_206 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1937,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X3,X3))
      | ~ v2_struct_0(g1_orders_2(X3,X4))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f160,f138])).

fof(f3831,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f2776,f1861,f1853,f1731,f1420,f390])).

fof(f2776,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f2775,f1862])).

fof(f2775,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1873,f1732])).

fof(f1873,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f597,f1854])).

fof(f3830,plain,
    ( spl15_208
    | ~ spl15_53
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1434,f1409,f390,f1420])).

fof(f1409,plain,
    ( spl15_204
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_204])])).

fof(f1434,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_204 ),
    inference(resolution,[],[f1410,f153])).

fof(f1410,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_204 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f3829,plain,
    ( spl15_208
    | ~ spl15_53
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1433,f1409,f390,f1420])).

fof(f1433,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_204 ),
    inference(resolution,[],[f1410,f154])).

fof(f3828,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_206 ),
    inference(avatar_split_clause,[],[f1431,f1416,f1420,f390])).

fof(f1431,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_206 ),
    inference(resolution,[],[f1417,f601])).

fof(f601,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X6,X4))
      | v1_xboole_0(X5)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f153,f138])).

fof(f3827,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_206 ),
    inference(avatar_split_clause,[],[f1430,f1416,f1420,f390])).

fof(f1430,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_206 ),
    inference(resolution,[],[f1417,f837])).

fof(f837,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X4,X6))
      | v1_xboole_0(X5)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f154,f138])).

fof(f3826,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2794,f1396,f1177,f1420,f390])).

fof(f1177,plain,
    ( spl15_154
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_154])])).

fof(f2794,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1267,f1397])).

fof(f1267,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_154 ),
    inference(resolution,[],[f1178,f153])).

fof(f1178,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_154 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f3825,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2797,f1396,f1177,f1420,f390])).

fof(f2797,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1266,f1397])).

fof(f1266,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_154 ),
    inference(resolution,[],[f1178,f154])).

fof(f3824,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2800,f1396,f1191,f1420,f390])).

fof(f1191,plain,
    ( spl15_158
  <=> r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_158])])).

fof(f2800,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1264,f1397])).

fof(f1264,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158 ),
    inference(resolution,[],[f1192,f601])).

fof(f1192,plain,
    ( r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_158 ),
    inference(avatar_component_clause,[],[f1191])).

fof(f3823,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2803,f1396,f1191,f1420,f390])).

fof(f2803,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1263,f1397])).

fof(f1263,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158 ),
    inference(resolution,[],[f1192,f837])).

fof(f3822,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2813,f1396,f1146,f193,f1420,f390])).

fof(f2813,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2812,f1397])).

fof(f2812,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1165,f194])).

fof(f1165,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f597,f1147])).

fof(f3821,plain,
    ( spl15_208
    | ~ spl15_53
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3820,f1396,f1146,f1117,f390,f1420])).

fof(f1117,plain,
    ( spl15_144
  <=> r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_144])])).

fof(f3820,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2822,f1147])).

fof(f2822,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1124,f1397])).

fof(f1124,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144 ),
    inference(resolution,[],[f1118,f601])).

fof(f1118,plain,
    ( r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_144 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f3819,plain,
    ( spl15_208
    | ~ spl15_53
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3818,f1396,f1146,f1117,f390,f1420])).

fof(f3818,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2826,f1147])).

fof(f2826,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1123,f1397])).

fof(f1123,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144 ),
    inference(resolution,[],[f1118,f837])).

fof(f3817,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2835,f1396,f1146,f1072,f1420,f390])).

fof(f1072,plain,
    ( spl15_132
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_132])])).

fof(f2835,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2834,f1397])).

fof(f2834,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_132
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1097,f1147])).

fof(f1097,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_132 ),
    inference(resolution,[],[f1073,f153])).

fof(f1073,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl15_132 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f3816,plain,
    ( ~ spl15_53
    | spl15_208
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f2839,f1396,f1146,f1072,f1420,f390])).

fof(f2839,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f2838,f1397])).

fof(f2838,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_132
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1096,f1147])).

fof(f1096,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_132 ),
    inference(resolution,[],[f1073,f154])).

fof(f3815,plain,
    ( ~ spl15_63
    | spl15_208
    | ~ spl15_4
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3814,f1396,f193,f1420,f433])).

fof(f433,plain,
    ( spl15_63
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_63])])).

fof(f3814,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v2_struct_0(sK1)
    | ~ spl15_4
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f1403,f194])).

fof(f1403,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_202 ),
    inference(superposition,[],[f703,f1397])).

fof(f3813,plain,
    ( ~ spl15_283
    | spl15_208
    | ~ spl15_262
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f3812,f1861,f1731,f1420,f1906])).

fof(f3812,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_274 ),
    inference(subsumption_resolution,[],[f1926,f1732])).

fof(f1926,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_274 ),
    inference(superposition,[],[f703,f1862])).

fof(f3811,plain,
    ( ~ spl15_197
    | spl15_444
    | ~ spl15_212 ),
    inference(avatar_split_clause,[],[f1518,f1456,f3806,f1357])).

fof(f3806,plain,
    ( spl15_444
  <=> v1_xboole_0(k3_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_444])])).

fof(f1456,plain,
    ( spl15_212
  <=> r1_tarski(k3_waybel_0(sK1,sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_212])])).

fof(f1518,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_212 ),
    inference(resolution,[],[f1457,f378])).

fof(f1457,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK4(sK1)),sK4(sK1))
    | ~ spl15_212 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f3810,plain,
    ( ~ spl15_197
    | spl15_198
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162
    | ~ spl15_176 ),
    inference(avatar_split_clause,[],[f3809,f1282,f1211,f1146,f193,f1363,f1357])).

fof(f1211,plain,
    ( spl15_162
  <=> r1_tarski(sK4(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_162])])).

fof(f1282,plain,
    ( spl15_176
  <=> v13_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_176])])).

fof(f3809,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162
    | ~ spl15_176 ),
    inference(subsumption_resolution,[],[f1529,f1283])).

fof(f1283,plain,
    ( v13_waybel_0(sK4(sK1),sK1)
    | ~ spl15_176 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1529,plain,
    ( ~ v13_waybel_0(sK4(sK1),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162 ),
    inference(resolution,[],[f1381,f1212])).

fof(f1212,plain,
    ( r1_tarski(sK4(sK1),u1_struct_0(sK0))
    | ~ spl15_162 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f3808,plain,
    ( ~ spl15_197
    | spl15_444
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162
    | ~ spl15_210 ),
    inference(avatar_split_clause,[],[f3801,f1447,f1211,f1146,f193,f3806,f1357])).

fof(f1447,plain,
    ( spl15_210
  <=> v12_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_210])])).

fof(f3801,plain,
    ( v1_xboole_0(k3_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162
    | ~ spl15_210 ),
    inference(subsumption_resolution,[],[f1594,f1448])).

fof(f1448,plain,
    ( v12_waybel_0(sK4(sK1),sK1)
    | ~ spl15_210 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1594,plain,
    ( ~ v12_waybel_0(sK4(sK1),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_162 ),
    inference(resolution,[],[f1520,f1212])).

fof(f1520,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v12_waybel_0(X1,sK1)
        | v1_xboole_0(k3_waybel_0(sK1,X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1444,f378])).

fof(f1444,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(sK1,X0),X0)
        | ~ v12_waybel_0(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1203,f138])).

fof(f3800,plain,
    ( spl15_196
    | ~ spl15_53
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f1227,f1199,f390,f1354])).

fof(f1354,plain,
    ( spl15_196
  <=> v1_xboole_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_196])])).

fof(f1227,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(sK1))
    | ~ spl15_160 ),
    inference(resolution,[],[f1200,f148])).

fof(f3799,plain,
    ( ~ spl15_53
    | spl15_196
    | ~ spl15_162 ),
    inference(avatar_split_clause,[],[f1222,f1211,f1354,f390])).

fof(f1222,plain,
    ( v1_xboole_0(sK4(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_162 ),
    inference(resolution,[],[f1212,f378])).

fof(f3798,plain,
    ( spl15_196
    | ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3797,f1146,f193,f390,f1354])).

fof(f3797,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(sK1))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1164,f194])).

fof(f1164,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK4(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f375,f1147])).

fof(f3796,plain,
    ( ~ spl15_157
    | spl15_208
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3795,f1396,f1191,f1420,f1184])).

fof(f3795,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1265,f1397])).

fof(f1265,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_158 ),
    inference(resolution,[],[f1192,f378])).

fof(f3794,plain,
    ( ~ spl15_157
    | spl15_208
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3793,f1396,f1177,f1420,f1184])).

fof(f3793,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1268,f1397])).

fof(f1268,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_154 ),
    inference(resolution,[],[f1178,f148])).

fof(f3792,plain,
    ( ~ spl15_157
    | spl15_208
    | ~ spl15_206 ),
    inference(avatar_split_clause,[],[f1432,f1416,f1420,f1184])).

fof(f1432,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_206 ),
    inference(resolution,[],[f1417,f378])).

fof(f3791,plain,
    ( spl15_208
    | ~ spl15_157
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1435,f1409,f1184,f1420])).

fof(f1435,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_204 ),
    inference(resolution,[],[f1410,f148])).

fof(f3790,plain,
    ( ~ spl15_157
    | spl15_208
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3789,f1396,f1146,f193,f1420,f1184])).

fof(f3789,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3788,f1397])).

fof(f3788,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3054,f194])).

fof(f3054,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_150 ),
    inference(superposition,[],[f527,f1147])).

fof(f527,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f135,f148])).

fof(f3787,plain,
    ( ~ spl15_157
    | spl15_208
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f3786,f1861,f1853,f1731,f1420,f1184])).

fof(f3786,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f3785,f1862])).

fof(f3785,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3055,f1732])).

fof(f3055,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_272 ),
    inference(superposition,[],[f527,f1854])).

fof(f3784,plain,
    ( spl15_208
    | ~ spl15_157
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3783,f1396,f1146,f1117,f1184,f1420])).

fof(f3783,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3782,f1147])).

fof(f3782,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_144
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1125,f1397])).

fof(f1125,plain,
    ( v1_xboole_0(u1_orders_2(sK1))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_144 ),
    inference(resolution,[],[f1118,f378])).

fof(f3781,plain,
    ( spl15_56
    | spl15_406
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3647,f1396,f1146,f310,f193,f179,f3653,f403])).

fof(f403,plain,
    ( spl15_56
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_56])])).

fof(f3647,plain,
    ( k4_waybel_0(sK0,sK14(sK0)) = k4_waybel_0(sK1,sK14(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3597,f311])).

fof(f3597,plain,
    ( k4_waybel_0(sK0,sK14(sK0)) = k4_waybel_0(sK1,sK14(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f166])).

fof(f3780,plain,
    ( ~ spl15_53
    | spl15_442
    | ~ spl15_362 ),
    inference(avatar_split_clause,[],[f2957,f2930,f3778,f390])).

fof(f3778,plain,
    ( spl15_442
  <=> v1_xboole_0(sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_442])])).

fof(f2957,plain,
    ( v1_xboole_0(sK14(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_362 ),
    inference(resolution,[],[f2931,f378])).

fof(f2931,plain,
    ( r1_tarski(sK14(sK1),u1_struct_0(sK0))
    | ~ spl15_362 ),
    inference(avatar_component_clause,[],[f2930])).

fof(f3773,plain,
    ( ~ spl15_53
    | spl15_440
    | ~ spl15_380 ),
    inference(avatar_split_clause,[],[f3045,f3033,f3771,f390])).

fof(f3771,plain,
    ( spl15_440
  <=> v1_xboole_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_440])])).

fof(f3045,plain,
    ( v1_xboole_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_380 ),
    inference(resolution,[],[f3034,f378])).

fof(f3766,plain,
    ( spl15_438
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3762,f1146,f193,f179,f390,f3764])).

fof(f3764,plain,
    ( spl15_438
  <=> ! [X2] :
        ( v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_438])])).

fof(f3762,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3233,f180])).

fof(f3233,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2025,f2099])).

fof(f3761,plain,
    ( spl15_436
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3757,f1853,f1731,f179,f390,f3759])).

fof(f3759,plain,
    ( spl15_436
  <=> ! [X3] :
        ( v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_436])])).

fof(f3757,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3234,f180])).

fof(f3234,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2025,f2101])).

fof(f2101,plain,
    ( ! [X2] :
        ( m1_subset_1(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f2100,f1854])).

fof(f2100,plain,
    ( ! [X2] :
        ( m1_subset_1(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2091,f1732])).

fof(f2091,plain,
    ( ! [X2] :
        ( m1_subset_1(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_272 ),
    inference(superposition,[],[f143,f1854])).

fof(f3756,plain,
    ( spl15_434
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3752,f1146,f193,f179,f390,f3754])).

fof(f3754,plain,
    ( spl15_434
  <=> ! [X6] :
        ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_434])])).

fof(f3752,plain,
    ( ! [X6] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3236,f180])).

fof(f3236,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2025,f2038])).

fof(f3751,plain,
    ( spl15_432
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3747,f1853,f1731,f179,f390,f3749])).

fof(f3749,plain,
    ( spl15_432
  <=> ! [X7] :
        ( v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_432])])).

fof(f3747,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3237,f180])).

fof(f3237,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2025,f2040])).

fof(f2040,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f2039,f1854])).

fof(f2039,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2030,f1732])).

fof(f2030,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl15_272 ),
    inference(superposition,[],[f140,f1854])).

fof(f3746,plain,
    ( spl15_430
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f3739,f200,f179,f390,f3744])).

fof(f3739,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f3238,f180])).

fof(f3238,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK3))
    | ~ spl15_6 ),
    inference(resolution,[],[f2025,f201])).

fof(f3738,plain,
    ( spl15_428
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f3731,f1199,f179,f390,f3736])).

fof(f3731,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(subsumption_resolution,[],[f3240,f180])).

fof(f3240,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_160 ),
    inference(resolution,[],[f2025,f1200])).

fof(f3730,plain,
    ( spl15_426
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f3723,f1887,f179,f390,f3728])).

fof(f3728,plain,
    ( spl15_426
  <=> v1_xboole_0(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_426])])).

fof(f3723,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3241,f180])).

fof(f3241,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ spl15_278 ),
    inference(resolution,[],[f2025,f1888])).

fof(f3722,plain,
    ( spl15_344
    | ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3259,f1146,f193,f390,f2767])).

fof(f2767,plain,
    ( spl15_344
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_344])])).

fof(f3259,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f3258,f1147])).

fof(f3258,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3250,f194])).

fof(f3250,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK1)
        | ~ v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(k4_waybel_0(sK1,X1)) )
    | ~ spl15_150 ),
    inference(superposition,[],[f2025,f1147])).

fof(f3721,plain,
    ( spl15_342
    | ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3261,f1853,f1731,f390,f2762])).

fof(f2762,plain,
    ( spl15_342
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_342])])).

fof(f3261,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3260,f1854])).

fof(f3260,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3251,f1732])).

fof(f3251,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_272 ),
    inference(superposition,[],[f2025,f1854])).

fof(f3720,plain,
    ( spl15_424
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3716,f1146,f193,f179,f390,f3718])).

fof(f3718,plain,
    ( spl15_424
  <=> ! [X2] :
        ( v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_424])])).

fof(f3716,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3302,f180])).

fof(f3302,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(sK1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2086,f2099])).

fof(f3715,plain,
    ( spl15_422
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3711,f1853,f1731,f179,f390,f3713])).

fof(f3713,plain,
    ( spl15_422
  <=> ! [X3] :
        ( v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_422])])).

fof(f3711,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3303,f180])).

fof(f3303,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2086,f2101])).

fof(f3710,plain,
    ( spl15_420
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3706,f1146,f193,f179,f390,f3708])).

fof(f3708,plain,
    ( spl15_420
  <=> ! [X6] :
        ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_420])])).

fof(f3706,plain,
    ( ! [X6] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3305,f180])).

fof(f3305,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(sK1,X6)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2086,f2038])).

fof(f3705,plain,
    ( spl15_418
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3701,f1853,f1731,f179,f390,f3703])).

fof(f3703,plain,
    ( spl15_418
  <=> ! [X7] :
        ( v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_418])])).

fof(f3701,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_0
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3306,f180])).

fof(f3306,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK0,k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2086,f2040])).

fof(f3700,plain,
    ( spl15_336
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f3699,f200,f179,f390,f2748])).

fof(f3699,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK3))
    | ~ spl15_0
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f3307,f180])).

fof(f3307,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK3))
    | ~ spl15_6 ),
    inference(resolution,[],[f2086,f201])).

fof(f3698,plain,
    ( spl15_416
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f3691,f1199,f179,f390,f3696])).

fof(f3696,plain,
    ( spl15_416
  <=> v1_xboole_0(k3_waybel_0(sK0,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_416])])).

fof(f3691,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(subsumption_resolution,[],[f3309,f180])).

fof(f3309,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK4(sK1)))
    | ~ spl15_160 ),
    inference(resolution,[],[f2086,f1200])).

fof(f3690,plain,
    ( spl15_414
    | ~ spl15_53
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f3683,f1887,f179,f390,f3688])).

fof(f3688,plain,
    ( spl15_414
  <=> v1_xboole_0(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_414])])).

fof(f3683,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f3310,f180])).

fof(f3310,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ spl15_278 ),
    inference(resolution,[],[f2086,f1888])).

fof(f3682,plain,
    ( spl15_340
    | ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f3328,f1146,f193,f390,f2757])).

fof(f2757,plain,
    ( spl15_340
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_340])])).

fof(f3328,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f3327,f1147])).

fof(f3327,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(k3_waybel_0(sK1,X1)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f3319,f194])).

fof(f3319,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK1)
        | ~ v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(k3_waybel_0(sK1,X1)) )
    | ~ spl15_150 ),
    inference(superposition,[],[f2086,f1147])).

fof(f3681,plain,
    ( spl15_338
    | ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3330,f1853,f1731,f390,f2752])).

fof(f2752,plain,
    ( spl15_338
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_338])])).

fof(f3330,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3329,f1854])).

fof(f3329,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3320,f1732])).

fof(f3320,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2)) )
    | ~ spl15_272 ),
    inference(superposition,[],[f2086,f1854])).

fof(f3680,plain,
    ( ~ spl15_53
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | spl15_317 ),
    inference(avatar_split_clause,[],[f3524,f2535,f1853,f1731,f249,f390])).

fof(f2535,plain,
    ( spl15_317
  <=> ~ v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_317])])).

fof(f3524,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_317 ),
    inference(forward_demodulation,[],[f3523,f1854])).

fof(f3523,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_317 ),
    inference(subsumption_resolution,[],[f3504,f1732])).

fof(f3504,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_317 ),
    inference(resolution,[],[f3245,f2536])).

fof(f2536,plain,
    ( ~ v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_317 ),
    inference(avatar_component_clause,[],[f2535])).

fof(f3679,plain,
    ( ~ spl15_53
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | spl15_321 ),
    inference(avatar_split_clause,[],[f3545,f2558,f1853,f1731,f249,f390])).

fof(f2558,plain,
    ( spl15_321
  <=> ~ v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_321])])).

fof(f3545,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_321 ),
    inference(forward_demodulation,[],[f3544,f1854])).

fof(f3544,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_20
    | ~ spl15_262
    | ~ spl15_321 ),
    inference(subsumption_resolution,[],[f3525,f1732])).

fof(f3525,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_20
    | ~ spl15_321 ),
    inference(resolution,[],[f3314,f2559])).

fof(f2559,plain,
    ( ~ v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_321 ),
    inference(avatar_component_clause,[],[f2558])).

fof(f3314,plain,
    ( ! [X10] :
        ( v1_xboole_0(k3_waybel_0(X10,sK7))
        | ~ v1_xboole_0(u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
    | ~ spl15_20 ),
    inference(resolution,[],[f2086,f345])).

fof(f3678,plain,
    ( spl15_52
    | spl15_410
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3599,f1396,f1146,f193,f179,f3668,f387])).

fof(f3599,plain,
    ( k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f149])).

fof(f3677,plain,
    ( spl15_412
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3601,f1396,f1146,f193,f179,f3675])).

fof(f3601,plain,
    ( k4_waybel_0(sK0,sK5(k1_zfmisc_1(u1_struct_0(sK0)))) = k4_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f130])).

fof(f3670,plain,
    ( spl15_410
    | ~ spl15_0
    | ~ spl15_4
    | spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3663,f1396,f1146,f390,f193,f179,f3668])).

fof(f3663,plain,
    ( k4_waybel_0(sK0,sK10(u1_struct_0(sK0))) = k4_waybel_0(sK1,sK10(u1_struct_0(sK0)))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_53
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3599,f391])).

fof(f3662,plain,
    ( spl15_408
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3598,f1396,f1146,f249,f193,f179,f3660])).

fof(f3598,plain,
    ( k4_waybel_0(sK0,sK7) = k4_waybel_0(sK1,sK7)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f345])).

fof(f3655,plain,
    ( spl15_406
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | spl15_57
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3648,f1396,f1146,f406,f310,f193,f179,f3653])).

fof(f3648,plain,
    ( k4_waybel_0(sK0,sK14(sK0)) = k4_waybel_0(sK1,sK14(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_57
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3647,f407])).

fof(f3646,plain,
    ( spl15_404
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f3596,f2741,f1396,f1146,f193,f179,f3644])).

fof(f3596,plain,
    ( k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_334 ),
    inference(resolution,[],[f3584,f2742])).

fof(f3639,plain,
    ( spl15_402
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f3595,f2732,f1396,f1146,f193,f179,f3637])).

fof(f3595,plain,
    ( k4_waybel_0(sK0,sK14(sK1)) = k4_waybel_0(sK1,sK14(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_332 ),
    inference(resolution,[],[f3584,f2733])).

fof(f3632,plain,
    ( spl15_400
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3625,f1396,f1146,f193,f179,f3630])).

fof(f3625,plain,
    ( k4_waybel_0(sK0,sK4(sK0)) = k4_waybel_0(sK1,sK4(sK0))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3594,f180])).

fof(f3594,plain,
    ( k4_waybel_0(sK0,sK4(sK0)) = k4_waybel_0(sK1,sK4(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f123])).

fof(f3624,plain,
    ( spl15_398
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f3593,f1887,f1396,f1146,f193,f179,f3622])).

fof(f3593,plain,
    ( k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = k4_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_278 ),
    inference(resolution,[],[f3584,f1888])).

fof(f3617,plain,
    ( spl15_396
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3592,f1396,f1199,f1146,f193,f179,f3615])).

fof(f3592,plain,
    ( k4_waybel_0(sK0,sK4(sK1)) = k4_waybel_0(sK1,sK4(sK1))
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f1200])).

fof(f3610,plain,
    ( spl15_394
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3591,f1396,f1146,f200,f193,f179,f3608])).

fof(f3591,plain,
    ( k4_waybel_0(sK0,sK3) = k4_waybel_0(sK1,sK3)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(resolution,[],[f3584,f201])).

fof(f3578,plain,
    ( ~ spl15_391
    | spl15_392
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3577,f1396,f1146,f643,f631,f468,f277,f193,f3566,f3563])).

fof(f3563,plain,
    ( spl15_391
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_391])])).

fof(f3566,plain,
    ( spl15_392
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_392])])).

fof(f277,plain,
    ( spl15_28
  <=> l1_orders_2(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f468,plain,
    ( spl15_66
  <=> u1_struct_0(sK11) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).

fof(f631,plain,
    ( spl15_96
  <=> u1_orders_2(sK11) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f643,plain,
    ( spl15_98
  <=> g1_orders_2(sK7,sK7) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_98])])).

fof(f3577,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3576,f469])).

fof(f469,plain,
    ( u1_struct_0(sK11) = sK7
    | ~ spl15_66 ),
    inference(avatar_component_clause,[],[f468])).

fof(f3576,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3575,f644])).

fof(f644,plain,
    ( g1_orders_2(sK7,sK7) = sK11
    | ~ spl15_98 ),
    inference(avatar_component_clause,[],[f643])).

fof(f3575,plain,
    ( ! [X0] :
        ( g1_orders_2(sK7,sK7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3574,f469])).

fof(f3574,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK11),sK7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_96
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3549,f278])).

fof(f278,plain,
    ( l1_orders_2(sK11)
    | ~ spl15_28 ),
    inference(avatar_component_clause,[],[f277])).

fof(f3549,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK11),sK7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK11)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_96
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(superposition,[],[f2325,f632])).

fof(f632,plain,
    ( u1_orders_2(sK11) = sK7
    | ~ spl15_96 ),
    inference(avatar_component_clause,[],[f631])).

fof(f3568,plain,
    ( ~ spl15_391
    | spl15_392
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f3558,f1396,f1146,f643,f631,f468,f277,f193,f3566,f3563])).

fof(f3558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3557,f469])).

fof(f3557,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_98
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3556,f644])).

fof(f3556,plain,
    ( ! [X0] :
        ( g1_orders_2(sK7,sK7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_96
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f3555,f632])).

fof(f3555,plain,
    ( ! [X0] :
        ( g1_orders_2(sK7,u1_orders_2(sK11)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_28
    | ~ spl15_66
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f3546,f278])).

fof(f3546,plain,
    ( ! [X0] :
        ( g1_orders_2(sK7,u1_orders_2(sK11)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK11)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | k4_waybel_0(sK1,X0) = k4_waybel_0(sK11,X0) )
    | ~ spl15_4
    | ~ spl15_66
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(superposition,[],[f2325,f469])).

fof(f3429,plain,
    ( spl15_386
    | ~ spl15_389
    | spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3416,f1853,f1731,f390,f3427,f3421])).

fof(f3421,plain,
    ( spl15_386
  <=> r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_386])])).

fof(f3427,plain,
    ( spl15_389
  <=> ~ v12_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_389])])).

fof(f3416,plain,
    ( ~ v12_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3415,f391])).

fof(f3415,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v12_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3414,f1854])).

fof(f3414,plain,
    ( ~ v12_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3413,f1854])).

fof(f3413,plain,
    ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3405,f1732])).

fof(f3405,plain,
    ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_272 ),
    inference(superposition,[],[f951,f1854])).

fof(f951,plain,(
    ! [X2] :
      ( r1_tarski(k3_waybel_0(X2,sK10(u1_struct_0(X2))),sK10(u1_struct_0(X2)))
      | ~ l1_orders_2(X2)
      | ~ v12_waybel_0(sK10(u1_struct_0(X2)),X2)
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(resolution,[],[f129,f149])).

fof(f3398,plain,
    ( spl15_382
    | ~ spl15_385
    | spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f3385,f1853,f1731,f390,f3396,f3390])).

fof(f3390,plain,
    ( spl15_382
  <=> r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_382])])).

fof(f3396,plain,
    ( spl15_385
  <=> ~ v13_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_385])])).

fof(f3385,plain,
    ( ~ v13_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3384,f391])).

fof(f3384,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v13_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3383,f1854])).

fof(f3383,plain,
    ( ~ v13_waybel_0(sK10(u1_struct_0(sK0)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f3382,f1854])).

fof(f3382,plain,
    ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f3374,f1732])).

fof(f3374,plain,
    ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_272 ),
    inference(superposition,[],[f727,f1854])).

fof(f727,plain,(
    ! [X2] :
      ( r1_tarski(k4_waybel_0(X2,sK10(u1_struct_0(X2))),sK10(u1_struct_0(X2)))
      | ~ l1_orders_2(X2)
      | ~ v13_waybel_0(sK10(u1_struct_0(X2)),X2)
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(resolution,[],[f127,f149])).

fof(f3035,plain,
    ( spl15_380
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f2974,f2741,f3033])).

fof(f2974,plain,
    ( r1_tarski(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f139])).

fof(f3028,plain,
    ( ~ spl15_377
    | spl15_378
    | ~ spl15_0
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f3015,f2741,f179,f3026,f3020])).

fof(f3020,plain,
    ( spl15_377
  <=> ~ v13_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_377])])).

fof(f3026,plain,
    ( spl15_378
  <=> r1_tarski(k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_378])])).

fof(f3015,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v13_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_334 ),
    inference(subsumption_resolution,[],[f2972,f180])).

fof(f2972,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v13_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f127])).

fof(f3014,plain,
    ( ~ spl15_373
    | spl15_374
    | ~ spl15_0
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f3001,f2741,f179,f3012,f3006])).

fof(f3006,plain,
    ( spl15_373
  <=> ~ v12_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_373])])).

fof(f3012,plain,
    ( spl15_374
  <=> r1_tarski(k3_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_374])])).

fof(f3001,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v12_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_334 ),
    inference(subsumption_resolution,[],[f2971,f180])).

fof(f2971,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v12_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f129])).

fof(f3000,plain,
    ( ~ spl15_369
    | spl15_370
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f2970,f2741,f1146,f193,f2998,f2992])).

fof(f2992,plain,
    ( spl15_369
  <=> ~ v13_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_369])])).

fof(f2998,plain,
    ( spl15_370
  <=> r1_tarski(k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_370])])).

fof(f2970,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v13_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f1202])).

fof(f2987,plain,
    ( ~ spl15_365
    | spl15_366
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_334 ),
    inference(avatar_split_clause,[],[f2969,f2741,f1146,f193,f2985,f2979])).

fof(f2979,plain,
    ( spl15_365
  <=> ~ v12_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_365])])).

fof(f2985,plain,
    ( spl15_366
  <=> r1_tarski(k3_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_366])])).

fof(f2969,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v12_waybel_0(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_334 ),
    inference(resolution,[],[f2742,f1203])).

fof(f2932,plain,
    ( spl15_362
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2871,f2732,f2930])).

fof(f2871,plain,
    ( r1_tarski(sK14(sK1),u1_struct_0(sK0))
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f139])).

fof(f2925,plain,
    ( ~ spl15_359
    | spl15_360
    | ~ spl15_0
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2912,f2732,f179,f2923,f2917])).

fof(f2917,plain,
    ( spl15_359
  <=> ~ v13_waybel_0(sK14(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_359])])).

fof(f2923,plain,
    ( spl15_360
  <=> r1_tarski(k4_waybel_0(sK0,sK14(sK1)),sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_360])])).

fof(f2912,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK14(sK1)),sK14(sK1))
    | ~ v13_waybel_0(sK14(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_332 ),
    inference(subsumption_resolution,[],[f2869,f180])).

fof(f2869,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK14(sK1)),sK14(sK1))
    | ~ v13_waybel_0(sK14(sK1),sK0)
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f127])).

fof(f2911,plain,
    ( ~ spl15_355
    | spl15_356
    | ~ spl15_0
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2898,f2732,f179,f2909,f2903])).

fof(f2903,plain,
    ( spl15_355
  <=> ~ v12_waybel_0(sK14(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_355])])).

fof(f2909,plain,
    ( spl15_356
  <=> r1_tarski(k3_waybel_0(sK0,sK14(sK1)),sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_356])])).

fof(f2898,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK14(sK1)),sK14(sK1))
    | ~ v12_waybel_0(sK14(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_332 ),
    inference(subsumption_resolution,[],[f2868,f180])).

fof(f2868,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK14(sK1)),sK14(sK1))
    | ~ v12_waybel_0(sK14(sK1),sK0)
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f129])).

fof(f2897,plain,
    ( ~ spl15_351
    | spl15_352
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2867,f2732,f1146,f193,f2895,f2889])).

fof(f2889,plain,
    ( spl15_351
  <=> ~ v13_waybel_0(sK14(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_351])])).

fof(f2895,plain,
    ( spl15_352
  <=> r1_tarski(k4_waybel_0(sK1,sK14(sK1)),sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_352])])).

fof(f2867,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK14(sK1)),sK14(sK1))
    | ~ v13_waybel_0(sK14(sK1),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f1202])).

fof(f2884,plain,
    ( ~ spl15_347
    | spl15_348
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2866,f2732,f1146,f193,f2882,f2876])).

fof(f2876,plain,
    ( spl15_347
  <=> ~ v12_waybel_0(sK14(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_347])])).

fof(f2882,plain,
    ( spl15_348
  <=> r1_tarski(k3_waybel_0(sK1,sK14(sK1)),sK14(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_348])])).

fof(f2866,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK14(sK1)),sK14(sK1))
    | ~ v12_waybel_0(sK14(sK1),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_332 ),
    inference(resolution,[],[f2733,f1203])).

fof(f2864,plain,
    ( ~ spl15_53
    | spl15_55
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2863,f1146,f397,f390])).

fof(f2863,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_55
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f398,f1147])).

fof(f2862,plain,
    ( spl15_52
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2861,f1146,f394,f387])).

fof(f2861,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_54
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f395,f1147])).

fof(f2860,plain,
    ( ~ spl15_283
    | spl15_209
    | ~ spl15_262
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f2859,f1861,f1731,f1423,f1906])).

fof(f2859,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_209
    | ~ spl15_262
    | ~ spl15_274 ),
    inference(subsumption_resolution,[],[f2858,f1732])).

fof(f2858,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_209
    | ~ spl15_274 ),
    inference(subsumption_resolution,[],[f1926,f1424])).

fof(f1424,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_209 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f2857,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1933,f1409,f387,f1906])).

fof(f1933,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_204 ),
    inference(resolution,[],[f160,f1410])).

fof(f2856,plain,
    ( ~ spl15_283
    | ~ spl15_262
    | spl15_289 ),
    inference(avatar_split_clause,[],[f2855,f1952,f1731,f1906])).

fof(f2855,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_289 ),
    inference(subsumption_resolution,[],[f1980,f1732])).

fof(f1980,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_289 ),
    inference(resolution,[],[f1953,f458])).

fof(f1953,plain,
    ( ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_289 ),
    inference(avatar_component_clause,[],[f1952])).

fof(f2854,plain,
    ( spl15_282
    | spl15_334
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2735,f1853,f1815,f2741,f1903])).

fof(f2735,plain,
    ( m1_subset_1(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2693,f1816])).

fof(f2693,plain,
    ( m1_subset_1(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f166,f1854])).

fof(f2853,plain,
    ( ~ spl15_63
    | ~ spl15_4
    | spl15_141 ),
    inference(avatar_split_clause,[],[f2852,f1101,f193,f433])).

fof(f2852,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl15_4
    | ~ spl15_141 ),
    inference(subsumption_resolution,[],[f1120,f194])).

fof(f1120,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_141 ),
    inference(resolution,[],[f1102,f703])).

fof(f2851,plain,
    ( ~ spl15_63
    | spl15_52
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2850,f1146,f317,f387,f433])).

fof(f2850,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(sK1)
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1161,f318])).

fof(f1161,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f165,f1147])).

fof(f2849,plain,
    ( ~ spl15_63
    | ~ spl15_4
    | spl15_197 ),
    inference(avatar_split_clause,[],[f2848,f1357,f193,f433])).

fof(f2848,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl15_4
    | ~ spl15_197 ),
    inference(subsumption_resolution,[],[f1366,f194])).

fof(f1366,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_197 ),
    inference(resolution,[],[f1358,f458])).

fof(f1358,plain,
    ( ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_197 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f2847,plain,
    ( ~ spl15_63
    | ~ spl15_4
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2846,f1423,f1396,f193,f433])).

fof(f2846,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl15_4
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2845,f194])).

fof(f2845,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f1403,f1424])).

fof(f2844,plain,
    ( spl15_62
    | spl15_332
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2726,f1146,f317,f2732,f430])).

fof(f2726,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2692,f318])).

fof(f2692,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f166,f1147])).

fof(f2843,plain,
    ( spl15_50
    | ~ spl15_53
    | ~ spl15_48
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2842,f1146,f365,f390,f384])).

fof(f365,plain,
    ( spl15_48
  <=> r1_tarski(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f2842,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | ~ spl15_48
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f439,f1147])).

fof(f439,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_48 ),
    inference(resolution,[],[f378,f366])).

fof(f366,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl15_48 ),
    inference(avatar_component_clause,[],[f365])).

fof(f2841,plain,
    ( ~ spl15_53
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2840,f1423,f1396,f1146,f1072,f390])).

fof(f2840,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2839,f1424])).

fof(f2837,plain,
    ( ~ spl15_53
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2836,f1423,f1396,f1146,f1072,f390])).

fof(f2836,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_132
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2835,f1424])).

fof(f2833,plain,
    ( ~ spl15_53
    | spl15_143
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2832,f1146,f1110,f390])).

fof(f2832,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_143
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1121,f1147])).

fof(f1121,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_143 ),
    inference(resolution,[],[f1111,f841])).

fof(f2831,plain,
    ( ~ spl15_53
    | spl15_143
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2830,f1146,f1110,f390])).

fof(f2830,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_143
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1122,f1147])).

fof(f1122,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_143 ),
    inference(resolution,[],[f1111,f606])).

fof(f2829,plain,
    ( ~ spl15_53
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2828,f1423,f1396,f1146,f1117,f390])).

fof(f2828,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(forward_demodulation,[],[f2827,f1147])).

fof(f2827,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2826,f1424])).

fof(f2825,plain,
    ( ~ spl15_53
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2824,f1423,f1396,f1146,f1117,f390])).

fof(f2824,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_144
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(forward_demodulation,[],[f2823,f1147])).

fof(f2823,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl15_144
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2822,f1424])).

fof(f2821,plain,
    ( ~ spl15_53
    | spl15_50
    | ~ spl15_46 ),
    inference(avatar_split_clause,[],[f438,f358,f384,f390])).

fof(f438,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_46 ),
    inference(resolution,[],[f378,f359])).

fof(f2820,plain,
    ( spl15_62
    | ~ spl15_53
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2819,f1146,f317,f390,f430])).

fof(f2819,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ spl15_38
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1162,f318])).

fof(f1162,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f168,f1147])).

fof(f168,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',fc2_struct_0)).

fof(f2818,plain,
    ( ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150
    | spl15_197 ),
    inference(avatar_split_clause,[],[f2817,f1357,f1146,f193,f390])).

fof(f2817,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_197 ),
    inference(subsumption_resolution,[],[f2816,f194])).

fof(f2816,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150
    | ~ spl15_197 ),
    inference(subsumption_resolution,[],[f1164,f1358])).

fof(f2815,plain,
    ( ~ spl15_53
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2814,f1423,f1396,f1146,f193,f390])).

fof(f2814,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2813,f1424])).

fof(f2811,plain,
    ( ~ spl15_53
    | ~ spl15_162
    | spl15_197 ),
    inference(avatar_split_clause,[],[f2810,f1357,f1211,f390])).

fof(f2810,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_162
    | ~ spl15_197 ),
    inference(subsumption_resolution,[],[f1222,f1358])).

fof(f2809,plain,
    ( ~ spl15_53
    | spl15_157 ),
    inference(avatar_split_clause,[],[f1223,f1184,f390])).

fof(f1223,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_157 ),
    inference(resolution,[],[f1185,f841])).

fof(f2808,plain,
    ( ~ spl15_53
    | spl15_157 ),
    inference(avatar_split_clause,[],[f1224,f1184,f390])).

fof(f1224,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_157 ),
    inference(resolution,[],[f1185,f606])).

fof(f2807,plain,
    ( ~ spl15_53
    | ~ spl15_160
    | spl15_197 ),
    inference(avatar_split_clause,[],[f2806,f1357,f1199,f390])).

fof(f2806,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_160
    | ~ spl15_197 ),
    inference(subsumption_resolution,[],[f1227,f1358])).

fof(f2805,plain,
    ( ~ spl15_53
    | ~ spl15_158
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2804,f1423,f1396,f1191,f390])).

fof(f2804,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2803,f1424])).

fof(f2802,plain,
    ( ~ spl15_53
    | ~ spl15_158
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2801,f1423,f1396,f1191,f390])).

fof(f2801,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_158
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2800,f1424])).

fof(f2799,plain,
    ( ~ spl15_53
    | ~ spl15_154
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2798,f1423,f1396,f1177,f390])).

fof(f2798,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_154
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2797,f1424])).

fof(f2796,plain,
    ( ~ spl15_53
    | ~ spl15_154
    | ~ spl15_202
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2795,f1423,f1396,f1177,f390])).

fof(f2795,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_154
    | ~ spl15_202
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f2794,f1424])).

fof(f2793,plain,
    ( ~ spl15_53
    | ~ spl15_206
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2792,f1423,f1416,f390])).

fof(f2792,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_206
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f1430,f1424])).

fof(f2791,plain,
    ( ~ spl15_53
    | ~ spl15_206
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2790,f1423,f1416,f390])).

fof(f2790,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_206
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f1431,f1424])).

fof(f2789,plain,
    ( ~ spl15_53
    | ~ spl15_204
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2788,f1423,f1409,f390])).

fof(f2788,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_204
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f1433,f1424])).

fof(f2787,plain,
    ( ~ spl15_53
    | ~ spl15_204
    | spl15_209 ),
    inference(avatar_split_clause,[],[f2786,f1423,f1409,f390])).

fof(f2786,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_204
    | ~ spl15_209 ),
    inference(subsumption_resolution,[],[f1434,f1424])).

fof(f2785,plain,
    ( ~ spl15_283
    | spl15_52
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2784,f1853,f1815,f387,f1906])).

fof(f2784,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1869,f1816])).

fof(f1869,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f165,f1854])).

fof(f2783,plain,
    ( spl15_282
    | ~ spl15_53
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2782,f1853,f1815,f390,f1903])).

fof(f2782,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1870,f1816])).

fof(f1870,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f168,f1854])).

fof(f2781,plain,
    ( ~ spl15_53
    | ~ spl15_262
    | ~ spl15_272
    | spl15_289 ),
    inference(avatar_split_clause,[],[f2780,f1952,f1853,f1731,f390])).

fof(f2780,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_289 ),
    inference(subsumption_resolution,[],[f2779,f1732])).

fof(f2779,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272
    | ~ spl15_289 ),
    inference(subsumption_resolution,[],[f1872,f1953])).

fof(f2778,plain,
    ( ~ spl15_53
    | spl15_209
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f2777,f1861,f1853,f1731,f1423,f390])).

fof(f2777,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_209
    | ~ spl15_262
    | ~ spl15_272
    | ~ spl15_274 ),
    inference(subsumption_resolution,[],[f2776,f1424])).

fof(f2774,plain,
    ( ~ spl15_53
    | ~ spl15_284
    | spl15_289 ),
    inference(avatar_split_clause,[],[f2773,f1952,f1914,f390])).

fof(f2773,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_284
    | ~ spl15_289 ),
    inference(subsumption_resolution,[],[f1947,f1953])).

fof(f2772,plain,
    ( ~ spl15_53
    | ~ spl15_278
    | spl15_289 ),
    inference(avatar_split_clause,[],[f2771,f1952,f1887,f390])).

fof(f2771,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_278
    | ~ spl15_289 ),
    inference(subsumption_resolution,[],[f1985,f1953])).

fof(f2770,plain,
    ( ~ spl15_53
    | spl15_344
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2045,f1146,f193,f2767,f390])).

fof(f2045,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(sK1,X4)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2038,f148])).

fof(f2769,plain,
    ( ~ spl15_53
    | spl15_344
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2052,f1146,f193,f2767,f390])).

fof(f2052,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(sK1,X2))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2046,f378])).

fof(f2765,plain,
    ( ~ spl15_53
    | spl15_342
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2069,f1853,f1731,f2762,f390])).

fof(f2069,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2040,f148])).

fof(f2764,plain,
    ( ~ spl15_53
    | spl15_342
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2076,f1853,f1731,f2762,f390])).

fof(f2076,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2070,f378])).

fof(f2070,plain,
    ( ! [X5] :
        ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2040,f139])).

fof(f2760,plain,
    ( ~ spl15_53
    | spl15_340
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2106,f1146,f193,f2757,f390])).

fof(f2106,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(sK1,X4)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2099,f148])).

fof(f2759,plain,
    ( ~ spl15_53
    | spl15_340
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2113,f1146,f193,f2757,f390])).

fof(f2113,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(sK1,X2))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2107,f378])).

fof(f2755,plain,
    ( ~ spl15_53
    | spl15_338
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2118,f1853,f1731,f2752,f390])).

fof(f2118,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2101,f148])).

fof(f2754,plain,
    ( ~ spl15_53
    | spl15_338
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2125,f1853,f1731,f2752,f390])).

fof(f2125,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2119,f378])).

fof(f2119,plain,
    ( ! [X5] :
        ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f2101,f139])).

fof(f2750,plain,
    ( ~ spl15_51
    | spl15_336
    | ~ spl15_120 ),
    inference(avatar_split_clause,[],[f968,f962,f2748,f381])).

fof(f381,plain,
    ( spl15_51
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).

fof(f968,plain,
    ( v1_xboole_0(k3_waybel_0(sK0,sK3))
    | ~ v1_xboole_0(sK3)
    | ~ spl15_120 ),
    inference(resolution,[],[f963,f378])).

fof(f2743,plain,
    ( spl15_334
    | ~ spl15_264
    | ~ spl15_272
    | spl15_283 ),
    inference(avatar_split_clause,[],[f2736,f1906,f1853,f1815,f2741])).

fof(f2736,plain,
    ( m1_subset_1(sK14(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_264
    | ~ spl15_272
    | ~ spl15_283 ),
    inference(subsumption_resolution,[],[f2735,f1907])).

fof(f1907,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_283 ),
    inference(avatar_component_clause,[],[f1906])).

fof(f2734,plain,
    ( spl15_332
    | ~ spl15_38
    | spl15_63
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2727,f1146,f433,f317,f2732])).

fof(f2727,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_38
    | ~ spl15_63
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2726,f434])).

fof(f434,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl15_63 ),
    inference(avatar_component_clause,[],[f433])).

fof(f2725,plain,
    ( ~ spl15_329
    | spl15_330
    | ~ spl15_4
    | ~ spl15_36
    | spl15_57
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2712,f1146,f406,f310,f193,f2723,f2717])).

fof(f2723,plain,
    ( spl15_330
  <=> r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_330])])).

fof(f2712,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_57
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2711,f407])).

fof(f2711,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2688,f311])).

fof(f2688,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(k4_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v13_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f166,f1202])).

fof(f2710,plain,
    ( ~ spl15_325
    | spl15_326
    | ~ spl15_4
    | ~ spl15_36
    | spl15_57
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f2697,f1146,f406,f310,f193,f2708,f2702])).

fof(f2702,plain,
    ( spl15_325
  <=> ~ v12_waybel_0(sK14(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_325])])).

fof(f2708,plain,
    ( spl15_326
  <=> r1_tarski(k3_waybel_0(sK1,sK14(sK0)),sK14(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_326])])).

fof(f2697,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v12_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_57
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2696,f407])).

fof(f2696,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(k3_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v12_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2687,f311])).

fof(f2687,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(k3_waybel_0(sK1,sK14(sK0)),sK14(sK0))
    | ~ v12_waybel_0(sK14(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f166,f1203])).

fof(f2569,plain,
    ( spl15_320
    | ~ spl15_323
    | ~ spl15_20
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2556,f1853,f1731,f846,f249,f2567,f2561])).

fof(f2561,plain,
    ( spl15_320
  <=> v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_320])])).

fof(f2567,plain,
    ( spl15_323
  <=> ~ v12_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_323])])).

fof(f846,plain,
    ( spl15_118
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK7))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_118])])).

fof(f2556,plain,
    ( ~ v12_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_20
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2555,f345])).

fof(f2555,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f1891,f864])).

fof(f864,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK7)
        | v1_xboole_0(X0) )
    | ~ spl15_118 ),
    inference(resolution,[],[f847,f138])).

fof(f847,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK7))
        | v1_xboole_0(X2) )
    | ~ spl15_118 ),
    inference(avatar_component_clause,[],[f846])).

fof(f2546,plain,
    ( spl15_316
    | ~ spl15_319
    | ~ spl15_20
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2533,f1853,f1731,f846,f249,f2544,f2538])).

fof(f2538,plain,
    ( spl15_316
  <=> v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_316])])).

fof(f2544,plain,
    ( spl15_319
  <=> ~ v13_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_319])])).

fof(f2533,plain,
    ( ~ v13_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_20
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2532,f345])).

fof(f2532,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK7,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | v1_xboole_0(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7))
    | ~ spl15_118
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(resolution,[],[f1890,f864])).

fof(f2199,plain,
    ( spl15_312
    | ~ spl15_315
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2186,f1853,f1731,f2197,f2191])).

fof(f2191,plain,
    ( spl15_312
  <=> r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_312])])).

fof(f2197,plain,
    ( spl15_315
  <=> ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_315])])).

fof(f2186,plain,
    ( ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f2185,f1854])).

fof(f2185,plain,
    ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2177,f1732])).

fof(f2177,plain,
    ( r1_tarski(k3_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f953,f1854])).

fof(f953,plain,(
    ! [X5] :
      ( r1_tarski(k3_waybel_0(X5,sK5(k1_zfmisc_1(u1_struct_0(X5)))),sK5(k1_zfmisc_1(u1_struct_0(X5))))
      | ~ l1_orders_2(X5)
      | ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(X5))),X5) ) ),
    inference(resolution,[],[f129,f130])).

fof(f2160,plain,
    ( spl15_308
    | ~ spl15_311
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f2147,f1853,f1731,f2158,f2152])).

fof(f2152,plain,
    ( spl15_308
  <=> r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_308])])).

fof(f2158,plain,
    ( spl15_311
  <=> ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_311])])).

fof(f2147,plain,
    ( ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(forward_demodulation,[],[f2146,f1854])).

fof(f2146,plain,
    ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f2138,f1732])).

fof(f2138,plain,
    ( r1_tarski(k4_waybel_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f729,f1854])).

fof(f729,plain,(
    ! [X5] :
      ( r1_tarski(k4_waybel_0(X5,sK5(k1_zfmisc_1(u1_struct_0(X5)))),sK5(k1_zfmisc_1(u1_struct_0(X5))))
      | ~ l1_orders_2(X5)
      | ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(X5))),X5) ) ),
    inference(resolution,[],[f127,f130])).

fof(f2063,plain,
    ( ~ spl15_307
    | ~ spl15_4
    | ~ spl15_150
    | spl15_241 ),
    inference(avatar_split_clause,[],[f2056,f1571,f1146,f193,f2061])).

fof(f2061,plain,
    ( spl15_307
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_307])])).

fof(f1571,plain,
    ( spl15_241
  <=> ~ v13_waybel_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_241])])).

fof(f2056,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_241 ),
    inference(duplicate_literal_removal,[],[f2055])).

fof(f2055,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_241 ),
    inference(forward_demodulation,[],[f2054,f1147])).

fof(f2054,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_241 ),
    inference(subsumption_resolution,[],[f2053,f1572])).

fof(f1572,plain,
    ( ~ v13_waybel_0(u1_struct_0(sK0),sK1)
    | ~ spl15_241 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f2053,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v13_waybel_0(u1_struct_0(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f2051,f194])).

fof(f2051,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | v13_waybel_0(u1_struct_0(sK0),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f2046,f126])).

fof(f2014,plain,
    ( ~ spl15_303
    | spl15_304
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f2001,f1887,f179,f2012,f2006])).

fof(f2006,plain,
    ( spl15_303
  <=> ~ v13_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_303])])).

fof(f2012,plain,
    ( spl15_304
  <=> r1_tarski(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_304])])).

fof(f2001,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v13_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f1984,f180])).

fof(f1984,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v13_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_278 ),
    inference(resolution,[],[f1888,f127])).

fof(f2000,plain,
    ( ~ spl15_299
    | spl15_300
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(avatar_split_clause,[],[f1987,f1887,f179,f1998,f1992])).

fof(f1992,plain,
    ( spl15_299
  <=> ~ v12_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_299])])).

fof(f1998,plain,
    ( spl15_300
  <=> r1_tarski(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_300])])).

fof(f1987,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v12_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_0
    | ~ spl15_278 ),
    inference(subsumption_resolution,[],[f1983,f180])).

fof(f1983,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))),sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ v12_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK0)
    | ~ spl15_278 ),
    inference(resolution,[],[f1888,f129])).

fof(f1979,plain,
    ( ~ spl15_289
    | spl15_294
    | ~ spl15_297
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_284 ),
    inference(avatar_split_clause,[],[f1946,f1914,f1146,f193,f1977,f1971,f1952])).

fof(f1971,plain,
    ( spl15_294
  <=> v1_xboole_0(k4_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_294])])).

fof(f1977,plain,
    ( spl15_297
  <=> ~ v13_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_297])])).

fof(f1946,plain,
    ( ~ v13_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_284 ),
    inference(resolution,[],[f1915,f1381])).

fof(f1966,plain,
    ( ~ spl15_289
    | spl15_290
    | ~ spl15_293
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_284 ),
    inference(avatar_split_clause,[],[f1945,f1914,f1146,f193,f1964,f1958,f1952])).

fof(f1958,plain,
    ( spl15_290
  <=> v1_xboole_0(k3_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_290])])).

fof(f1964,plain,
    ( spl15_293
  <=> ~ v12_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_293])])).

fof(f1945,plain,
    ( ~ v12_waybel_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),sK1)
    | v1_xboole_0(k3_waybel_0(sK1,sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ v1_xboole_0(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_284 ),
    inference(resolution,[],[f1915,f1520])).

fof(f1924,plain,
    ( spl15_286
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1917,f1853,f1731,f1922])).

fof(f1922,plain,
    ( spl15_286
  <=> v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_286])])).

fof(f1917,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1874,f1732])).

fof(f1874,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f1705,f1854])).

fof(f1916,plain,
    ( spl15_284
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1909,f1853,f1731,f1914])).

fof(f1909,plain,
    ( r1_tarski(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1871,f1732])).

fof(f1871,plain,
    ( r1_tarski(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f350,f1854])).

fof(f1908,plain,
    ( ~ spl15_283
    | spl15_53
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1901,f1853,f1815,f390,f1906])).

fof(f1901,plain,
    ( ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_53
    | ~ spl15_264
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1900,f1816])).

fof(f1900,plain,
    ( ~ l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v2_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_53
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1869,f391])).

fof(f1899,plain,
    ( spl15_280
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1892,f1853,f1731,f1897])).

fof(f1897,plain,
    ( spl15_280
  <=> m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_280])])).

fof(f1892,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1868,f1732])).

fof(f1868,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f135,f1854])).

fof(f1889,plain,
    ( spl15_278
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1882,f1853,f1731,f1887])).

fof(f1882,plain,
    ( m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_262
    | ~ spl15_272 ),
    inference(subsumption_resolution,[],[f1865,f1732])).

fof(f1865,plain,
    ( m1_subset_1(sK4(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_272 ),
    inference(superposition,[],[f123,f1854])).

fof(f1881,plain,
    ( spl15_276
    | ~ spl15_260
    | ~ spl15_272 ),
    inference(avatar_split_clause,[],[f1864,f1853,f1728,f1879])).

fof(f1879,plain,
    ( spl15_276
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_276])])).

fof(f1728,plain,
    ( spl15_260
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_260])])).

fof(f1864,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_260
    | ~ spl15_272 ),
    inference(backward_demodulation,[],[f1854,f1729])).

fof(f1729,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_260 ),
    inference(avatar_component_clause,[],[f1728])).

fof(f1863,plain,
    ( spl15_274
    | ~ spl15_152
    | ~ spl15_154
    | ~ spl15_202
    | ~ spl15_260 ),
    inference(avatar_split_clause,[],[f1832,f1728,f1396,f1177,f1170,f1861])).

fof(f1170,plain,
    ( spl15_152
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_152])])).

fof(f1832,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_152
    | ~ spl15_154
    | ~ spl15_202
    | ~ spl15_260 ),
    inference(trivial_inequality_removal,[],[f1831])).

fof(f1831,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_152
    | ~ spl15_154
    | ~ spl15_202
    | ~ spl15_260 ),
    inference(superposition,[],[f1399,f1729])).

fof(f1399,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X3 )
    | ~ spl15_152
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(backward_demodulation,[],[f1397,f1378])).

fof(f1378,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X3 )
    | ~ spl15_152
    | ~ spl15_154 ),
    inference(subsumption_resolution,[],[f1368,f1178])).

fof(f1368,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_orders_2(sK1) = X3 )
    | ~ spl15_152 ),
    inference(superposition,[],[f133,f1171])).

fof(f1171,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl15_152 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',free_g1_orders_2)).

fof(f1855,plain,
    ( spl15_272
    | ~ spl15_174
    | ~ spl15_260 ),
    inference(avatar_split_clause,[],[f1833,f1728,f1260,f1853])).

fof(f1260,plain,
    ( spl15_174
  <=> ! [X3,X2] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_174])])).

fof(f1833,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_174
    | ~ spl15_260 ),
    inference(trivial_inequality_removal,[],[f1828])).

fof(f1828,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_174
    | ~ spl15_260 ),
    inference(superposition,[],[f1261,f1729])).

fof(f1261,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X2 )
    | ~ spl15_174 ),
    inference(avatar_component_clause,[],[f1260])).

fof(f1847,plain,
    ( ~ spl15_267
    | spl15_270
    | ~ spl15_260 ),
    inference(avatar_split_clause,[],[f1824,f1728,f1845,f1838])).

fof(f1838,plain,
    ( spl15_267
  <=> ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_267])])).

fof(f1845,plain,
    ( spl15_270
  <=> ! [X5,X4] :
        ( g1_orders_2(X4,X5) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_270])])).

fof(f1824,plain,
    ( ! [X4,X5] :
        ( g1_orders_2(X4,X5) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
        | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X5 )
    | ~ spl15_260 ),
    inference(superposition,[],[f133,f1729])).

fof(f1843,plain,
    ( ~ spl15_267
    | spl15_268
    | ~ spl15_260 ),
    inference(avatar_split_clause,[],[f1822,f1728,f1841,f1838])).

fof(f1841,plain,
    ( spl15_268
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_268])])).

fof(f1822,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
        | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0 )
    | ~ spl15_260 ),
    inference(superposition,[],[f132,f1729])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1817,plain,
    ( spl15_264
    | ~ spl15_262 ),
    inference(avatar_split_clause,[],[f1810,f1731,f1815])).

fof(f1810,plain,
    ( l1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_262 ),
    inference(resolution,[],[f1732,f137])).

fof(f1809,plain,
    ( spl15_262
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1797,f1409,f1731])).

fof(f1797,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_204 ),
    inference(resolution,[],[f163,f1410])).

fof(f1807,plain,
    ( ~ spl15_204
    | spl15_263 ),
    inference(avatar_contradiction_clause,[],[f1806])).

fof(f1806,plain,
    ( $false
    | ~ spl15_204
    | ~ spl15_263 ),
    inference(subsumption_resolution,[],[f1797,f1735])).

fof(f1735,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_263 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f1734,plain,
    ( spl15_263
  <=> ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_263])])).

fof(f1736,plain,
    ( spl15_260
    | ~ spl15_263
    | ~ spl15_258 ),
    inference(avatar_split_clause,[],[f1723,f1719,f1734,f1728])).

fof(f1719,plain,
    ( spl15_258
  <=> v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_258])])).

fof(f1723,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl15_258 ),
    inference(resolution,[],[f1720,f134])).

fof(f1720,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_258 ),
    inference(avatar_component_clause,[],[f1719])).

fof(f1721,plain,
    ( spl15_258
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1706,f1409,f1719])).

fof(f1706,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl15_204 ),
    inference(resolution,[],[f162,f1410])).

fof(f1695,plain,
    ( ~ spl15_257
    | ~ spl15_32
    | spl15_249 ),
    inference(avatar_split_clause,[],[f1688,f1660,f291,f1693])).

fof(f1693,plain,
    ( spl15_257
  <=> ~ v2_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_257])])).

fof(f291,plain,
    ( spl15_32
  <=> l1_orders_2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f1660,plain,
    ( spl15_249
  <=> ~ v1_xboole_0(u1_orders_2(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_249])])).

fof(f1688,plain,
    ( ~ v2_struct_0(sK12)
    | ~ spl15_32
    | ~ spl15_249 ),
    inference(subsumption_resolution,[],[f1687,f292])).

fof(f292,plain,
    ( l1_orders_2(sK12)
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f291])).

fof(f1687,plain,
    ( ~ l1_orders_2(sK12)
    | ~ v2_struct_0(sK12)
    | ~ spl15_249 ),
    inference(resolution,[],[f1661,f703])).

fof(f1661,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK12))
    | ~ spl15_249 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f1686,plain,
    ( spl15_254
    | ~ spl15_136 ),
    inference(avatar_split_clause,[],[f1658,f1082,f1684])).

fof(f1684,plain,
    ( spl15_254
  <=> r1_tarski(u1_orders_2(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_254])])).

fof(f1082,plain,
    ( spl15_136
  <=> m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_136])])).

fof(f1658,plain,
    ( r1_tarski(u1_orders_2(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))
    | ~ spl15_136 ),
    inference(resolution,[],[f1083,f139])).

fof(f1083,plain,
    ( m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))
    | ~ spl15_136 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1679,plain,
    ( spl15_248
    | ~ spl15_253
    | ~ spl15_136 ),
    inference(avatar_split_clause,[],[f1657,f1082,f1677,f1663])).

fof(f1663,plain,
    ( spl15_248
  <=> v1_xboole_0(u1_orders_2(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_248])])).

fof(f1657,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))
    | v1_xboole_0(u1_orders_2(sK12))
    | ~ spl15_136 ),
    inference(resolution,[],[f1083,f148])).

fof(f1672,plain,
    ( spl15_248
    | ~ spl15_251
    | ~ spl15_136 ),
    inference(avatar_split_clause,[],[f1656,f1082,f1669,f1663])).

fof(f1669,plain,
    ( spl15_251
  <=> ~ v1_xboole_0(u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_251])])).

fof(f1656,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK12))
    | v1_xboole_0(u1_orders_2(sK12))
    | ~ spl15_136 ),
    inference(resolution,[],[f1083,f153])).

fof(f1671,plain,
    ( spl15_248
    | ~ spl15_251
    | ~ spl15_136 ),
    inference(avatar_split_clause,[],[f1655,f1082,f1669,f1663])).

fof(f1655,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK12))
    | v1_xboole_0(u1_orders_2(sK12))
    | ~ spl15_136 ),
    inference(resolution,[],[f1083,f154])).

fof(f1654,plain,
    ( ~ spl15_32
    | spl15_137 ),
    inference(avatar_contradiction_clause,[],[f1653])).

fof(f1653,plain,
    ( $false
    | ~ spl15_32
    | ~ spl15_137 ),
    inference(subsumption_resolution,[],[f1651,f292])).

fof(f1651,plain,
    ( ~ l1_orders_2(sK12)
    | ~ spl15_137 ),
    inference(resolution,[],[f1086,f135])).

fof(f1086,plain,
    ( ~ m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))
    | ~ spl15_137 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1085,plain,
    ( spl15_137
  <=> ~ m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_137])])).

fof(f1591,plain,
    ( ~ spl15_231
    | ~ spl15_241
    | ~ spl15_243
    | spl15_244
    | ~ spl15_247
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1532,f1146,f193,f1589,f1583,f1577,f1571,f1540])).

fof(f1540,plain,
    ( spl15_231
  <=> ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_231])])).

fof(f1577,plain,
    ( spl15_243
  <=> ~ v1_xboole_0(k4_waybel_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_243])])).

fof(f1583,plain,
    ( spl15_244
  <=> v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_244])])).

fof(f1589,plain,
    ( spl15_247
  <=> ~ v13_waybel_0(k4_waybel_0(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_247])])).

fof(f1532,plain,
    ( ~ v13_waybel_0(k4_waybel_0(sK1,u1_struct_0(sK0)),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k4_waybel_0(sK1,u1_struct_0(sK0))))
    | ~ v1_xboole_0(k4_waybel_0(sK1,u1_struct_0(sK0)))
    | ~ v13_waybel_0(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1381,f1279])).

fof(f1566,plain,
    ( ~ spl15_231
    | ~ spl15_233
    | ~ spl15_235
    | spl15_236
    | ~ spl15_239
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1531,f1146,f193,f1564,f1558,f1552,f1546,f1540])).

fof(f1546,plain,
    ( spl15_233
  <=> ~ v12_waybel_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_233])])).

fof(f1552,plain,
    ( spl15_235
  <=> ~ v1_xboole_0(k3_waybel_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_235])])).

fof(f1558,plain,
    ( spl15_236
  <=> v1_xboole_0(k4_waybel_0(sK1,k3_waybel_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_236])])).

fof(f1564,plain,
    ( spl15_239
  <=> ~ v13_waybel_0(k3_waybel_0(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_239])])).

fof(f1531,plain,
    ( ~ v13_waybel_0(k3_waybel_0(sK1,u1_struct_0(sK0)),sK1)
    | v1_xboole_0(k4_waybel_0(sK1,k3_waybel_0(sK1,u1_struct_0(sK0))))
    | ~ v1_xboole_0(k3_waybel_0(sK1,u1_struct_0(sK0)))
    | ~ v12_waybel_0(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1381,f1444])).

fof(f1515,plain,
    ( ~ spl15_4
    | spl15_211 ),
    inference(avatar_contradiction_clause,[],[f1514])).

fof(f1514,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_211 ),
    inference(subsumption_resolution,[],[f1513,f194])).

fof(f1513,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl15_211 ),
    inference(resolution,[],[f1451,f124])).

fof(f1451,plain,
    ( ~ v12_waybel_0(sK4(sK1),sK1)
    | ~ spl15_211 ),
    inference(avatar_component_clause,[],[f1450])).

fof(f1450,plain,
    ( spl15_211
  <=> ~ v12_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_211])])).

fof(f1512,plain,
    ( ~ spl15_227
    | spl15_228
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1445,f1146,f193,f1510,f1504])).

fof(f1504,plain,
    ( spl15_227
  <=> ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_227])])).

fof(f1510,plain,
    ( spl15_228
  <=> r1_tarski(k3_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_228])])).

fof(f1445,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v12_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1203,f130])).

fof(f1499,plain,
    ( ~ spl15_223
    | spl15_224
    | ~ spl15_4
    | spl15_53
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1486,f1146,f390,f193,f1497,f1491])).

fof(f1491,plain,
    ( spl15_223
  <=> ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_223])])).

fof(f1497,plain,
    ( spl15_224
  <=> r1_tarski(k3_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_224])])).

fof(f1486,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_53
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1443,f391])).

fof(f1443,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1203,f149])).

fof(f1485,plain,
    ( ~ spl15_219
    | spl15_220
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1442,f1146,f249,f193,f1483,f1477])).

fof(f1477,plain,
    ( spl15_219
  <=> ~ v12_waybel_0(sK7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_219])])).

fof(f1483,plain,
    ( spl15_220
  <=> r1_tarski(k3_waybel_0(sK1,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_220])])).

fof(f1442,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK7),sK7)
    | ~ v12_waybel_0(sK7,sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f1203,f345])).

fof(f1472,plain,
    ( ~ spl15_215
    | spl15_216
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1459,f1146,f193,f179,f1470,f1464])).

fof(f1464,plain,
    ( spl15_215
  <=> ~ v12_waybel_0(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_215])])).

fof(f1470,plain,
    ( spl15_216
  <=> r1_tarski(k3_waybel_0(sK1,sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_216])])).

fof(f1459,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ v12_waybel_0(sK4(sK0),sK1)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1441,f180])).

fof(f1441,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ v12_waybel_0(sK4(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1203,f123])).

fof(f1458,plain,
    ( ~ spl15_211
    | spl15_212
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f1440,f1199,f1146,f193,f1456,f1450])).

fof(f1440,plain,
    ( r1_tarski(k3_waybel_0(sK1,sK4(sK1)),sK4(sK1))
    | ~ v12_waybel_0(sK4(sK1),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160 ),
    inference(resolution,[],[f1203,f1200])).

fof(f1428,plain,
    ( spl15_204
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f1427,f1396,f1146,f193,f1409])).

fof(f1427,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1426,f1147])).

fof(f1426,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl15_4
    | ~ spl15_202 ),
    inference(subsumption_resolution,[],[f1404,f194])).

fof(f1404,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | ~ spl15_202 ),
    inference(superposition,[],[f135,f1397])).

fof(f1425,plain,
    ( ~ spl15_209
    | spl15_141
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f1402,f1396,f1101,f1423])).

fof(f1402,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ~ spl15_141
    | ~ spl15_202 ),
    inference(backward_demodulation,[],[f1397,f1102])).

fof(f1418,plain,
    ( spl15_206
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f1401,f1396,f1191,f1416])).

fof(f1401,plain,
    ( r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_158
    | ~ spl15_202 ),
    inference(backward_demodulation,[],[f1397,f1192])).

fof(f1411,plain,
    ( spl15_204
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f1400,f1396,f1177,f1409])).

fof(f1400,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_154
    | ~ spl15_202 ),
    inference(backward_demodulation,[],[f1397,f1178])).

fof(f1398,plain,
    ( spl15_202
    | ~ spl15_152
    | ~ spl15_154 ),
    inference(avatar_split_clause,[],[f1391,f1177,f1170,f1396])).

fof(f1391,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl15_152
    | ~ spl15_154 ),
    inference(equality_resolution,[],[f1378])).

fof(f1377,plain,
    ( ~ spl15_137
    | spl15_200
    | ~ spl15_60 ),
    inference(avatar_split_clause,[],[f1367,f424,f1375,f1085])).

fof(f1375,plain,
    ( spl15_200
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != sK12
        | u1_orders_2(sK12) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_200])])).

fof(f424,plain,
    ( spl15_60
  <=> g1_orders_2(u1_struct_0(sK12),u1_orders_2(sK12)) = sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_60])])).

fof(f1367,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != sK12
        | ~ m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))
        | u1_orders_2(sK12) = X1 )
    | ~ spl15_60 ),
    inference(superposition,[],[f133,f425])).

fof(f425,plain,
    ( g1_orders_2(u1_struct_0(sK12),u1_orders_2(sK12)) = sK12
    | ~ spl15_60 ),
    inference(avatar_component_clause,[],[f424])).

fof(f1365,plain,
    ( ~ spl15_197
    | spl15_198
    | ~ spl15_178 ),
    inference(avatar_split_clause,[],[f1352,f1291,f1363,f1357])).

fof(f1291,plain,
    ( spl15_178
  <=> r1_tarski(k4_waybel_0(sK1,sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_178])])).

fof(f1352,plain,
    ( v1_xboole_0(k4_waybel_0(sK1,sK4(sK1)))
    | ~ v1_xboole_0(sK4(sK1))
    | ~ spl15_178 ),
    inference(resolution,[],[f1292,f378])).

fof(f1292,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK1)),sK4(sK1))
    | ~ spl15_178 ),
    inference(avatar_component_clause,[],[f1291])).

fof(f1350,plain,
    ( ~ spl15_4
    | spl15_177 ),
    inference(avatar_contradiction_clause,[],[f1349])).

fof(f1349,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_177 ),
    inference(subsumption_resolution,[],[f1348,f194])).

fof(f1348,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl15_177 ),
    inference(resolution,[],[f1286,f125])).

fof(f1286,plain,
    ( ~ v13_waybel_0(sK4(sK1),sK1)
    | ~ spl15_177 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1285,plain,
    ( spl15_177
  <=> ~ v13_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_177])])).

fof(f1347,plain,
    ( ~ spl15_193
    | spl15_194
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1280,f1146,f193,f1345,f1339])).

fof(f1339,plain,
    ( spl15_193
  <=> ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_193])])).

fof(f1345,plain,
    ( spl15_194
  <=> r1_tarski(k4_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_194])])).

fof(f1280,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v13_waybel_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1202,f130])).

fof(f1334,plain,
    ( ~ spl15_189
    | spl15_190
    | ~ spl15_4
    | spl15_53
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1321,f1146,f390,f193,f1332,f1326])).

fof(f1332,plain,
    ( spl15_190
  <=> r1_tarski(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_190])])).

fof(f1321,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | ~ spl15_4
    | ~ spl15_53
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1278,f391])).

fof(f1278,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK10(u1_struct_0(sK0))),sK10(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK10(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1202,f149])).

fof(f1320,plain,
    ( ~ spl15_185
    | spl15_186
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1277,f1146,f249,f193,f1318,f1312])).

fof(f1318,plain,
    ( spl15_186
  <=> r1_tarski(k4_waybel_0(sK1,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_186])])).

fof(f1277,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK7),sK7)
    | ~ v13_waybel_0(sK7,sK1)
    | ~ spl15_4
    | ~ spl15_20
    | ~ spl15_150 ),
    inference(resolution,[],[f1202,f345])).

fof(f1307,plain,
    ( ~ spl15_181
    | spl15_182
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1294,f1146,f193,f179,f1305,f1299])).

fof(f1294,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ spl15_0
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1276,f180])).

fof(f1276,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK0)),sK4(sK0))
    | ~ v13_waybel_0(sK4(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(resolution,[],[f1202,f123])).

fof(f1293,plain,
    ( ~ spl15_177
    | spl15_178
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f1275,f1199,f1146,f193,f1291,f1285])).

fof(f1275,plain,
    ( r1_tarski(k4_waybel_0(sK1,sK4(sK1)),sK4(sK1))
    | ~ v13_waybel_0(sK4(sK1),sK1)
    | ~ spl15_4
    | ~ spl15_150
    | ~ spl15_160 ),
    inference(resolution,[],[f1202,f1200])).

fof(f1270,plain,
    ( spl15_174
    | ~ spl15_134
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1154,f1146,f1078,f1260])).

fof(f1078,plain,
    ( spl15_134
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_134])])).

fof(f1154,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(sK0) = X0
        | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl15_134
    | ~ spl15_150 ),
    inference(backward_demodulation,[],[f1147,f1079])).

fof(f1079,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl15_134 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f1262,plain,
    ( ~ spl15_155
    | spl15_174
    | ~ spl15_152 ),
    inference(avatar_split_clause,[],[f1258,f1170,f1260,f1174])).

fof(f1174,plain,
    ( spl15_155
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_155])])).

fof(f1258,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK0) = X2 )
    | ~ spl15_152 ),
    inference(superposition,[],[f132,f1171])).

fof(f1256,plain,
    ( ~ spl15_171
    | spl15_172
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f1243,f1199,f179,f1254,f1248])).

fof(f1243,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(subsumption_resolution,[],[f1226,f180])).

fof(f1226,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k4_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ v13_waybel_0(sK4(sK1),sK0)
    | ~ spl15_160 ),
    inference(resolution,[],[f1200,f127])).

fof(f1242,plain,
    ( ~ spl15_167
    | spl15_168
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(avatar_split_clause,[],[f1229,f1199,f179,f1240,f1234])).

fof(f1229,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_0
    | ~ spl15_160 ),
    inference(subsumption_resolution,[],[f1225,f180])).

fof(f1225,plain,
    ( ~ l1_orders_2(sK0)
    | r1_tarski(k3_waybel_0(sK0,sK4(sK1)),sK4(sK1))
    | ~ v12_waybel_0(sK4(sK1),sK0)
    | ~ spl15_160 ),
    inference(resolution,[],[f1200,f129])).

fof(f1221,plain,
    ( ~ spl15_165
    | spl15_147
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1214,f1146,f1130,f1219])).

fof(f1219,plain,
    ( spl15_165
  <=> u1_struct_0(sK0) != u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_165])])).

fof(f1130,plain,
    ( spl15_147
  <=> u1_struct_0(sK1) != u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_147])])).

fof(f1214,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK12)
    | ~ spl15_147
    | ~ spl15_150 ),
    inference(forward_demodulation,[],[f1131,f1147])).

fof(f1131,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK12)
    | ~ spl15_147 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1213,plain,
    ( spl15_162
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1206,f1146,f193,f1211])).

fof(f1206,plain,
    ( r1_tarski(sK4(sK1),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1163,f194])).

fof(f1163,plain,
    ( r1_tarski(sK4(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f350,f1147])).

fof(f1205,plain,
    ( spl15_154
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1204,f1146,f193,f1177])).

fof(f1204,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1160,f194])).

fof(f1160,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f135,f1147])).

fof(f1201,plain,
    ( spl15_160
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1194,f1146,f193,f1199])).

fof(f1194,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_4
    | ~ spl15_150 ),
    inference(subsumption_resolution,[],[f1157,f194])).

fof(f1157,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK1)
    | ~ spl15_150 ),
    inference(superposition,[],[f123,f1147])).

fof(f1193,plain,
    ( spl15_158
    | ~ spl15_144
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1156,f1146,f1117,f1191])).

fof(f1156,plain,
    ( r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_144
    | ~ spl15_150 ),
    inference(backward_demodulation,[],[f1147,f1118])).

fof(f1186,plain,
    ( ~ spl15_157
    | spl15_143
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1155,f1146,f1110,f1184])).

fof(f1155,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl15_143
    | ~ spl15_150 ),
    inference(backward_demodulation,[],[f1147,f1111])).

fof(f1179,plain,
    ( spl15_154
    | ~ spl15_132
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1153,f1146,f1072,f1177])).

fof(f1153,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_132
    | ~ spl15_150 ),
    inference(backward_demodulation,[],[f1147,f1073])).

fof(f1172,plain,
    ( spl15_152
    | ~ spl15_2
    | ~ spl15_150 ),
    inference(avatar_split_clause,[],[f1149,f1146,f186,f1170])).

fof(f186,plain,
    ( spl15_2
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f1149,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl15_2
    | ~ spl15_150 ),
    inference(backward_demodulation,[],[f1147,f187])).

fof(f187,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1148,plain,
    ( spl15_150
    | ~ spl15_134 ),
    inference(avatar_split_clause,[],[f1128,f1078,f1146])).

fof(f1128,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl15_134 ),
    inference(equality_resolution,[],[f1079])).

fof(f1141,plain,
    ( spl15_146
    | ~ spl15_149
    | ~ spl15_60
    | ~ spl15_134 ),
    inference(avatar_split_clause,[],[f1127,f1078,f424,f1139,f1133])).

fof(f1133,plain,
    ( spl15_146
  <=> u1_struct_0(sK1) = u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_146])])).

fof(f1139,plain,
    ( spl15_149
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_149])])).

fof(f1127,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != sK12
    | u1_struct_0(sK1) = u1_struct_0(sK12)
    | ~ spl15_60
    | ~ spl15_134 ),
    inference(superposition,[],[f1079,f425])).

fof(f1119,plain,
    ( spl15_144
    | ~ spl15_132 ),
    inference(avatar_split_clause,[],[f1099,f1072,f1117])).

fof(f1099,plain,
    ( r1_tarski(u1_orders_2(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl15_132 ),
    inference(resolution,[],[f1073,f139])).

fof(f1112,plain,
    ( spl15_140
    | ~ spl15_143
    | ~ spl15_132 ),
    inference(avatar_split_clause,[],[f1098,f1072,f1110,f1104])).

fof(f1098,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ spl15_132 ),
    inference(resolution,[],[f1073,f148])).

fof(f1095,plain,
    ( ~ spl15_4
    | spl15_133 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_133 ),
    inference(subsumption_resolution,[],[f1092,f194])).

fof(f1092,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl15_133 ),
    inference(resolution,[],[f1076,f135])).

fof(f1076,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl15_133 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f1075,plain,
    ( spl15_133
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_133])])).

fof(f1090,plain,
    ( ~ spl15_137
    | spl15_138
    | ~ spl15_60 ),
    inference(avatar_split_clause,[],[f1065,f424,f1088,f1085])).

fof(f1088,plain,
    ( spl15_138
  <=> ! [X3,X2] :
        ( g1_orders_2(X2,X3) != sK12
        | u1_struct_0(sK12) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_138])])).

fof(f1065,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != sK12
        | ~ m1_subset_1(u1_orders_2(sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12))))
        | u1_struct_0(sK12) = X2 )
    | ~ spl15_60 ),
    inference(superposition,[],[f132,f425])).

fof(f1080,plain,
    ( ~ spl15_133
    | spl15_134
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f1064,f186,f1078,f1075])).

fof(f1064,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X0 )
    | ~ spl15_2 ),
    inference(superposition,[],[f132,f187])).

fof(f1028,plain,
    ( spl15_130
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f997,f988,f249,f1026])).

fof(f1026,plain,
    ( spl15_130
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK11,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_130])])).

fof(f988,plain,
    ( spl15_124
  <=> v1_xboole_0(k3_waybel_0(sK11,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_124])])).

fof(f997,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k3_waybel_0(sK11,sK7))))) = sK7
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(resolution,[],[f989,f446])).

fof(f989,plain,
    ( v1_xboole_0(k3_waybel_0(sK11,sK7))
    | ~ spl15_124 ),
    inference(avatar_component_clause,[],[f988])).

fof(f1021,plain,
    ( spl15_128
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f995,f988,f249,f1019])).

fof(f1019,plain,
    ( spl15_128
  <=> sK5(k1_zfmisc_1(k3_waybel_0(sK11,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_128])])).

fof(f995,plain,
    ( sK5(k1_zfmisc_1(k3_waybel_0(sK11,sK7))) = sK7
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(resolution,[],[f989,f436])).

fof(f1014,plain,
    ( spl15_126
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f994,f988,f249,f1012])).

fof(f1012,plain,
    ( spl15_126
  <=> k3_waybel_0(sK11,sK7) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_126])])).

fof(f994,plain,
    ( k3_waybel_0(sK11,sK7) = sK7
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(resolution,[],[f989,f341])).

fof(f992,plain,
    ( spl15_124
    | ~ spl15_20
    | ~ spl15_122 ),
    inference(avatar_split_clause,[],[f991,f978,f249,f988])).

fof(f978,plain,
    ( spl15_122
  <=> r1_tarski(k3_waybel_0(sK11,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_122])])).

fof(f991,plain,
    ( v1_xboole_0(k3_waybel_0(sK11,sK7))
    | ~ spl15_20
    | ~ spl15_122 ),
    inference(subsumption_resolution,[],[f983,f250])).

fof(f983,plain,
    ( v1_xboole_0(k3_waybel_0(sK11,sK7))
    | ~ v1_xboole_0(sK7)
    | ~ spl15_122 ),
    inference(resolution,[],[f979,f378])).

fof(f979,plain,
    ( r1_tarski(k3_waybel_0(sK11,sK7),sK7)
    | ~ spl15_122 ),
    inference(avatar_component_clause,[],[f978])).

fof(f990,plain,
    ( spl15_124
    | ~ spl15_118
    | ~ spl15_122 ),
    inference(avatar_split_clause,[],[f981,f978,f846,f988])).

fof(f981,plain,
    ( v1_xboole_0(k3_waybel_0(sK11,sK7))
    | ~ spl15_118
    | ~ spl15_122 ),
    inference(resolution,[],[f979,f864])).

fof(f980,plain,
    ( spl15_122
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f973,f523,f277,f978])).

fof(f523,plain,
    ( spl15_78
  <=> sK4(sK11) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_78])])).

fof(f973,plain,
    ( r1_tarski(k3_waybel_0(sK11,sK7),sK7)
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(subsumption_resolution,[],[f971,f278])).

fof(f971,plain,
    ( r1_tarski(k3_waybel_0(sK11,sK7),sK7)
    | ~ l1_orders_2(sK11)
    | ~ spl15_78 ),
    inference(superposition,[],[f965,f524])).

fof(f524,plain,
    ( sK4(sK11) = sK7
    | ~ spl15_78 ),
    inference(avatar_component_clause,[],[f523])).

fof(f965,plain,(
    ! [X0] :
      ( r1_tarski(k3_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f955,f124])).

fof(f955,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r1_tarski(k3_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ v12_waybel_0(sK4(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f949])).

fof(f949,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r1_tarski(k3_waybel_0(X0,sK4(X0)),sK4(X0))
      | ~ v12_waybel_0(sK4(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f129,f123])).

fof(f964,plain,
    ( spl15_120
    | ~ spl15_0
    | ~ spl15_6
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f957,f220,f200,f179,f962])).

fof(f220,plain,
    ( spl15_12
  <=> v12_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f957,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ spl15_0
    | ~ spl15_6
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f956,f221])).

fof(f221,plain,
    ( v12_waybel_0(sK3,sK0)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f848,plain,
    ( spl15_116
    | spl15_118
    | ~ spl15_20 ),
    inference(avatar_split_clause,[],[f840,f249,f846,f843])).

fof(f843,plain,
    ( spl15_116
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_116])])).

fof(f840,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK7))
        | ~ v1_xboole_0(X1)
        | v1_xboole_0(X2) )
    | ~ spl15_20 ),
    inference(superposition,[],[f154,f695])).

fof(f695,plain,
    ( ! [X9] : k2_zfmisc_1(X9,sK7) = sK7
    | ~ spl15_20 ),
    inference(resolution,[],[f651,f250])).

fof(f785,plain,
    ( spl15_114
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f763,f756,f249,f783])).

fof(f783,plain,
    ( spl15_114
  <=> k4_waybel_0(sK11,sK7) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_114])])).

fof(f756,plain,
    ( spl15_108
  <=> v1_xboole_0(k4_waybel_0(sK11,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_108])])).

fof(f763,plain,
    ( k4_waybel_0(sK11,sK7) = sK7
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(resolution,[],[f757,f341])).

fof(f757,plain,
    ( v1_xboole_0(k4_waybel_0(sK11,sK7))
    | ~ spl15_108 ),
    inference(avatar_component_clause,[],[f756])).

fof(f778,plain,
    ( spl15_112
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f762,f756,f249,f776])).

fof(f776,plain,
    ( spl15_112
  <=> sK5(k1_zfmisc_1(k4_waybel_0(sK11,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_112])])).

fof(f762,plain,
    ( sK5(k1_zfmisc_1(k4_waybel_0(sK11,sK7))) = sK7
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(resolution,[],[f757,f436])).

fof(f771,plain,
    ( spl15_110
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f760,f756,f249,f769])).

fof(f769,plain,
    ( spl15_110
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK11,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_110])])).

fof(f760,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k4_waybel_0(sK11,sK7))))) = sK7
    | ~ spl15_20
    | ~ spl15_108 ),
    inference(resolution,[],[f757,f446])).

fof(f758,plain,
    ( spl15_108
    | ~ spl15_20
    | ~ spl15_106 ),
    inference(avatar_split_clause,[],[f751,f746,f249,f756])).

fof(f746,plain,
    ( spl15_106
  <=> r1_tarski(k4_waybel_0(sK11,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_106])])).

fof(f751,plain,
    ( v1_xboole_0(k4_waybel_0(sK11,sK7))
    | ~ spl15_20
    | ~ spl15_106 ),
    inference(subsumption_resolution,[],[f750,f250])).

fof(f750,plain,
    ( v1_xboole_0(k4_waybel_0(sK11,sK7))
    | ~ v1_xboole_0(sK7)
    | ~ spl15_106 ),
    inference(resolution,[],[f747,f378])).

fof(f747,plain,
    ( r1_tarski(k4_waybel_0(sK11,sK7),sK7)
    | ~ spl15_106 ),
    inference(avatar_component_clause,[],[f746])).

fof(f748,plain,
    ( spl15_106
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f741,f523,f277,f746])).

fof(f741,plain,
    ( r1_tarski(k4_waybel_0(sK11,sK7),sK7)
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(subsumption_resolution,[],[f739,f278])).

fof(f739,plain,
    ( r1_tarski(k4_waybel_0(sK11,sK7),sK7)
    | ~ l1_orders_2(sK11)
    | ~ spl15_78 ),
    inference(superposition,[],[f732,f524])).

fof(f683,plain,
    ( spl15_104
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(avatar_split_clause,[],[f660,f573,f249,f681])).

fof(f681,plain,
    ( spl15_104
  <=> k2_zfmisc_1(sK7,sK7) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_104])])).

fof(f573,plain,
    ( spl15_88
  <=> v1_xboole_0(k2_zfmisc_1(sK7,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_88])])).

fof(f660,plain,
    ( k2_zfmisc_1(sK7,sK7) = sK7
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(resolution,[],[f574,f341])).

fof(f574,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK7))
    | ~ spl15_88 ),
    inference(avatar_component_clause,[],[f573])).

fof(f676,plain,
    ( spl15_102
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(avatar_split_clause,[],[f659,f573,f249,f674])).

fof(f674,plain,
    ( spl15_102
  <=> sK5(k1_zfmisc_1(k2_zfmisc_1(sK7,sK7))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_102])])).

fof(f659,plain,
    ( sK5(k1_zfmisc_1(k2_zfmisc_1(sK7,sK7))) = sK7
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(resolution,[],[f574,f436])).

fof(f669,plain,
    ( spl15_100
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(avatar_split_clause,[],[f657,f573,f249,f667])).

fof(f667,plain,
    ( spl15_100
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK7,sK7))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_100])])).

fof(f657,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK7,sK7))))) = sK7
    | ~ spl15_20
    | ~ spl15_88 ),
    inference(resolution,[],[f574,f446])).

fof(f654,plain,
    ( ~ spl15_20
    | spl15_89 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | ~ spl15_20
    | ~ spl15_89 ),
    inference(subsumption_resolution,[],[f647,f250])).

fof(f647,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl15_89 ),
    inference(resolution,[],[f606,f577])).

fof(f577,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK7,sK7))
    | ~ spl15_89 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl15_89
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK7,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_89])])).

fof(f645,plain,
    ( spl15_98
    | ~ spl15_68
    | ~ spl15_96 ),
    inference(avatar_split_clause,[],[f637,f631,f481,f643])).

fof(f481,plain,
    ( spl15_68
  <=> g1_orders_2(sK7,u1_orders_2(sK11)) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_68])])).

fof(f637,plain,
    ( g1_orders_2(sK7,sK7) = sK11
    | ~ spl15_68
    | ~ spl15_96 ),
    inference(backward_demodulation,[],[f632,f482])).

fof(f482,plain,
    ( g1_orders_2(sK7,u1_orders_2(sK11)) = sK11
    | ~ spl15_68 ),
    inference(avatar_component_clause,[],[f481])).

fof(f633,plain,
    ( spl15_96
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(avatar_split_clause,[],[f611,f570,f249,f631])).

fof(f570,plain,
    ( spl15_86
  <=> v1_xboole_0(u1_orders_2(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_86])])).

fof(f611,plain,
    ( u1_orders_2(sK11) = sK7
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(resolution,[],[f571,f341])).

fof(f571,plain,
    ( v1_xboole_0(u1_orders_2(sK11))
    | ~ spl15_86 ),
    inference(avatar_component_clause,[],[f570])).

fof(f626,plain,
    ( spl15_94
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(avatar_split_clause,[],[f610,f570,f249,f624])).

fof(f624,plain,
    ( spl15_94
  <=> sK5(k1_zfmisc_1(u1_orders_2(sK11))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_94])])).

fof(f610,plain,
    ( sK5(k1_zfmisc_1(u1_orders_2(sK11))) = sK7
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(resolution,[],[f571,f436])).

fof(f619,plain,
    ( spl15_92
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(avatar_split_clause,[],[f608,f570,f249,f617])).

fof(f617,plain,
    ( spl15_92
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(u1_orders_2(sK11))))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).

fof(f608,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(u1_orders_2(sK11))))) = sK7
    | ~ spl15_20
    | ~ spl15_86 ),
    inference(resolution,[],[f571,f446])).

fof(f607,plain,
    ( spl15_86
    | ~ spl15_20
    | ~ spl15_80 ),
    inference(avatar_split_clause,[],[f603,f535,f249,f570])).

fof(f535,plain,
    ( spl15_80
  <=> m1_subset_1(u1_orders_2(sK11),k1_zfmisc_1(k2_zfmisc_1(sK7,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_80])])).

fof(f603,plain,
    ( v1_xboole_0(u1_orders_2(sK11))
    | ~ spl15_20
    | ~ spl15_80 ),
    inference(subsumption_resolution,[],[f598,f250])).

fof(f598,plain,
    ( ~ v1_xboole_0(sK7)
    | v1_xboole_0(u1_orders_2(sK11))
    | ~ spl15_80 ),
    inference(resolution,[],[f153,f536])).

fof(f536,plain,
    ( m1_subset_1(u1_orders_2(sK11),k1_zfmisc_1(k2_zfmisc_1(sK7,sK7)))
    | ~ spl15_80 ),
    inference(avatar_component_clause,[],[f535])).

fof(f605,plain,
    ( ~ spl15_20
    | ~ spl15_80
    | spl15_87 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl15_20
    | ~ spl15_80
    | ~ spl15_87 ),
    inference(subsumption_resolution,[],[f603,f568])).

fof(f568,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK11))
    | ~ spl15_87 ),
    inference(avatar_component_clause,[],[f567])).

fof(f567,plain,
    ( spl15_87
  <=> ~ v1_xboole_0(u1_orders_2(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_87])])).

fof(f585,plain,
    ( spl15_90
    | ~ spl15_80 ),
    inference(avatar_split_clause,[],[f565,f535,f583])).

fof(f583,plain,
    ( spl15_90
  <=> r1_tarski(u1_orders_2(sK11),k2_zfmisc_1(sK7,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_90])])).

fof(f565,plain,
    ( r1_tarski(u1_orders_2(sK11),k2_zfmisc_1(sK7,sK7))
    | ~ spl15_80 ),
    inference(resolution,[],[f536,f139])).

fof(f578,plain,
    ( spl15_86
    | ~ spl15_89
    | ~ spl15_80 ),
    inference(avatar_split_clause,[],[f564,f535,f576,f570])).

fof(f564,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK7,sK7))
    | v1_xboole_0(u1_orders_2(sK11))
    | ~ spl15_80 ),
    inference(resolution,[],[f536,f148])).

fof(f560,plain,
    ( spl15_84
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f553,f523,f277,f558])).

fof(f558,plain,
    ( spl15_84
  <=> v12_waybel_0(sK7,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_84])])).

fof(f553,plain,
    ( v12_waybel_0(sK7,sK11)
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(subsumption_resolution,[],[f544,f278])).

fof(f544,plain,
    ( v12_waybel_0(sK7,sK11)
    | ~ l1_orders_2(sK11)
    | ~ spl15_78 ),
    inference(superposition,[],[f124,f524])).

fof(f552,plain,
    ( spl15_82
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f545,f523,f277,f550])).

fof(f550,plain,
    ( spl15_82
  <=> v13_waybel_0(sK7,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_82])])).

fof(f545,plain,
    ( v13_waybel_0(sK7,sK11)
    | ~ spl15_28
    | ~ spl15_78 ),
    inference(subsumption_resolution,[],[f543,f278])).

fof(f543,plain,
    ( v13_waybel_0(sK7,sK11)
    | ~ l1_orders_2(sK11)
    | ~ spl15_78 ),
    inference(superposition,[],[f125,f524])).

fof(f537,plain,
    ( spl15_80
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f530,f468,f277,f535])).

fof(f530,plain,
    ( m1_subset_1(u1_orders_2(sK11),k1_zfmisc_1(k2_zfmisc_1(sK7,sK7)))
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f529,f278])).

fof(f529,plain,
    ( m1_subset_1(u1_orders_2(sK11),k1_zfmisc_1(k2_zfmisc_1(sK7,sK7)))
    | ~ l1_orders_2(sK11)
    | ~ spl15_66 ),
    inference(superposition,[],[f135,f469])).

fof(f525,plain,
    ( spl15_78
    | ~ spl15_20
    | ~ spl15_70 ),
    inference(avatar_split_clause,[],[f510,f490,f249,f523])).

fof(f490,plain,
    ( spl15_70
  <=> v1_xboole_0(sK4(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f510,plain,
    ( sK4(sK11) = sK7
    | ~ spl15_20
    | ~ spl15_70 ),
    inference(resolution,[],[f491,f341])).

fof(f491,plain,
    ( v1_xboole_0(sK4(sK11))
    | ~ spl15_70 ),
    inference(avatar_component_clause,[],[f490])).

fof(f518,plain,
    ( spl15_76
    | ~ spl15_20
    | ~ spl15_70 ),
    inference(avatar_split_clause,[],[f509,f490,f249,f516])).

fof(f516,plain,
    ( spl15_76
  <=> sK5(k1_zfmisc_1(sK4(sK11))) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).

fof(f509,plain,
    ( sK5(k1_zfmisc_1(sK4(sK11))) = sK7
    | ~ spl15_20
    | ~ spl15_70 ),
    inference(resolution,[],[f491,f436])).

fof(f508,plain,
    ( spl15_74
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f501,f468,f277,f506])).

fof(f506,plain,
    ( spl15_74
  <=> m1_subset_1(sK4(sK11),k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f501,plain,
    ( m1_subset_1(sK4(sK11),k1_zfmisc_1(sK7))
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f476,f278])).

fof(f476,plain,
    ( m1_subset_1(sK4(sK11),k1_zfmisc_1(sK7))
    | ~ l1_orders_2(sK11)
    | ~ spl15_66 ),
    inference(superposition,[],[f123,f469])).

fof(f500,plain,
    ( spl15_72
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f493,f468,f277,f498])).

fof(f498,plain,
    ( spl15_72
  <=> r1_tarski(sK4(sK11),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f493,plain,
    ( r1_tarski(sK4(sK11),sK7)
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f473,f278])).

fof(f473,plain,
    ( r1_tarski(sK4(sK11),sK7)
    | ~ l1_orders_2(sK11)
    | ~ spl15_66 ),
    inference(superposition,[],[f350,f469])).

fof(f492,plain,
    ( spl15_70
    | ~ spl15_20
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f485,f468,f277,f249,f490])).

fof(f485,plain,
    ( v1_xboole_0(sK4(sK11))
    | ~ spl15_20
    | ~ spl15_28
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f484,f278])).

fof(f484,plain,
    ( v1_xboole_0(sK4(sK11))
    | ~ l1_orders_2(sK11)
    | ~ spl15_20
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f472,f250])).

fof(f472,plain,
    ( ~ v1_xboole_0(sK7)
    | v1_xboole_0(sK4(sK11))
    | ~ l1_orders_2(sK11)
    | ~ spl15_66 ),
    inference(superposition,[],[f375,f469])).

fof(f483,plain,
    ( spl15_68
    | ~ spl15_58
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f471,f468,f416,f481])).

fof(f416,plain,
    ( spl15_58
  <=> g1_orders_2(u1_struct_0(sK11),u1_orders_2(sK11)) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).

fof(f471,plain,
    ( g1_orders_2(sK7,u1_orders_2(sK11)) = sK11
    | ~ spl15_58
    | ~ spl15_66 ),
    inference(backward_demodulation,[],[f469,f417])).

fof(f417,plain,
    ( g1_orders_2(u1_struct_0(sK11),u1_orders_2(sK11)) = sK11
    | ~ spl15_58 ),
    inference(avatar_component_clause,[],[f416])).

fof(f470,plain,
    ( spl15_66
    | ~ spl15_20
    | ~ spl15_26
    | ~ spl15_42 ),
    inference(avatar_split_clause,[],[f463,f331,f270,f249,f468])).

fof(f270,plain,
    ( spl15_26
  <=> v2_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f331,plain,
    ( spl15_42
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f463,plain,
    ( u1_struct_0(sK11) = sK7
    | ~ spl15_20
    | ~ spl15_26
    | ~ spl15_42 ),
    inference(subsumption_resolution,[],[f462,f332])).

fof(f332,plain,
    ( l1_struct_0(sK11)
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f331])).

fof(f462,plain,
    ( ~ l1_struct_0(sK11)
    | u1_struct_0(sK11) = sK7
    | ~ spl15_20
    | ~ spl15_26 ),
    inference(resolution,[],[f369,f271])).

fof(f271,plain,
    ( v2_struct_0(sK11)
    | ~ spl15_26 ),
    inference(avatar_component_clause,[],[f270])).

fof(f453,plain,
    ( spl15_64
    | ~ spl15_20 ),
    inference(avatar_split_clause,[],[f444,f249,f451])).

fof(f451,plain,
    ( spl15_64
  <=> sK5(k1_zfmisc_1(sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f444,plain,
    ( sK5(k1_zfmisc_1(sK7)) = sK7
    | ~ spl15_20 ),
    inference(resolution,[],[f436,f250])).

fof(f435,plain,
    ( ~ spl15_63
    | ~ spl15_38
    | spl15_55 ),
    inference(avatar_split_clause,[],[f428,f397,f317,f433])).

fof(f428,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl15_38
    | ~ spl15_55 ),
    inference(subsumption_resolution,[],[f427,f318])).

fof(f427,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl15_55 ),
    inference(resolution,[],[f398,f165])).

fof(f426,plain,
    ( spl15_60
    | ~ spl15_30
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f419,f291,f284,f424])).

fof(f284,plain,
    ( spl15_30
  <=> v1_orders_2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f419,plain,
    ( g1_orders_2(u1_struct_0(sK12),u1_orders_2(sK12)) = sK12
    | ~ spl15_30
    | ~ spl15_32 ),
    inference(subsumption_resolution,[],[f410,f292])).

fof(f410,plain,
    ( ~ l1_orders_2(sK12)
    | g1_orders_2(u1_struct_0(sK12),u1_orders_2(sK12)) = sK12
    | ~ spl15_30 ),
    inference(resolution,[],[f134,f285])).

fof(f285,plain,
    ( v1_orders_2(sK12)
    | ~ spl15_30 ),
    inference(avatar_component_clause,[],[f284])).

fof(f418,plain,
    ( spl15_58
    | ~ spl15_24
    | ~ spl15_28 ),
    inference(avatar_split_clause,[],[f411,f277,f263,f416])).

fof(f263,plain,
    ( spl15_24
  <=> v1_orders_2(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f411,plain,
    ( g1_orders_2(u1_struct_0(sK11),u1_orders_2(sK11)) = sK11
    | ~ spl15_24
    | ~ spl15_28 ),
    inference(subsumption_resolution,[],[f409,f278])).

fof(f409,plain,
    ( ~ l1_orders_2(sK11)
    | g1_orders_2(u1_struct_0(sK11),u1_orders_2(sK11)) = sK11
    | ~ spl15_24 ),
    inference(resolution,[],[f134,f264])).

fof(f264,plain,
    ( v1_orders_2(sK11)
    | ~ spl15_24 ),
    inference(avatar_component_clause,[],[f263])).

fof(f408,plain,
    ( ~ spl15_57
    | ~ spl15_36
    | spl15_53 ),
    inference(avatar_split_clause,[],[f401,f390,f310,f406])).

fof(f401,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_36
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f400,f311])).

fof(f400,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl15_53 ),
    inference(resolution,[],[f391,f165])).

fof(f399,plain,
    ( spl15_50
    | ~ spl15_55
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f374,f207,f397,f384])).

fof(f207,plain,
    ( spl15_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f374,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK3)
    | ~ spl15_8 ),
    inference(resolution,[],[f148,f208])).

fof(f208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f207])).

fof(f392,plain,
    ( spl15_50
    | ~ spl15_53
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f373,f200,f390,f384])).

fof(f373,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | ~ spl15_6 ),
    inference(resolution,[],[f148,f201])).

fof(f367,plain,
    ( spl15_48
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f349,f207,f365])).

fof(f349,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl15_8 ),
    inference(resolution,[],[f139,f208])).

fof(f360,plain,
    ( spl15_46
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f348,f200,f358])).

fof(f348,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl15_6 ),
    inference(resolution,[],[f139,f201])).

fof(f340,plain,
    ( spl15_44
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f305,f291,f338])).

fof(f338,plain,
    ( spl15_44
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f305,plain,
    ( l1_struct_0(sK12)
    | ~ spl15_32 ),
    inference(resolution,[],[f137,f292])).

fof(f333,plain,
    ( spl15_42
    | ~ spl15_28 ),
    inference(avatar_split_clause,[],[f304,f277,f331])).

fof(f304,plain,
    ( l1_struct_0(sK11)
    | ~ spl15_28 ),
    inference(resolution,[],[f137,f278])).

fof(f326,plain,
    ( spl15_40
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f303,f242,f324])).

fof(f324,plain,
    ( spl15_40
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f303,plain,
    ( l1_struct_0(sK6)
    | ~ spl15_18 ),
    inference(resolution,[],[f137,f243])).

fof(f319,plain,
    ( spl15_38
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f302,f193,f317])).

fof(f302,plain,
    ( l1_struct_0(sK1)
    | ~ spl15_4 ),
    inference(resolution,[],[f137,f194])).

fof(f312,plain,
    ( spl15_36
    | ~ spl15_0 ),
    inference(avatar_split_clause,[],[f301,f179,f310])).

fof(f301,plain,
    ( l1_struct_0(sK0)
    | ~ spl15_0 ),
    inference(resolution,[],[f137,f180])).

fof(f300,plain,(
    spl15_34 ),
    inference(avatar_split_clause,[],[f164,f298])).

fof(f298,plain,
    ( spl15_34
  <=> l1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f164,plain,(
    l1_struct_0(sK13) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',existence_l1_struct_0)).

fof(f293,plain,(
    spl15_32 ),
    inference(avatar_split_clause,[],[f158,f291])).

fof(f158,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ? [X0] :
      ( v1_orders_2(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc1_orders_2)).

fof(f286,plain,(
    spl15_30 ),
    inference(avatar_split_clause,[],[f159,f284])).

fof(f159,plain,(
    v1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f54])).

fof(f279,plain,(
    spl15_28 ),
    inference(avatar_split_clause,[],[f155,f277])).

fof(f155,plain,(
    l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,axiom,(
    ? [X0] :
      ( v1_orders_2(X0)
      & v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc4_orders_2)).

fof(f272,plain,(
    spl15_26 ),
    inference(avatar_split_clause,[],[f156,f270])).

fof(f156,plain,(
    v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f65])).

fof(f265,plain,(
    spl15_24 ),
    inference(avatar_split_clause,[],[f157,f263])).

fof(f157,plain,(
    v1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f65])).

fof(f258,plain,(
    ~ spl15_23 ),
    inference(avatar_split_clause,[],[f145,f256])).

fof(f256,plain,
    ( spl15_23
  <=> ~ v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f145,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc2_xboole_0)).

fof(f251,plain,(
    spl15_20 ),
    inference(avatar_split_clause,[],[f144,f249])).

fof(f144,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',rc1_xboole_0)).

fof(f244,plain,(
    spl15_18 ),
    inference(avatar_split_clause,[],[f136,f242])).

fof(f136,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',existence_l1_orders_2)).

fof(f237,plain,
    ( spl15_14
    | ~ spl15_17 ),
    inference(avatar_split_clause,[],[f172,f234,f227])).

fof(f227,plain,
    ( spl15_14
  <=> v13_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f172,plain,
    ( ~ v12_waybel_0(sK3,sK1)
    | v13_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f113,f118])).

fof(f118,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => ( ( v13_waybel_0(X2,X0)
                           => v13_waybel_0(X3,X1) )
                          & ( v12_waybel_0(X2,X0)
                           => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t25_waybel_0)).

fof(f113,plain,
    ( ~ v12_waybel_0(sK3,sK1)
    | v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f236,plain,
    ( ~ spl15_11
    | ~ spl15_17 ),
    inference(avatar_split_clause,[],[f114,f234,f214])).

fof(f114,plain,
    ( ~ v12_waybel_0(sK3,sK1)
    | ~ v13_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f229,plain,
    ( spl15_14
    | spl15_12 ),
    inference(avatar_split_clause,[],[f171,f220,f227])).

fof(f171,plain,
    ( v12_waybel_0(sK3,sK0)
    | v13_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f115,f118,f118])).

fof(f115,plain,
    ( v12_waybel_0(sK2,sK0)
    | v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f222,plain,
    ( ~ spl15_11
    | spl15_12 ),
    inference(avatar_split_clause,[],[f170,f220,f214])).

fof(f170,plain,
    ( v12_waybel_0(sK3,sK0)
    | ~ v13_waybel_0(sK3,sK1) ),
    inference(definition_unfolding,[],[f116,f118])).

fof(f116,plain,
    ( v12_waybel_0(sK2,sK0)
    | ~ v13_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f209,plain,(
    spl15_8 ),
    inference(avatar_split_clause,[],[f117,f207])).

fof(f117,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f82])).

fof(f202,plain,(
    spl15_6 ),
    inference(avatar_split_clause,[],[f169,f200])).

fof(f169,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f119,f118])).

fof(f119,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f195,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f120,f193])).

fof(f120,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f188,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f121,f186])).

fof(f121,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f82])).

fof(f181,plain,(
    spl15_0 ),
    inference(avatar_split_clause,[],[f122,f179])).

fof(f122,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
