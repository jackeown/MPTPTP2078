%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t28_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       : 1425 (8240 expanded)
%              Number of leaves         :  380 (3020 expanded)
%              Depth                    :   16
%              Number of atoms          : 3632 (17559 expanded)
%              Number of equality atoms :  234 (2368 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f139,f146,f153,f160,f167,f174,f181,f190,f197,f207,f214,f230,f252,f260,f269,f279,f309,f357,f377,f396,f413,f426,f435,f442,f458,f481,f492,f524,f561,f601,f610,f629,f638,f650,f663,f671,f678,f687,f694,f711,f726,f747,f757,f764,f772,f783,f798,f813,f820,f853,f897,f904,f911,f924,f937,f944,f960,f978,f1000,f1007,f1014,f1035,f1047,f1054,f1074,f1081,f1114,f1127,f1149,f1156,f1172,f1179,f1196,f1203,f1210,f1226,f1233,f1263,f1270,f1277,f1332,f1351,f1358,f1365,f1373,f1380,f1387,f1394,f1419,f1426,f1433,f1440,f1450,f1457,f1472,f1479,f1511,f1518,f1525,f1532,f1542,f1549,f1571,f1578,f1609,f1617,f1624,f1637,f1650,f2088,f2125,f2132,f2171,f2183,f2193,f2200,f2207,f2220,f2508,f2513,f2520,f2527,f2531,f2541,f2562,f2564,f2566,f2582,f2584,f2590,f2592,f2598,f2622,f2645,f2666,f2674,f2750,f2873,f2880,f2907,f2914,f2932,f3000,f3056,f3092,f3102,f3141,f3148,f3181,f3251,f3258,f3265,f3272,f3328,f3336,f3343,f3350,f3357,f3364,f3366,f3389,f3413,f3420,f3427,f3461,f3482,f3532,f3539,f3546,f3553,f3562,f3569,f3576,f3672,f3679,f3686,f3693,f3700,f3766,f3773,f3780,f3797,f3852,f3891,f3912,f3935,f3957,f3976,f3983,f4001,f4024,f4073,f4080,f4153,f4160,f4167,f4215,f4226,f4233,f4242,f4249,f4256,f4288,f4316,f4323,f4330,f4342,f4353,f4360,f4370,f4377,f4405,f4434,f4441,f4491,f4498,f4569,f4576,f4583,f4590,f4628,f4752,f4759,f4766,f4773,f4874,f4881,f4888,f4895,f4902,f5007,f5023,f5038,f5066,f5078,f5085,f5096,f5121,f5134,f5161,f5168,f5179,f5186,f5287,f5295,f5302,f5309,f5316,f5323,f5490,f5497,f5504,f5511,f5518,f5686,f5693,f5700,f5798,f5805,f5812,f5831,f5838,f5845,f5852,f5859,f5872,f5879,f5886,f6139,f6146,f6153,f6160,f6167,f6174,f6194,f6201,f6204,f6223,f6230,f6237,f6244,f6251,f6266,f6273,f6280,f6287,f6294,f6308,f6315,f6322,f6329,f6336,f6353,f6407,f6415,f6422,f6429,f6436,f6443,f6450,f6457,f6472,f6554,f6566,f6573,f6605,f6612,f6626,f6654,f6668,f6698,f6705,f6712,f6719,f6746,f6753,f6775,f6782,f6802,f6811,f6843,f6850,f6888,f6927,f6934,f6941,f6948,f6973,f7021,f7028,f7035,f7051,f7058,f7065,f7078,f7094,f7105,f7168,f7200,f7217,f7232,f7239,f7275,f7293,f7775,f7780,f7783,f7790,f7797,f7800,f7863,f7907])).

fof(f7907,plain,
    ( ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | spl5_149
    | ~ spl5_240
    | ~ spl5_338 ),
    inference(avatar_contradiction_clause,[],[f7906])).

fof(f7906,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_149
    | ~ spl5_240
    | ~ spl5_338 ),
    inference(subsumption_resolution,[],[f7483,f1171])).

fof(f1171,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_149 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1170,plain,
    ( spl5_149
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f7483,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_240
    | ~ spl5_338 ),
    inference(backward_demodulation,[],[f7338,f3796])).

fof(f3796,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_338 ),
    inference(avatar_component_clause,[],[f3795])).

fof(f3795,plain,
    ( spl5_338
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_338])])).

fof(f7338,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7337,f395])).

fof(f395,plain,
    ( ~ v4_pre_topc(k3_tarski(sK1),sK0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl5_43
  <=> ~ v4_pre_topc(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f7337,plain,
    ( v4_pre_topc(k3_tarski(sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_20
    | ~ spl5_48
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7336,f434])).

fof(f434,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl5_48
  <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f7336,plain,
    ( v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_20
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7311,f206])).

fof(f206,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f7311,plain,
    ( v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_240 ),
    inference(superposition,[],[f2206,f1563])).

fof(f1563,plain,(
    ! [X2,X3] :
      ( k5_setfam_1(X2,X3) = k3_subset_1(X2,k1_setfam_1(k7_setfam_1(X2,X3)))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(subsumption_resolution,[],[f1556,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',dt_k5_setfam_1)).

fof(f1556,plain,(
    ! [X2,X3] :
      ( k5_setfam_1(X2,X3) = k3_subset_1(X2,k1_setfam_1(k7_setfam_1(X2,X3)))
      | ~ m1_subset_1(k5_setfam_1(X2,X3),k1_zfmisc_1(X2))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f111,f789])).

fof(f789,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k5_setfam_1(X2,X3)) = k1_setfam_1(k7_setfam_1(X2,X3))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(subsumption_resolution,[],[f785,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',dt_k7_setfam_1)).

fof(f785,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k5_setfam_1(X2,X3)) = k1_setfam_1(k7_setfam_1(X2,X3))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(k7_setfam_1(X2,X3),k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f119,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',redefinition_k6_setfam_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t11_tops_2)).

fof(f111,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',involutiveness_k3_subset_1)).

fof(f2206,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl5_240 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f2205,plain,
    ( spl5_240
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_240])])).

fof(f7863,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | spl5_125
    | ~ spl5_240
    | ~ spl5_244 ),
    inference(avatar_contradiction_clause,[],[f7862])).

fof(f7862,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_125
    | ~ spl5_240
    | ~ spl5_244 ),
    inference(subsumption_resolution,[],[f7861,f999])).

fof(f999,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_125 ),
    inference(avatar_component_clause,[],[f998])).

fof(f998,plain,
    ( spl5_125
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f7861,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_240
    | ~ spl5_244 ),
    inference(forward_demodulation,[],[f7443,f180])).

fof(f180,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_14
  <=> k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f7443,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_240
    | ~ spl5_244 ),
    inference(backward_demodulation,[],[f7338,f2219])).

fof(f2219,plain,
    ( r2_hidden(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_244 ),
    inference(avatar_component_clause,[],[f2218])).

fof(f2218,plain,
    ( spl5_244
  <=> r2_hidden(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_244])])).

fof(f7800,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | ~ spl5_38
    | spl5_43
    | ~ spl5_48
    | spl5_71
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7799])).

fof(f7799,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_38
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_71
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7798,f356])).

fof(f356,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl5_38
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f7798,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_71
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7353,f180])).

fof(f7353,plain,
    ( ~ r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_71
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f649])).

fof(f649,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl5_71
  <=> ~ r2_hidden(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f7797,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | ~ spl5_28
    | spl5_43
    | ~ spl5_48
    | spl5_69
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7796])).

fof(f7796,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_28
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_69
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7795,f259])).

fof(f259,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl5_28
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f7795,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_69
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7352,f180])).

fof(f7352,plain,
    ( ~ m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_69
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f637])).

fof(f637,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl5_69
  <=> ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f7790,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | ~ spl5_64
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7789])).

fof(f7789,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_64
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7788,f200])).

fof(f200,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f152,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t7_boole)).

fof(f152,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f7788,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_64
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7349,f180])).

fof(f7349,plain,
    ( r2_hidden(sK2(k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_64
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f609])).

fof(f609,plain,
    ( r2_hidden(sK2(k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl5_64
  <=> r2_hidden(sK2(k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f7783,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | spl5_63
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7782])).

fof(f7782,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_63
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7781,f152])).

fof(f7781,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_63
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7347,f180])).

fof(f7347,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_63
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f600])).

fof(f600,plain,
    ( ~ v1_xboole_0(k3_tarski(sK1))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl5_63
  <=> ~ v1_xboole_0(k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f7780,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | ~ spl5_52
    | spl5_121
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7779])).

fof(f7779,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_52
    | ~ spl5_121
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7778,f959])).

fof(f959,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f958])).

fof(f958,plain,
    ( spl5_121
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f7778,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_52
    | ~ spl5_240 ),
    inference(forward_demodulation,[],[f7345,f180])).

fof(f7345,plain,
    ( m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_52
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f457])).

fof(f457,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl5_52
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f7775,plain,
    ( ~ spl5_20
    | spl5_43
    | ~ spl5_48
    | spl5_145
    | ~ spl5_240 ),
    inference(avatar_contradiction_clause,[],[f7774])).

fof(f7774,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_145
    | ~ spl5_240 ),
    inference(subsumption_resolution,[],[f7341,f1148])).

fof(f1148,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_145 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1147,plain,
    ( spl5_145
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f7341,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_48
    | ~ spl5_240 ),
    inference(backward_demodulation,[],[f7338,f206])).

fof(f7293,plain,
    ( ~ spl5_667
    | ~ spl5_664 ),
    inference(avatar_split_clause,[],[f7279,f7273,f7291])).

fof(f7291,plain,
    ( spl5_667
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_667])])).

fof(f7273,plain,
    ( spl5_664
  <=> r2_hidden(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_664])])).

fof(f7279,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_setfam_1(sK1)))
    | ~ spl5_664 ),
    inference(unit_resulting_resolution,[],[f7274,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',antisymmetry_r2_hidden)).

fof(f7274,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_664 ),
    inference(avatar_component_clause,[],[f7273])).

fof(f7275,plain,
    ( spl5_664
    | spl5_67
    | ~ spl5_660 ),
    inference(avatar_split_clause,[],[f7257,f7230,f627,f7273])).

fof(f627,plain,
    ( spl5_67
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f7230,plain,
    ( spl5_660
  <=> m1_subset_1(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_660])])).

fof(f7257,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_67
    | ~ spl5_660 ),
    inference(unit_resulting_resolution,[],[f628,f7231,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t2_subset)).

fof(f7231,plain,
    ( m1_subset_1(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_660 ),
    inference(avatar_component_clause,[],[f7230])).

fof(f628,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f627])).

fof(f7239,plain,
    ( ~ spl5_663
    | ~ spl5_652 ),
    inference(avatar_split_clause,[],[f7111,f7103,f7237])).

fof(f7237,plain,
    ( spl5_663
  <=> ~ r2_hidden(k1_setfam_1(sK1),sK2(k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_663])])).

fof(f7103,plain,
    ( spl5_652
  <=> r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_652])])).

fof(f7111,plain,
    ( ~ r2_hidden(k1_setfam_1(sK1),sK2(k1_setfam_1(sK1)))
    | ~ spl5_652 ),
    inference(unit_resulting_resolution,[],[f7104,f107])).

fof(f7104,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1))
    | ~ spl5_652 ),
    inference(avatar_component_clause,[],[f7103])).

fof(f7232,plain,
    ( spl5_660
    | ~ spl5_54
    | ~ spl5_652 ),
    inference(avatar_split_clause,[],[f7106,f7103,f479,f7230])).

fof(f479,plain,
    ( spl5_54
  <=> m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f7106,plain,
    ( m1_subset_1(sK2(k1_setfam_1(sK1)),u1_struct_0(sK0))
    | ~ spl5_54
    | ~ spl5_652 ),
    inference(unit_resulting_resolution,[],[f480,f7104,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t4_subset)).

fof(f480,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f479])).

fof(f7217,plain,
    ( ~ spl5_659
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | spl5_261
    | spl5_647 ),
    inference(avatar_split_clause,[],[f7080,f7067,f2998,f479,f137,f130,f7215])).

fof(f7215,plain,
    ( spl5_659
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_659])])).

fof(f130,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f137,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2998,plain,
    ( spl5_261
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_261])])).

fof(f7067,plain,
    ( spl5_647
  <=> ~ v4_pre_topc(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_647])])).

fof(f7080,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | ~ spl5_261
    | ~ spl5_647 ),
    inference(unit_resulting_resolution,[],[f2999,f480,f7068,f947])).

fof(f947,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(resolution,[],[f594,f109])).

fof(f594,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f593,f138])).

fof(f138,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f593,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f104,f131])).

fof(f131,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f130])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',cc2_pre_topc)).

fof(f7068,plain,
    ( ~ v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl5_647 ),
    inference(avatar_component_clause,[],[f7067])).

fof(f2999,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK1))
    | ~ spl5_261 ),
    inference(avatar_component_clause,[],[f2998])).

fof(f7200,plain,
    ( ~ spl5_657
    | spl5_655 ),
    inference(avatar_split_clause,[],[f7191,f7166,f7198])).

fof(f7198,plain,
    ( spl5_657
  <=> ~ r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_657])])).

fof(f7166,plain,
    ( spl5_655
  <=> ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_655])])).

fof(f7191,plain,
    ( ~ r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_655 ),
    inference(unit_resulting_resolution,[],[f7167,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t1_subset)).

fof(f7167,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_655 ),
    inference(avatar_component_clause,[],[f7166])).

fof(f7168,plain,
    ( ~ spl5_655
    | ~ spl5_6
    | ~ spl5_652 ),
    inference(avatar_split_clause,[],[f7107,f7103,f151,f7166])).

fof(f7107,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_652 ),
    inference(unit_resulting_resolution,[],[f152,f7104,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t5_subset)).

fof(f7105,plain,
    ( spl5_652
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | spl5_647 ),
    inference(avatar_split_clause,[],[f7079,f7067,f479,f137,f130,f7103])).

fof(f7079,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | ~ spl5_647 ),
    inference(unit_resulting_resolution,[],[f106,f480,f7068,f947])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',existence_m1_subset_1)).

fof(f7094,plain,
    ( ~ spl5_651
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | spl5_647 ),
    inference(avatar_split_clause,[],[f7083,f7067,f479,f137,f130,f7092])).

fof(f7092,plain,
    ( spl5_651
  <=> ~ v1_xboole_0(k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_651])])).

fof(f7083,plain,
    ( ~ v1_xboole_0(k1_setfam_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_54
    | ~ spl5_647 ),
    inference(unit_resulting_resolution,[],[f131,f138,f480,f7068,f104])).

fof(f7078,plain,
    ( spl5_646
    | ~ spl5_649
    | ~ spl5_2
    | ~ spl5_54
    | ~ spl5_638 ),
    inference(avatar_split_clause,[],[f7044,f7033,f479,f137,f7076,f7070])).

fof(f7070,plain,
    ( spl5_646
  <=> v4_pre_topc(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_646])])).

fof(f7076,plain,
    ( spl5_649
  <=> ~ v3_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_649])])).

fof(f7033,plain,
    ( spl5_638
  <=> k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_638])])).

fof(f7044,plain,
    ( ~ v3_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl5_2
    | ~ spl5_54
    | ~ spl5_638 ),
    inference(subsumption_resolution,[],[f7043,f138])).

fof(f7043,plain,
    ( ~ v3_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_54
    | ~ spl5_638 ),
    inference(subsumption_resolution,[],[f7039,f480])).

fof(f7039,plain,
    ( ~ v3_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_638 ),
    inference(superposition,[],[f100,f7034])).

fof(f7034,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_638 ),
    inference(avatar_component_clause,[],[f7033])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t29_tops_1)).

fof(f7065,plain,
    ( ~ spl5_645
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6644,f6610,f7063])).

fof(f7063,plain,
    ( spl5_645
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_645])])).

fof(f6610,plain,
    ( spl5_591
  <=> ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_591])])).

fof(f6644,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f472,f6611,f122])).

fof(f6611,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_591 ),
    inference(avatar_component_clause,[],[f6610])).

fof(f472,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f467,f416])).

fof(f416,plain,(
    ! [X0] : k6_setfam_1(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) = k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f106,f114])).

fof(f467,plain,(
    ! [X0] : m1_subset_1(k6_setfam_1(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f106,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',dt_k6_setfam_1)).

fof(f7058,plain,
    ( ~ spl5_643
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6639,f6610,f7056])).

fof(f7056,plain,
    ( spl5_643
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_643])])).

fof(f6639,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f449,f6611,f122])).

fof(f449,plain,(
    ! [X0] : m1_subset_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f445,f380])).

fof(f380,plain,(
    ! [X0] : k5_setfam_1(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) = k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f106,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',redefinition_k5_setfam_1)).

fof(f445,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f106,f115])).

fof(f7051,plain,
    ( ~ spl5_641
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6634,f6610,f7049])).

fof(f7049,plain,
    ( spl5_641
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_641])])).

fof(f6634,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f552,f6611,f122])).

fof(f552,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,sK2(k1_zfmisc_1(k1_zfmisc_1(X0)))),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f106,f118])).

fof(f7035,plain,
    ( spl5_638
    | ~ spl5_116
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6476,f6470,f942,f7033])).

fof(f942,plain,
    ( spl5_116
  <=> m1_subset_1(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f6470,plain,
    ( spl5_580
  <=> k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_580])])).

fof(f6476,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_116
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6471,f1139])).

fof(f1139,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)))) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f943,f111])).

fof(f943,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f942])).

fof(f6471,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1)
    | ~ spl5_580 ),
    inference(avatar_component_clause,[],[f6470])).

fof(f7028,plain,
    ( spl5_636
    | ~ spl5_116
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6475,f6470,f942,f7026])).

fof(f7026,plain,
    ( spl5_636
  <=> k4_xboole_0(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_636])])).

fof(f6475,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1)
    | ~ spl5_116
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6471,f1138])).

fof(f1138,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f943,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',d5_subset_1)).

fof(f7021,plain,
    ( ~ spl5_635
    | spl5_609 ),
    inference(avatar_split_clause,[],[f6767,f6751,f7019])).

fof(f7019,plain,
    ( spl5_635
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_635])])).

fof(f6751,plain,
    ( spl5_609
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_609])])).

fof(f6767,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))))
    | ~ spl5_609 ),
    inference(unit_resulting_resolution,[],[f106,f6752,f122])).

fof(f6752,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_609 ),
    inference(avatar_component_clause,[],[f6751])).

fof(f6973,plain,
    ( ~ spl5_633
    | spl5_603 ),
    inference(avatar_split_clause,[],[f6738,f6710,f6971])).

fof(f6971,plain,
    ( spl5_633
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_633])])).

fof(f6710,plain,
    ( spl5_603
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_603])])).

fof(f6738,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))))
    | ~ spl5_603 ),
    inference(unit_resulting_resolution,[],[f106,f6711,f122])).

fof(f6711,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_603 ),
    inference(avatar_component_clause,[],[f6710])).

fof(f6948,plain,
    ( ~ spl5_631
    | spl5_597 ),
    inference(avatar_split_clause,[],[f6687,f6666,f6946])).

fof(f6946,plain,
    ( spl5_631
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_631])])).

fof(f6666,plain,
    ( spl5_597
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_597])])).

fof(f6687,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_597 ),
    inference(unit_resulting_resolution,[],[f106,f6667,f122])).

fof(f6667,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_597 ),
    inference(avatar_component_clause,[],[f6666])).

fof(f6941,plain,
    ( ~ spl5_629
    | spl5_587 ),
    inference(avatar_split_clause,[],[f6596,f6571,f6939])).

fof(f6939,plain,
    ( spl5_629
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_629])])).

fof(f6571,plain,
    ( spl5_587
  <=> ~ m1_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_587])])).

fof(f6596,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))))))
    | ~ spl5_587 ),
    inference(unit_resulting_resolution,[],[f472,f6572,f122])).

fof(f6572,plain,
    ( ~ m1_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_587 ),
    inference(avatar_component_clause,[],[f6571])).

fof(f6934,plain,
    ( ~ spl5_627
    | spl5_587 ),
    inference(avatar_split_clause,[],[f6591,f6571,f6932])).

fof(f6932,plain,
    ( spl5_627
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_627])])).

fof(f6591,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))))))
    | ~ spl5_587 ),
    inference(unit_resulting_resolution,[],[f449,f6572,f122])).

fof(f6927,plain,
    ( ~ spl5_625
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6525,f6461,f6925])).

fof(f6925,plain,
    ( spl5_625
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_625])])).

fof(f6461,plain,
    ( spl5_579
  <=> k7_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_579])])).

fof(f6525,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f6462,f340])).

fof(f340,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2(X5))
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f325,f107])).

fof(f325,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f219,f106])).

fof(f219,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f109,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t6_boole)).

fof(f6462,plain,
    ( k7_setfam_1(u1_struct_0(sK0),sK1) != k1_xboole_0
    | ~ spl5_579 ),
    inference(avatar_component_clause,[],[f6461])).

fof(f6888,plain,
    ( spl5_622
    | ~ spl5_6
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6531,f6461,f151,f6886])).

fof(f6886,plain,
    ( spl5_622
  <=> r2_hidden(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_622])])).

fof(f6531,plain,
    ( r2_hidden(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f200,f106,f106,f6462,f1251])).

fof(f1251,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,X3)
      | X3 = X4
      | r2_hidden(X2,X3)
      | r2_hidden(X5,X4)
      | ~ m1_subset_1(X5,X4) ) ),
    inference(resolution,[],[f218,f109])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | X1 = X2
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f109,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t8_boole)).

fof(f6850,plain,
    ( ~ spl5_621
    | spl5_249
    | ~ spl5_610 ),
    inference(avatar_split_clause,[],[f6783,f6773,f2748,f6848])).

fof(f6848,plain,
    ( spl5_621
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_621])])).

fof(f2748,plain,
    ( spl5_249
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_249])])).

fof(f6773,plain,
    ( spl5_610
  <=> m1_subset_1(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_610])])).

fof(f6783,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_249
    | ~ spl5_610 ),
    inference(unit_resulting_resolution,[],[f6774,f3522])).

fof(f3522,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_249 ),
    inference(resolution,[],[f2763,f107])).

fof(f2763,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_249 ),
    inference(resolution,[],[f2749,f109])).

fof(f2749,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_249 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f6774,plain,
    ( m1_subset_1(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_610 ),
    inference(avatar_component_clause,[],[f6773])).

fof(f6843,plain,
    ( ~ spl5_619
    | ~ spl5_116
    | spl5_451
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6489,f6470,f5094,f942,f6841])).

fof(f6841,plain,
    ( spl5_619
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_619])])).

fof(f5094,plain,
    ( spl5_451
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_451])])).

fof(f6489,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_116
    | ~ spl5_451
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6476,f5095])).

fof(f5095,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_451 ),
    inference(avatar_component_clause,[],[f5094])).

fof(f6811,plain,
    ( spl5_616
    | spl5_249
    | ~ spl5_610 ),
    inference(avatar_split_clause,[],[f6793,f6773,f2748,f6809])).

fof(f6809,plain,
    ( spl5_616
  <=> r2_hidden(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_616])])).

fof(f6793,plain,
    ( r2_hidden(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_249
    | ~ spl5_610 ),
    inference(unit_resulting_resolution,[],[f2749,f6774,f109])).

fof(f6802,plain,
    ( ~ spl5_615
    | ~ spl5_6
    | spl5_353
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6533,f6461,f3981,f151,f6800])).

fof(f6800,plain,
    ( spl5_615
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_615])])).

fof(f3981,plain,
    ( spl5_353
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_353])])).

fof(f6533,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_353
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f200,f106,f3982,f6462,f1251])).

fof(f3982,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_353 ),
    inference(avatar_component_clause,[],[f3981])).

fof(f6782,plain,
    ( ~ spl5_613
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6645,f6610,f6780])).

fof(f6780,plain,
    ( spl5_613
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_613])])).

fof(f6645,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f106,f6611,f122])).

fof(f6775,plain,
    ( spl5_610
    | ~ spl5_100
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6522,f6461,f818,f6773])).

fof(f818,plain,
    ( spl5_100
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f6522,plain,
    ( m1_subset_1(sK2(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_100
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f819,f6462,f337])).

fof(f337,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f325,f122])).

fof(f819,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f818])).

fof(f6753,plain,
    ( ~ spl5_609
    | ~ spl5_6
    | spl5_389
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6532,f6461,f4340,f151,f6751])).

fof(f4340,plain,
    ( spl5_389
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_389])])).

fof(f6532,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_389
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f200,f106,f4341,f6462,f1251])).

fof(f4341,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_389 ),
    inference(avatar_component_clause,[],[f4340])).

fof(f6746,plain,
    ( ~ spl5_607
    | spl5_603 ),
    inference(avatar_split_clause,[],[f6739,f6710,f6744])).

fof(f6744,plain,
    ( spl5_607
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_607])])).

fof(f6739,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_603 ),
    inference(unit_resulting_resolution,[],[f6711,f108])).

fof(f6719,plain,
    ( spl5_604
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f983,f909,f6717])).

fof(f6717,plain,
    ( spl5_604
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_604])])).

fof(f909,plain,
    ( spl5_108
  <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f983,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',involutiveness_k7_setfam_1)).

fof(f910,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_108 ),
    inference(avatar_component_clause,[],[f909])).

fof(f6712,plain,
    ( ~ spl5_603
    | ~ spl5_38
    | spl5_587 ),
    inference(avatar_split_clause,[],[f6583,f6571,f355,f6710])).

fof(f6583,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_38
    | ~ spl5_587 ),
    inference(unit_resulting_resolution,[],[f356,f6572,f122])).

fof(f6705,plain,
    ( ~ spl5_601
    | spl5_597 ),
    inference(avatar_split_clause,[],[f6688,f6666,f6703])).

fof(f6703,plain,
    ( spl5_601
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_601])])).

fof(f6688,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_597 ),
    inference(unit_resulting_resolution,[],[f6667,f108])).

fof(f6698,plain,
    ( ~ spl5_599
    | spl5_587 ),
    inference(avatar_split_clause,[],[f6597,f6571,f6696])).

fof(f6696,plain,
    ( spl5_599
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_599])])).

fof(f6597,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k7_setfam_1(u1_struct_0(sK0),sK1))))
    | ~ spl5_587 ),
    inference(unit_resulting_resolution,[],[f106,f6572,f122])).

fof(f6668,plain,
    ( ~ spl5_597
    | ~ spl5_348
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6646,f6610,f3955,f6666])).

fof(f3955,plain,
    ( spl5_348
  <=> r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_348])])).

fof(f6646,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_348
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f3956,f6611,f122])).

fof(f3956,plain,
    ( r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_348 ),
    inference(avatar_component_clause,[],[f3955])).

fof(f6654,plain,
    ( ~ spl5_595
    | spl5_591 ),
    inference(avatar_split_clause,[],[f6647,f6610,f6652])).

fof(f6652,plain,
    ( spl5_595
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_595])])).

fof(f6647,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_591 ),
    inference(unit_resulting_resolution,[],[f6611,f108])).

fof(f6626,plain,
    ( spl5_592
    | ~ spl5_116
    | ~ spl5_282
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6481,f6470,f3326,f942,f6624])).

fof(f6624,plain,
    ( spl5_592
  <=> k4_xboole_0(u1_struct_0(sK0),k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_592])])).

fof(f3326,plain,
    ( spl5_282
  <=> k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_282])])).

fof(f6481,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_116
    | ~ spl5_282
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6476,f3327])).

fof(f3327,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_setfam_1(sK1))
    | ~ spl5_282 ),
    inference(avatar_component_clause,[],[f3326])).

fof(f6612,plain,
    ( ~ spl5_591
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6528,f6461,f6610])).

fof(f6528,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f6462,f873])).

fof(f873,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f861,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',dt_k3_subset_1)).

fof(f861,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | ~ m1_subset_1(k3_subset_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f331,f111])).

fof(f331,plain,(
    ! [X3] :
      ( k3_subset_1(k1_xboole_0,X3) = k1_xboole_0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f112,f95])).

fof(f95,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t4_boole)).

fof(f6605,plain,
    ( ~ spl5_589
    | ~ spl5_116
    | spl5_445
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6485,f6470,f5055,f942,f6603])).

fof(f6603,plain,
    ( spl5_589
  <=> ~ v4_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_589])])).

fof(f5055,plain,
    ( spl5_445
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_445])])).

fof(f6485,plain,
    ( ~ v4_pre_topc(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl5_116
    | ~ spl5_445
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6476,f5056])).

fof(f5056,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ spl5_445 ),
    inference(avatar_component_clause,[],[f5055])).

fof(f6573,plain,
    ( ~ spl5_587
    | ~ spl5_6
    | spl5_127
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6534,f6461,f1005,f151,f6571])).

fof(f1005,plain,
    ( spl5_127
  <=> ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f6534,plain,
    ( ~ m1_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_127
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f200,f106,f1006,f6462,f1251])).

fof(f1006,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_127 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f6566,plain,
    ( ~ spl5_585
    | ~ spl5_116
    | spl5_449
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6488,f6470,f5083,f942,f6564])).

fof(f6564,plain,
    ( spl5_585
  <=> ~ v1_xboole_0(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_585])])).

fof(f5083,plain,
    ( spl5_449
  <=> ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_449])])).

fof(f6488,plain,
    ( ~ v1_xboole_0(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_116
    | ~ spl5_449
    | ~ spl5_580 ),
    inference(backward_demodulation,[],[f6476,f5084])).

fof(f5084,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_449 ),
    inference(avatar_component_clause,[],[f5083])).

fof(f6554,plain,
    ( ~ spl5_583
    | ~ spl5_6
    | spl5_579 ),
    inference(avatar_split_clause,[],[f6536,f6461,f151,f6552])).

fof(f6552,plain,
    ( spl5_583
  <=> ~ v1_xboole_0(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_583])])).

fof(f6536,plain,
    ( ~ v1_xboole_0(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_6
    | ~ spl5_579 ),
    inference(unit_resulting_resolution,[],[f152,f6462,f120])).

fof(f6472,plain,
    ( spl5_578
    | spl5_580
    | ~ spl5_50
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f844,f818,f811,f440,f6470,f6464])).

fof(f6464,plain,
    ( spl5_578
  <=> k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_578])])).

fof(f440,plain,
    ( spl5_50
  <=> k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f811,plain,
    ( spl5_98
  <=> k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f844,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1)
    | k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_50
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(backward_demodulation,[],[f831,f828])).

fof(f828,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(sK1)
    | k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_50
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f827,f441])).

fof(f441,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f440])).

fof(f827,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) = k6_setfam_1(u1_struct_0(sK0),sK1)
    | k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f823,f819])).

fof(f823,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) = k6_setfam_1(u1_struct_0(sK0),sK1)
    | k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_98 ),
    inference(superposition,[],[f119,f812])).

fof(f812,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f811])).

fof(f831,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f113])).

fof(f6457,plain,
    ( ~ spl5_577
    | spl5_45 ),
    inference(avatar_split_clause,[],[f4107,f411,f6455])).

fof(f6455,plain,
    ( spl5_577
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_577])])).

fof(f411,plain,
    ( spl5_45
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f4107,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f550,f122])).

fof(f550,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f472,f118])).

fof(f412,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f411])).

fof(f6450,plain,
    ( ~ spl5_575
    | spl5_45 ),
    inference(avatar_split_clause,[],[f4039,f411,f6448])).

fof(f6448,plain,
    ( spl5_575
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_575])])).

fof(f4039,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f549,f122])).

fof(f549,plain,(
    ! [X0] : m1_subset_1(k7_setfam_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f449,f118])).

fof(f6443,plain,
    ( ~ spl5_573
    | spl5_45 ),
    inference(avatar_split_clause,[],[f1935,f411,f6441])).

fof(f6441,plain,
    ( spl5_573
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_573])])).

fof(f1935,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f540,f122])).

fof(f540,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f532,f534])).

fof(f534,plain,(
    ! [X0] : k6_setfam_1(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f472,f114])).

fof(f532,plain,(
    ! [X0] : m1_subset_1(k6_setfam_1(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f472,f116])).

fof(f6436,plain,
    ( spl5_570
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f838,f818,f6434])).

fof(f6434,plain,
    ( spl5_570
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))) = k7_setfam_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_570])])).

fof(f838,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))) = k7_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f111])).

fof(f6429,plain,
    ( ~ spl5_569
    | spl5_45 ),
    inference(avatar_split_clause,[],[f1884,f411,f6427])).

fof(f6427,plain,
    ( spl5_569
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_569])])).

fof(f1884,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f539,f122])).

fof(f539,plain,(
    ! [X0] : m1_subset_1(k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f533,f535])).

fof(f535,plain,(
    ! [X0] : k5_setfam_1(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f472,f113])).

fof(f533,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f472,f115])).

fof(f6422,plain,
    ( ~ spl5_567
    | spl5_45 ),
    inference(avatar_split_clause,[],[f1770,f411,f6420])).

fof(f6420,plain,
    ( spl5_567
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_567])])).

fof(f1770,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f506,f122])).

fof(f506,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f498,f500])).

fof(f500,plain,(
    ! [X0] : k6_setfam_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f449,f114])).

fof(f498,plain,(
    ! [X0] : m1_subset_1(k6_setfam_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f449,f116])).

fof(f6415,plain,
    ( ~ spl5_565
    | spl5_45 ),
    inference(avatar_split_clause,[],[f1721,f411,f6413])).

fof(f6413,plain,
    ( spl5_565
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_565])])).

fof(f1721,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f505,f122])).

fof(f505,plain,(
    ! [X0] : m1_subset_1(k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f499,f501])).

fof(f501,plain,(
    ! [X0] : k5_setfam_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f449,f113])).

fof(f499,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f449,f115])).

fof(f6407,plain,
    ( spl5_562
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f837,f818,f6405])).

fof(f6405,plain,
    ( spl5_562
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_562])])).

fof(f837,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f112])).

fof(f6353,plain,
    ( ~ spl5_561
    | spl5_451 ),
    inference(avatar_split_clause,[],[f5110,f5094,f6351])).

fof(f6351,plain,
    ( spl5_561
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_561])])).

fof(f5110,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))))
    | ~ spl5_451 ),
    inference(unit_resulting_resolution,[],[f106,f5095,f122])).

fof(f6336,plain,
    ( ~ spl5_559
    | spl5_443 ),
    inference(avatar_split_clause,[],[f5052,f5036,f6334])).

fof(f6334,plain,
    ( spl5_559
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_559])])).

fof(f5036,plain,
    ( spl5_443
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_443])])).

fof(f5052,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))))
    | ~ spl5_443 ),
    inference(unit_resulting_resolution,[],[f106,f5037,f122])).

fof(f5037,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_443 ),
    inference(avatar_component_clause,[],[f5036])).

fof(f6329,plain,
    ( ~ spl5_557
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4306,f4286,f6327])).

fof(f6327,plain,
    ( spl5_557
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_557])])).

fof(f4286,plain,
    ( spl5_381
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_381])])).

fof(f4306,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f472,f4287,f122])).

fof(f4287,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_381 ),
    inference(avatar_component_clause,[],[f4286])).

fof(f6322,plain,
    ( ~ spl5_555
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4301,f4286,f6320])).

fof(f6320,plain,
    ( spl5_555
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_555])])).

fof(f4301,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f449,f4287,f122])).

fof(f6315,plain,
    ( ~ spl5_553
    | spl5_83 ),
    inference(avatar_split_clause,[],[f4110,f709,f6313])).

fof(f6313,plain,
    ( spl5_553
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_553])])).

fof(f709,plain,
    ( spl5_83
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f4110,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f550,f122])).

fof(f710,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f709])).

fof(f6308,plain,
    ( ~ spl5_551
    | spl5_83 ),
    inference(avatar_split_clause,[],[f4042,f709,f6306])).

fof(f6306,plain,
    ( spl5_551
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_551])])).

fof(f4042,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f549,f122])).

fof(f6294,plain,
    ( ~ spl5_549
    | spl5_355 ),
    inference(avatar_split_clause,[],[f4016,f3999,f6292])).

fof(f6292,plain,
    ( spl5_549
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_549])])).

fof(f3999,plain,
    ( spl5_355
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_355])])).

fof(f4016,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_355 ),
    inference(unit_resulting_resolution,[],[f106,f4000,f122])).

fof(f4000,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_355 ),
    inference(avatar_component_clause,[],[f3999])).

fof(f6287,plain,
    ( ~ spl5_547
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1937,f709,f6285])).

fof(f6285,plain,
    ( spl5_547
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_547])])).

fof(f1937,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f540,f122])).

fof(f6280,plain,
    ( ~ spl5_545
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1886,f709,f6278])).

fof(f6278,plain,
    ( spl5_545
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_545])])).

fof(f1886,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f539,f122])).

fof(f6273,plain,
    ( ~ spl5_543
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1772,f709,f6271])).

fof(f6271,plain,
    ( spl5_543
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_543])])).

fof(f1772,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f506,f122])).

fof(f6266,plain,
    ( ~ spl5_541
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1723,f709,f6264])).

fof(f6264,plain,
    ( spl5_541
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_541])])).

fof(f1723,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f505,f122])).

fof(f6251,plain,
    ( ~ spl5_539
    | spl5_199 ),
    inference(avatar_split_clause,[],[f1503,f1477,f6249])).

fof(f6249,plain,
    ( spl5_539
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_539])])).

fof(f1477,plain,
    ( spl5_199
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f1503,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f106,f1478,f122])).

fof(f1478,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_199 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f6244,plain,
    ( ~ spl5_537
    | ~ spl5_38
    | spl5_199 ),
    inference(avatar_split_clause,[],[f1498,f1477,f355,f6242])).

fof(f6242,plain,
    ( spl5_537
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_537])])).

fof(f1498,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_38
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f356,f1478,f122])).

fof(f6237,plain,
    ( ~ spl5_535
    | spl5_197 ),
    inference(avatar_split_clause,[],[f1485,f1470,f6235])).

fof(f6235,plain,
    ( spl5_535
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_535])])).

fof(f1470,plain,
    ( spl5_197
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f1485,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_197 ),
    inference(unit_resulting_resolution,[],[f106,f1471,f122])).

fof(f1471,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_197 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f6230,plain,
    ( ~ spl5_533
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1105,f1072,f6228])).

fof(f6228,plain,
    ( spl5_533
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_533])])).

fof(f1072,plain,
    ( spl5_137
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f1105,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f472,f1073,f122])).

fof(f1073,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f6223,plain,
    ( ~ spl5_531
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1104,f1072,f6221])).

fof(f6221,plain,
    ( spl5_531
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_531])])).

fof(f1104,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f449,f1073,f122])).

fof(f6204,plain,
    ( spl5_336
    | spl5_358
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f989,f909,f4071,f3789])).

fof(f3789,plain,
    ( spl5_336
  <=> k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_336])])).

fof(f4071,plain,
    ( spl5_358
  <=> r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_358])])).

fof(f989,plain,
    ( r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl5_108 ),
    inference(resolution,[],[f910,f219])).

fof(f6201,plain,
    ( ~ spl5_529
    | spl5_249 ),
    inference(avatar_split_clause,[],[f4257,f2748,f6199])).

fof(f6199,plain,
    ( spl5_529
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_529])])).

fof(f4257,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f222,f3522])).

fof(f222,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f106,f110])).

fof(f6194,plain,
    ( ~ spl5_527
    | spl5_263 ),
    inference(avatar_split_clause,[],[f3068,f3054,f6192])).

fof(f6192,plain,
    ( spl5_527
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_527])])).

fof(f3054,plain,
    ( spl5_263
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_263])])).

fof(f3068,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f472,f3055,f122])).

fof(f3055,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_263 ),
    inference(avatar_component_clause,[],[f3054])).

fof(f6174,plain,
    ( ~ spl5_525
    | spl5_263 ),
    inference(avatar_split_clause,[],[f3064,f3054,f6172])).

fof(f6172,plain,
    ( spl5_525
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_525])])).

fof(f3064,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f449,f3055,f122])).

fof(f6167,plain,
    ( ~ spl5_523
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1948,f1033,f6165])).

fof(f6165,plain,
    ( spl5_523
  <=> ~ r2_hidden(sK1,k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_523])])).

fof(f1033,plain,
    ( spl5_131
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f1948,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f540,f122])).

fof(f1034,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f6160,plain,
    ( ~ spl5_521
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1897,f1033,f6158])).

fof(f6158,plain,
    ( spl5_521
  <=> ~ r2_hidden(sK1,k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_521])])).

fof(f1897,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f539,f122])).

fof(f6153,plain,
    ( ~ spl5_519
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1783,f1033,f6151])).

fof(f6151,plain,
    ( spl5_519
  <=> ~ r2_hidden(sK1,k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_519])])).

fof(f1783,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f506,f122])).

fof(f6146,plain,
    ( ~ spl5_517
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1734,f1033,f6144])).

fof(f6144,plain,
    ( spl5_517
  <=> ~ r2_hidden(sK1,k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_517])])).

fof(f1734,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f505,f122])).

fof(f6139,plain,
    ( ~ spl5_515
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1036,f1033,f6137])).

fof(f6137,plain,
    ( spl5_515
  <=> ~ r2_hidden(sK1,k3_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_515])])).

fof(f1036,plain,
    ( ~ r2_hidden(sK1,k3_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f222,f1034,f122])).

fof(f5886,plain,
    ( ~ spl5_513
    | spl5_69 ),
    inference(avatar_split_clause,[],[f4111,f636,f5884])).

fof(f5884,plain,
    ( spl5_513
  <=> ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_513])])).

fof(f4111,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f550,f122])).

fof(f5879,plain,
    ( ~ spl5_511
    | spl5_69 ),
    inference(avatar_split_clause,[],[f4043,f636,f5877])).

fof(f5877,plain,
    ( spl5_511
  <=> ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_511])])).

fof(f4043,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f549,f122])).

fof(f5872,plain,
    ( ~ spl5_509
    | spl5_303 ),
    inference(avatar_split_clause,[],[f3474,f3459,f5870])).

fof(f5870,plain,
    ( spl5_509
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_509])])).

fof(f3459,plain,
    ( spl5_303
  <=> ~ m1_subset_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_303])])).

fof(f3474,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_303 ),
    inference(unit_resulting_resolution,[],[f106,f3460,f122])).

fof(f3460,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_303 ),
    inference(avatar_component_clause,[],[f3459])).

fof(f5859,plain,
    ( ~ spl5_507
    | spl5_259 ),
    inference(avatar_split_clause,[],[f2949,f2930,f5857])).

fof(f5857,plain,
    ( spl5_507
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k3_tarski(sK1),sK2(k1_zfmisc_1(k3_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_507])])).

fof(f2930,plain,
    ( spl5_259
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).

fof(f2949,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k3_tarski(sK1),sK2(k1_zfmisc_1(k3_tarski(sK1)))))
    | ~ spl5_259 ),
    inference(unit_resulting_resolution,[],[f222,f2931,f122])).

fof(f2931,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1))
    | ~ spl5_259 ),
    inference(avatar_component_clause,[],[f2930])).

fof(f5852,plain,
    ( ~ spl5_505
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1936,f636,f5850])).

fof(f5850,plain,
    ( spl5_505
  <=> ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_505])])).

fof(f1936,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f540,f122])).

fof(f5845,plain,
    ( ~ spl5_503
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1885,f636,f5843])).

fof(f5843,plain,
    ( spl5_503
  <=> ~ r2_hidden(k3_tarski(sK1),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_503])])).

fof(f1885,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f539,f122])).

fof(f5838,plain,
    ( ~ spl5_501
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1771,f636,f5836])).

fof(f5836,plain,
    ( spl5_501
  <=> ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_501])])).

fof(f1771,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f506,f122])).

fof(f5831,plain,
    ( ~ spl5_499
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1722,f636,f5829])).

fof(f5829,plain,
    ( spl5_499
  <=> ~ r2_hidden(k3_tarski(sK1),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_499])])).

fof(f1722,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f505,f122])).

fof(f5812,plain,
    ( ~ spl5_497
    | spl5_223 ),
    inference(avatar_split_clause,[],[f1642,f1635,f5810])).

fof(f5810,plain,
    ( spl5_497
  <=> ~ r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_497])])).

fof(f1635,plain,
    ( spl5_223
  <=> ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f1642,plain,
    ( ~ r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f106,f1636,f122])).

fof(f1636,plain,
    ( ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_223 ),
    inference(avatar_component_clause,[],[f1635])).

fof(f5805,plain,
    ( ~ spl5_495
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1186,f1177,f5803])).

fof(f5803,plain,
    ( spl5_495
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_495])])).

fof(f1177,plain,
    ( spl5_151
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f1186,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f472,f1178,f122])).

fof(f1178,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_151 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f5798,plain,
    ( ~ spl5_493
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1185,f1177,f5796])).

fof(f5796,plain,
    ( spl5_493
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_493])])).

fof(f1185,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f449,f1178,f122])).

fof(f5700,plain,(
    spl5_490 ),
    inference(avatar_split_clause,[],[f4104,f5698])).

fof(f5698,plain,
    ( spl5_490
  <=> k3_tarski(k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_490])])).

fof(f4104,plain,(
    k3_tarski(k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f550,f1025])).

fof(f1025,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
      | k3_tarski(X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f448,f873])).

fof(f448,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f115,f113])).

fof(f5693,plain,(
    spl5_488 ),
    inference(avatar_split_clause,[],[f4103,f5691])).

fof(f5691,plain,
    ( spl5_488
  <=> k1_setfam_1(k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_488])])).

fof(f4103,plain,(
    k1_setfam_1(k7_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f550,f1062])).

fof(f1062,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f471,f873])).

fof(f471,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f116,f114])).

fof(f5686,plain,(
    spl5_486 ),
    inference(avatar_split_clause,[],[f4036,f5684])).

fof(f5684,plain,
    ( spl5_486
  <=> k3_tarski(k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_486])])).

fof(f4036,plain,(
    k3_tarski(k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f549,f1025])).

fof(f5518,plain,(
    spl5_484 ),
    inference(avatar_split_clause,[],[f4035,f5516])).

fof(f5516,plain,
    ( spl5_484
  <=> k1_setfam_1(k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_484])])).

fof(f4035,plain,(
    k1_setfam_1(k7_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f549,f1062])).

fof(f5511,plain,(
    spl5_482 ),
    inference(avatar_split_clause,[],[f2142,f5509])).

fof(f5509,plain,
    ( spl5_482
  <=> k6_setfam_1(k1_xboole_0,k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_482])])).

fof(f2142,plain,(
    k6_setfam_1(k1_xboole_0,k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f222,f884])).

fof(f884,plain,(
    ! [X2] :
      ( k6_setfam_1(k1_xboole_0,X2) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f873,f116])).

fof(f5504,plain,(
    spl5_480 ),
    inference(avatar_split_clause,[],[f2089,f5502])).

fof(f5502,plain,
    ( spl5_480
  <=> k5_setfam_1(k1_xboole_0,k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_480])])).

fof(f2089,plain,(
    k5_setfam_1(k1_xboole_0,k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f222,f881])).

fof(f881,plain,(
    ! [X0] :
      ( k5_setfam_1(k1_xboole_0,X0) = k1_xboole_0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ) ),
    inference(resolution,[],[f873,f115])).

fof(f5497,plain,(
    spl5_478 ),
    inference(avatar_split_clause,[],[f1960,f5495])).

fof(f5495,plain,
    ( spl5_478
  <=> k3_tarski(k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_478])])).

fof(f1960,plain,(
    k3_tarski(k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f540,f1025])).

fof(f5490,plain,(
    spl5_476 ),
    inference(avatar_split_clause,[],[f1959,f5488])).

fof(f5488,plain,
    ( spl5_476
  <=> k1_setfam_1(k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_476])])).

fof(f1959,plain,(
    k1_setfam_1(k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f540,f1062])).

fof(f5323,plain,(
    spl5_474 ),
    inference(avatar_split_clause,[],[f1909,f5321])).

fof(f5321,plain,
    ( spl5_474
  <=> k3_tarski(k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_474])])).

fof(f1909,plain,(
    k3_tarski(k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f539,f1025])).

fof(f5316,plain,(
    spl5_472 ),
    inference(avatar_split_clause,[],[f1908,f5314])).

fof(f5314,plain,
    ( spl5_472
  <=> k1_setfam_1(k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_472])])).

fof(f1908,plain,(
    k1_setfam_1(k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f539,f1062])).

fof(f5309,plain,(
    spl5_470 ),
    inference(avatar_split_clause,[],[f1795,f5307])).

fof(f5307,plain,
    ( spl5_470
  <=> k3_tarski(k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_470])])).

fof(f1795,plain,(
    k3_tarski(k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f506,f1025])).

fof(f5302,plain,(
    spl5_468 ),
    inference(avatar_split_clause,[],[f1794,f5300])).

fof(f5300,plain,
    ( spl5_468
  <=> k1_setfam_1(k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_468])])).

fof(f1794,plain,(
    k1_setfam_1(k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f506,f1062])).

fof(f5295,plain,(
    spl5_466 ),
    inference(avatar_split_clause,[],[f1746,f5293])).

fof(f5293,plain,
    ( spl5_466
  <=> k3_tarski(k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_466])])).

fof(f1746,plain,(
    k3_tarski(k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f505,f1025])).

fof(f5287,plain,(
    spl5_464 ),
    inference(avatar_split_clause,[],[f1745,f5285])).

fof(f5285,plain,
    ( spl5_464
  <=> k1_setfam_1(k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_464])])).

fof(f1745,plain,(
    k1_setfam_1(k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f505,f1062])).

fof(f5186,plain,
    ( ~ spl5_463
    | spl5_345 ),
    inference(avatar_split_clause,[],[f3926,f3910,f5184])).

fof(f5184,plain,
    ( spl5_463
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_463])])).

fof(f3910,plain,
    ( spl5_345
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_345])])).

fof(f3926,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_345 ),
    inference(unit_resulting_resolution,[],[f472,f3911,f122])).

fof(f3911,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_345 ),
    inference(avatar_component_clause,[],[f3910])).

fof(f5179,plain,
    ( ~ spl5_461
    | spl5_345 ),
    inference(avatar_split_clause,[],[f3921,f3910,f5177])).

fof(f5177,plain,
    ( spl5_461
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_461])])).

fof(f3921,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_345 ),
    inference(unit_resulting_resolution,[],[f449,f3911,f122])).

fof(f5168,plain,
    ( ~ spl5_459
    | spl5_345 ),
    inference(avatar_split_clause,[],[f3916,f3910,f5166])).

fof(f5166,plain,
    ( spl5_459
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_459])])).

fof(f3916,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_345 ),
    inference(unit_resulting_resolution,[],[f552,f3911,f122])).

fof(f5161,plain,
    ( ~ spl5_457
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2881,f2871,f5159])).

fof(f5159,plain,
    ( spl5_457
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_457])])).

fof(f2871,plain,
    ( spl5_251
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_251])])).

fof(f2881,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f222,f2872,f122])).

fof(f2872,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_251 ),
    inference(avatar_component_clause,[],[f2871])).

fof(f5134,plain,
    ( spl5_454
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f980,f909,f5132])).

fof(f5132,plain,
    ( spl5_454
  <=> k6_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_454])])).

fof(f980,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f114])).

fof(f5121,plain,
    ( spl5_452
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f979,f909,f5119])).

fof(f5119,plain,
    ( spl5_452
  <=> k5_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_452])])).

fof(f979,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f113])).

fof(f5096,plain,
    ( ~ spl5_451
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_106
    | spl5_289
    | spl5_445 ),
    inference(avatar_split_clause,[],[f5070,f5055,f3348,f902,f137,f130,f5094])).

fof(f902,plain,
    ( spl5_106
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f3348,plain,
    ( spl5_289
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_289])])).

fof(f5070,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_106
    | ~ spl5_289
    | ~ spl5_445 ),
    inference(unit_resulting_resolution,[],[f3349,f903,f5056,f947])).

fof(f903,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f902])).

fof(f3349,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_289 ),
    inference(avatar_component_clause,[],[f3348])).

fof(f5085,plain,
    ( ~ spl5_449
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_106
    | spl5_445 ),
    inference(avatar_split_clause,[],[f5073,f5055,f902,f137,f130,f5083])).

fof(f5073,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_106
    | ~ spl5_445 ),
    inference(unit_resulting_resolution,[],[f131,f138,f903,f5056,f104])).

fof(f5078,plain,
    ( spl5_336
    | spl5_348
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f840,f818,f3955,f3789])).

fof(f840,plain,
    ( r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl5_100 ),
    inference(resolution,[],[f819,f219])).

fof(f5066,plain,
    ( spl5_444
    | ~ spl5_447
    | ~ spl5_2
    | ~ spl5_106
    | ~ spl5_286 ),
    inference(avatar_split_clause,[],[f3497,f3341,f902,f137,f5064,f5058])).

fof(f5058,plain,
    ( spl5_444
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_444])])).

fof(f5064,plain,
    ( spl5_447
  <=> ~ v3_pre_topc(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_447])])).

fof(f3341,plain,
    ( spl5_286
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_286])])).

fof(f3497,plain,
    ( ~ v3_pre_topc(k1_setfam_1(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_106
    | ~ spl5_286 ),
    inference(subsumption_resolution,[],[f3496,f138])).

fof(f3496,plain,
    ( ~ v3_pre_topc(k1_setfam_1(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_106
    | ~ spl5_286 ),
    inference(subsumption_resolution,[],[f3494,f903])).

fof(f3494,plain,
    ( ~ v3_pre_topc(k1_setfam_1(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_286 ),
    inference(superposition,[],[f100,f3342])).

fof(f3342,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k1_setfam_1(sK1)
    | ~ spl5_286 ),
    inference(avatar_component_clause,[],[f3341])).

fof(f5038,plain,
    ( ~ spl5_443
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_104
    | spl5_285
    | spl5_437 ),
    inference(avatar_split_clause,[],[f5010,f4996,f3334,f895,f137,f130,f5036])).

fof(f895,plain,
    ( spl5_104
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f3334,plain,
    ( spl5_285
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_285])])).

fof(f4996,plain,
    ( spl5_437
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_437])])).

fof(f5010,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_285
    | ~ spl5_437 ),
    inference(unit_resulting_resolution,[],[f3335,f896,f4997,f947])).

fof(f4997,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ spl5_437 ),
    inference(avatar_component_clause,[],[f4996])).

fof(f896,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f895])).

fof(f3335,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_285 ),
    inference(avatar_component_clause,[],[f3334])).

fof(f5023,plain,
    ( ~ spl5_441
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_104
    | spl5_437 ),
    inference(avatar_split_clause,[],[f5013,f4996,f895,f137,f130,f5021])).

fof(f5021,plain,
    ( spl5_441
  <=> ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_441])])).

fof(f5013,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_437 ),
    inference(unit_resulting_resolution,[],[f131,f138,f896,f4997,f104])).

fof(f5007,plain,
    ( spl5_436
    | ~ spl5_439
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_234 ),
    inference(avatar_split_clause,[],[f3432,f2181,f895,f137,f5005,f4999])).

fof(f4999,plain,
    ( spl5_436
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_436])])).

fof(f5005,plain,
    ( spl5_439
  <=> ~ v3_pre_topc(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_439])])).

fof(f2181,plain,
    ( spl5_234
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_234])])).

fof(f3432,plain,
    ( ~ v3_pre_topc(k3_tarski(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_104
    | ~ spl5_234 ),
    inference(subsumption_resolution,[],[f3431,f138])).

fof(f3431,plain,
    ( ~ v3_pre_topc(k3_tarski(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_104
    | ~ spl5_234 ),
    inference(subsumption_resolution,[],[f3429,f896])).

fof(f3429,plain,
    ( ~ v3_pre_topc(k3_tarski(sK1),sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_234 ),
    inference(superposition,[],[f100,f2182])).

fof(f2182,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k3_tarski(sK1)
    | ~ spl5_234 ),
    inference(avatar_component_clause,[],[f2181])).

fof(f4902,plain,
    ( spl5_434
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2726,f2209,f4900])).

fof(f4900,plain,
    ( spl5_434
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_434])])).

fof(f2209,plain,
    ( spl5_243
  <=> k1_zfmisc_1(u1_struct_0(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_243])])).

fof(f2726,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f222,f2210,f219])).

fof(f2210,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_xboole_0
    | ~ spl5_243 ),
    inference(avatar_component_clause,[],[f2209])).

fof(f4895,plain,
    ( ~ spl5_433
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2707,f958,f4893])).

fof(f4893,plain,
    ( spl5_433
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_433])])).

fof(f2707,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f540,f959,f122])).

fof(f4888,plain,
    ( ~ spl5_431
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2706,f958,f4886])).

fof(f4886,plain,
    ( spl5_431
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_431])])).

fof(f2706,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f506,f959,f122])).

fof(f4881,plain,
    ( ~ spl5_429
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2703,f958,f4879])).

fof(f4879,plain,
    ( spl5_429
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_429])])).

fof(f2703,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f539,f959,f122])).

fof(f4874,plain,
    ( ~ spl5_427
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2702,f958,f4872])).

fof(f4872,plain,
    ( spl5_427
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_427])])).

fof(f2702,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f505,f959,f122])).

fof(f4773,plain,
    ( ~ spl5_425
    | spl5_121 ),
    inference(avatar_split_clause,[],[f2697,f958,f4771])).

fof(f4771,plain,
    ( spl5_425
  <=> ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_425])])).

fof(f2697,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f222,f959,f122])).

fof(f4766,plain,
    ( spl5_422
    | ~ spl5_54
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f1133,f902,f479,f4764])).

fof(f4764,plain,
    ( spl5_422
  <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_422])])).

fof(f1133,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k1_setfam_1(sK1)
    | ~ spl5_54
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1128,f483])).

fof(f483,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k1_setfam_1(sK1)
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f480,f111])).

fof(f1128,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_106 ),
    inference(unit_resulting_resolution,[],[f903,f112])).

fof(f4759,plain,
    ( spl5_420
    | ~ spl5_52
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f1120,f895,f456,f4757])).

fof(f4757,plain,
    ( spl5_420
  <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_420])])).

fof(f1120,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k3_tarski(sK1)
    | ~ spl5_52
    | ~ spl5_104 ),
    inference(forward_demodulation,[],[f1115,f460])).

fof(f460,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k3_tarski(sK1)
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f457,f111])).

fof(f1115,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_104 ),
    inference(unit_resulting_resolution,[],[f896,f112])).

fof(f4752,plain,
    ( ~ spl5_419
    | spl5_413 ),
    inference(avatar_split_clause,[],[f4621,f4581,f4750])).

fof(f4750,plain,
    ( spl5_419
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_419])])).

fof(f4581,plain,
    ( spl5_413
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_413])])).

fof(f4621,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_413 ),
    inference(unit_resulting_resolution,[],[f4582,f108])).

fof(f4582,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_413 ),
    inference(avatar_component_clause,[],[f4581])).

fof(f4628,plain,
    ( ~ spl5_417
    | spl5_45 ),
    inference(avatar_split_clause,[],[f417,f411,f4626])).

fof(f4626,plain,
    ( spl5_417
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_417])])).

fof(f417,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f222,f412,f122])).

fof(f4590,plain,
    ( ~ spl5_415
    | spl5_405 ),
    inference(avatar_split_clause,[],[f4517,f4489,f4588])).

fof(f4588,plain,
    ( spl5_415
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_415])])).

fof(f4489,plain,
    ( spl5_405
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_405])])).

fof(f4517,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_405 ),
    inference(unit_resulting_resolution,[],[f4490,f108])).

fof(f4490,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_405 ),
    inference(avatar_component_clause,[],[f4489])).

fof(f4583,plain,
    ( ~ spl5_413
    | ~ spl5_14
    | spl5_199 ),
    inference(avatar_split_clause,[],[f1496,f1477,f179,f4581])).

fof(f1496,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_14
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f1478,f1027])).

fof(f1027,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl5_14 ),
    inference(superposition,[],[f448,f180])).

fof(f4576,plain,
    ( ~ spl5_411
    | spl5_159 ),
    inference(avatar_split_clause,[],[f1238,f1224,f4574])).

fof(f4574,plain,
    ( spl5_411
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_411])])).

fof(f1224,plain,
    ( spl5_159
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1238,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_159 ),
    inference(unit_resulting_resolution,[],[f106,f1225,f122])).

fof(f1225,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_159 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f4569,plain,
    ( ~ spl5_409
    | spl5_83 ),
    inference(avatar_split_clause,[],[f715,f709,f4567])).

fof(f4567,plain,
    ( spl5_409
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_409])])).

fof(f715,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f222,f710,f122])).

fof(f4498,plain,
    ( ~ spl5_407
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1218,f1208,f4496])).

fof(f4496,plain,
    ( spl5_407
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_407])])).

fof(f1208,plain,
    ( spl5_157
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f1218,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f106,f1209,f122])).

fof(f1209,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f4491,plain,
    ( ~ spl5_405
    | ~ spl5_38
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1213,f1208,f355,f4489])).

fof(f1213,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_38
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f356,f1209,f122])).

fof(f4441,plain,
    ( ~ spl5_403
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1096,f1033,f4439])).

fof(f4439,plain,
    ( spl5_403
  <=> ~ r2_hidden(sK1,k7_setfam_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_403])])).

fof(f1096,plain,
    ( ~ r2_hidden(sK1,k7_setfam_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f552,f122])).

fof(f4434,plain,
    ( ~ spl5_401
    | spl5_121
    | ~ spl5_382 ),
    inference(avatar_split_clause,[],[f4418,f4314,f958,f4432])).

fof(f4432,plain,
    ( spl5_401
  <=> ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_401])])).

fof(f4314,plain,
    ( spl5_382
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_382])])).

fof(f4418,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))
    | ~ spl5_121
    | ~ spl5_382 ),
    inference(unit_resulting_resolution,[],[f959,f4315,f122])).

fof(f4315,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_382 ),
    inference(avatar_component_clause,[],[f4314])).

fof(f4405,plain,
    ( ~ spl5_399
    | spl5_121
    | ~ spl5_374 ),
    inference(avatar_split_clause,[],[f4388,f4240,f958,f4403])).

fof(f4403,plain,
    ( spl5_399
  <=> ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_399])])).

fof(f4240,plain,
    ( spl5_374
  <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_374])])).

fof(f4388,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_121
    | ~ spl5_374 ),
    inference(unit_resulting_resolution,[],[f959,f4241,f122])).

fof(f4241,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_374 ),
    inference(avatar_component_clause,[],[f4240])).

fof(f4377,plain,
    ( ~ spl5_397
    | ~ spl5_314 ),
    inference(avatar_split_clause,[],[f3600,f3560,f4375])).

fof(f4375,plain,
    ( spl5_397
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_397])])).

fof(f3560,plain,
    ( spl5_314
  <=> r2_hidden(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_314])])).

fof(f3600,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))
    | ~ spl5_314 ),
    inference(unit_resulting_resolution,[],[f3561,f107])).

fof(f3561,plain,
    ( r2_hidden(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_314 ),
    inference(avatar_component_clause,[],[f3560])).

fof(f4370,plain,
    ( ~ spl5_395
    | ~ spl5_312 ),
    inference(avatar_split_clause,[],[f3589,f3551,f4368])).

fof(f4368,plain,
    ( spl5_395
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_395])])).

fof(f3551,plain,
    ( spl5_312
  <=> r2_hidden(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_312])])).

fof(f3589,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))
    | ~ spl5_312 ),
    inference(unit_resulting_resolution,[],[f3552,f107])).

fof(f3552,plain,
    ( r2_hidden(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_312 ),
    inference(avatar_component_clause,[],[f3551])).

fof(f4360,plain,
    ( ~ spl5_393
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4308,f4286,f4358])).

fof(f4358,plain,
    ( spl5_393
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_393])])).

fof(f4308,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f106,f4287,f122])).

fof(f4353,plain,
    ( ~ spl5_391
    | ~ spl5_108
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4292,f4286,f909,f4351])).

fof(f4351,plain,
    ( spl5_391
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_391])])).

fof(f4292,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_108
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f910,f4287,f122])).

fof(f4342,plain,
    ( ~ spl5_389
    | ~ spl5_100
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4296,f4286,f818,f4340])).

fof(f4296,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f819,f4287,f122])).

fof(f4330,plain,
    ( ~ spl5_387
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4309,f4286,f4328])).

fof(f4328,plain,
    ( spl5_387
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_387])])).

fof(f4309,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f4287,f108])).

fof(f4323,plain,
    ( ~ spl5_385
    | ~ spl5_20
    | spl5_381 ),
    inference(avatar_split_clause,[],[f4307,f4286,f205,f4321])).

fof(f4321,plain,
    ( spl5_385
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_385])])).

fof(f4307,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_20
    | ~ spl5_381 ),
    inference(unit_resulting_resolution,[],[f206,f4287,f122])).

fof(f4316,plain,
    ( spl5_382
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f984,f909,f4314])).

fof(f984,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f118])).

fof(f4288,plain,
    ( ~ spl5_381
    | spl5_249 ),
    inference(avatar_split_clause,[],[f4281,f2748,f4286])).

fof(f4281,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_249 ),
    inference(duplicate_literal_removal,[],[f4280])).

fof(f4280,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_249 ),
    inference(resolution,[],[f3522,f2763])).

fof(f4256,plain,
    ( ~ spl5_379
    | spl5_259 ),
    inference(avatar_split_clause,[],[f2959,f2930,f4254])).

fof(f4254,plain,
    ( spl5_379
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_379])])).

fof(f2959,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1))))))
    | ~ spl5_259 ),
    inference(unit_resulting_resolution,[],[f472,f2931,f122])).

fof(f4249,plain,
    ( ~ spl5_377
    | spl5_259 ),
    inference(avatar_split_clause,[],[f2955,f2930,f4247])).

fof(f4247,plain,
    ( spl5_377
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_377])])).

fof(f2955,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1))))))
    | ~ spl5_259 ),
    inference(unit_resulting_resolution,[],[f449,f2931,f122])).

fof(f4242,plain,
    ( spl5_374
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f839,f818,f4240])).

fof(f839,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f110])).

fof(f4233,plain,
    ( ~ spl5_373
    | spl5_169 ),
    inference(avatar_split_clause,[],[f1343,f1330,f4231])).

fof(f4231,plain,
    ( spl5_373
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_373])])).

fof(f1330,plain,
    ( spl5_169
  <=> ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1343,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_169 ),
    inference(unit_resulting_resolution,[],[f106,f1331,f122])).

fof(f1331,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f4226,plain,
    ( ~ spl5_371
    | spl5_69 ),
    inference(avatar_split_clause,[],[f639,f636,f4224])).

fof(f4224,plain,
    ( spl5_371
  <=> ~ r2_hidden(k3_tarski(sK1),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_371])])).

fof(f639,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f222,f637,f122])).

fof(f4215,plain,
    ( spl5_368
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f832,f818,f4213])).

fof(f4213,plain,
    ( spl5_368
  <=> k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_368])])).

fof(f832,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f114])).

fof(f4167,plain,
    ( spl5_366
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f831,f818,f4165])).

fof(f4165,plain,
    ( spl5_366
  <=> k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_366])])).

fof(f4160,plain,
    ( ~ spl5_365
    | ~ spl5_358 ),
    inference(avatar_split_clause,[],[f4086,f4071,f4158])).

fof(f4158,plain,
    ( spl5_365
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_365])])).

fof(f4086,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_358 ),
    inference(unit_resulting_resolution,[],[f4072,f107])).

fof(f4072,plain,
    ( r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_358 ),
    inference(avatar_component_clause,[],[f4071])).

fof(f4153,plain,
    ( ~ spl5_363
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3842,f3786,f4151])).

fof(f4151,plain,
    ( spl5_363
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_363])])).

fof(f3786,plain,
    ( spl5_337
  <=> k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_337])])).

fof(f3842,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f3787,f340])).

fof(f3787,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_xboole_0
    | ~ spl5_337 ),
    inference(avatar_component_clause,[],[f3786])).

fof(f4080,plain,
    ( spl5_360
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3840,f3786,f4078])).

fof(f4078,plain,
    ( spl5_360
  <=> r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_360])])).

fof(f3840,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f3787,f325])).

fof(f4073,plain,
    ( spl5_358
    | ~ spl5_108
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3823,f3786,f909,f4071])).

fof(f3823,plain,
    ( r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_108
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f910,f3787,f219])).

fof(f4024,plain,
    ( ~ spl5_357
    | spl5_355 ),
    inference(avatar_split_clause,[],[f4017,f3999,f4022])).

fof(f4022,plain,
    ( spl5_357
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_357])])).

fof(f4017,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_355 ),
    inference(unit_resulting_resolution,[],[f4000,f108])).

fof(f4001,plain,
    ( ~ spl5_355
    | spl5_131
    | ~ spl5_338 ),
    inference(avatar_split_clause,[],[f3874,f3795,f1033,f3999])).

fof(f3874,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_131
    | ~ spl5_338 ),
    inference(unit_resulting_resolution,[],[f1034,f3796,f122])).

fof(f3983,plain,
    ( ~ spl5_353
    | ~ spl5_348 ),
    inference(avatar_split_clause,[],[f3963,f3955,f3981])).

fof(f3963,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_348 ),
    inference(unit_resulting_resolution,[],[f3956,f107])).

fof(f3976,plain,
    ( ~ spl5_351
    | spl5_345 ),
    inference(avatar_split_clause,[],[f3927,f3910,f3974])).

fof(f3974,plain,
    ( spl5_351
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_351])])).

fof(f3927,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_345 ),
    inference(unit_resulting_resolution,[],[f106,f3911,f122])).

fof(f3957,plain,
    ( spl5_348
    | ~ spl5_100
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3825,f3786,f818,f3955])).

fof(f3825,plain,
    ( r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_100
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f819,f3787,f219])).

fof(f3935,plain,
    ( ~ spl5_347
    | spl5_345 ),
    inference(avatar_split_clause,[],[f3928,f3910,f3933])).

fof(f3933,plain,
    ( spl5_347
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_347])])).

fof(f3928,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_345 ),
    inference(unit_resulting_resolution,[],[f3911,f108])).

fof(f3912,plain,
    ( ~ spl5_345
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3843,f3786,f3910])).

fof(f3843,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f3787,f873])).

fof(f3891,plain,
    ( ~ spl5_343
    | ~ spl5_338 ),
    inference(avatar_split_clause,[],[f3878,f3795,f3889])).

fof(f3889,plain,
    ( spl5_343
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_343])])).

fof(f3878,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl5_338 ),
    inference(unit_resulting_resolution,[],[f3796,f107])).

fof(f3852,plain,
    ( ~ spl5_341
    | ~ spl5_6
    | spl5_337 ),
    inference(avatar_split_clause,[],[f3845,f3786,f151,f3850])).

fof(f3850,plain,
    ( spl5_341
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_341])])).

fof(f3845,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_6
    | ~ spl5_337 ),
    inference(unit_resulting_resolution,[],[f152,f3787,f120])).

fof(f3797,plain,
    ( spl5_336
    | spl5_338
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f324,f205,f3795,f3789])).

fof(f324,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl5_20 ),
    inference(resolution,[],[f219,f206])).

fof(f3780,plain,(
    spl5_334 ),
    inference(avatar_split_clause,[],[f2153,f3778])).

fof(f3778,plain,
    ( spl5_334
  <=> k6_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_334])])).

fof(f2153,plain,(
    k6_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f472,f884])).

fof(f3773,plain,(
    spl5_332 ),
    inference(avatar_split_clause,[],[f2149,f3771])).

fof(f3771,plain,
    ( spl5_332
  <=> k6_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_332])])).

fof(f2149,plain,(
    k6_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f449,f884])).

fof(f3766,plain,(
    spl5_330 ),
    inference(avatar_split_clause,[],[f2145,f3764])).

fof(f3764,plain,
    ( spl5_330
  <=> k6_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_330])])).

fof(f2145,plain,(
    k6_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f552,f884])).

fof(f3700,plain,(
    spl5_328 ),
    inference(avatar_split_clause,[],[f2100,f3698])).

fof(f3698,plain,
    ( spl5_328
  <=> k5_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_328])])).

fof(f2100,plain,(
    k5_setfam_1(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f472,f881])).

fof(f3693,plain,(
    spl5_326 ),
    inference(avatar_split_clause,[],[f2096,f3691])).

fof(f3691,plain,
    ( spl5_326
  <=> k5_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_326])])).

fof(f2096,plain,(
    k5_setfam_1(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f449,f881])).

fof(f3686,plain,(
    spl5_324 ),
    inference(avatar_split_clause,[],[f2092,f3684])).

fof(f3684,plain,
    ( spl5_324
  <=> k5_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_324])])).

fof(f2092,plain,(
    k5_setfam_1(k1_xboole_0,k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f552,f881])).

fof(f3679,plain,(
    spl5_322 ),
    inference(avatar_split_clause,[],[f1313,f3677])).

fof(f3677,plain,
    ( spl5_322
  <=> k1_setfam_1(k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_322])])).

fof(f1313,plain,(
    k1_setfam_1(k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f222,f1062])).

fof(f3672,plain,(
    spl5_320 ),
    inference(avatar_split_clause,[],[f1297,f3670])).

fof(f3670,plain,
    ( spl5_320
  <=> k3_tarski(k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_320])])).

fof(f1297,plain,(
    k3_tarski(k3_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f222,f1025])).

fof(f3576,plain,
    ( ~ spl5_319
    | ~ spl5_300 ),
    inference(avatar_split_clause,[],[f3446,f3425,f3574])).

fof(f3574,plain,
    ( spl5_319
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_319])])).

fof(f3425,plain,
    ( spl5_300
  <=> r2_hidden(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_300])])).

fof(f3446,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_300 ),
    inference(unit_resulting_resolution,[],[f3426,f107])).

fof(f3426,plain,
    ( r2_hidden(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_300 ),
    inference(avatar_component_clause,[],[f3425])).

fof(f3569,plain,
    ( ~ spl5_317
    | ~ spl5_298 ),
    inference(avatar_split_clause,[],[f3436,f3418,f3567])).

fof(f3567,plain,
    ( spl5_317
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_317])])).

fof(f3418,plain,
    ( spl5_298
  <=> r2_hidden(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_298])])).

fof(f3436,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_298 ),
    inference(unit_resulting_resolution,[],[f3419,f107])).

fof(f3419,plain,
    ( r2_hidden(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_298 ),
    inference(avatar_component_clause,[],[f3418])).

fof(f3562,plain,
    ( spl5_314
    | ~ spl5_220
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3278,f2748,f1622,f3560])).

fof(f1622,plain,
    ( spl5_220
  <=> m1_subset_1(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).

fof(f3278,plain,
    ( r2_hidden(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_220
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f1623,f109])).

fof(f1623,plain,
    ( m1_subset_1(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_220 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f3553,plain,
    ( spl5_312
    | ~ spl5_218
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3228,f2748,f1615,f3551])).

fof(f1615,plain,
    ( spl5_218
  <=> m1_subset_1(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).

fof(f3228,plain,
    ( r2_hidden(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_218
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f1616,f109])).

fof(f1616,plain,
    ( m1_subset_1(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_218 ),
    inference(avatar_component_clause,[],[f1615])).

fof(f3546,plain,
    ( ~ spl5_311
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2892,f2871,f3544])).

fof(f3544,plain,
    ( spl5_311
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_311])])).

fof(f2892,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f472,f2872,f122])).

fof(f3539,plain,
    ( ~ spl5_309
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2888,f2871,f3537])).

fof(f3537,plain,
    ( spl5_309
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_309])])).

fof(f2888,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f449,f2872,f122])).

fof(f3532,plain,
    ( ~ spl5_307
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2884,f2871,f3530])).

fof(f3530,plain,
    ( spl5_307
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_307])])).

fof(f2884,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f552,f2872,f122])).

fof(f3482,plain,
    ( ~ spl5_305
    | spl5_303 ),
    inference(avatar_split_clause,[],[f3475,f3459,f3480])).

fof(f3480,plain,
    ( spl5_305
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_305])])).

fof(f3475,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_303 ),
    inference(unit_resulting_resolution,[],[f3460,f108])).

fof(f3461,plain,
    ( ~ spl5_303
    | spl5_125
    | ~ spl5_300 ),
    inference(avatar_split_clause,[],[f3454,f3425,f998,f3459])).

fof(f3454,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_125
    | ~ spl5_300 ),
    inference(subsumption_resolution,[],[f3453,f999])).

fof(f3453,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_300 ),
    inference(superposition,[],[f3426,f1062])).

fof(f3427,plain,
    ( spl5_300
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2736,f2209,f3425])).

fof(f2736,plain,
    ( r2_hidden(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f472,f2210,f219])).

fof(f3420,plain,
    ( spl5_298
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2732,f2209,f3418])).

fof(f2732,plain,
    ( r2_hidden(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f449,f2210,f219])).

fof(f3413,plain,
    ( ~ spl5_297
    | spl5_263 ),
    inference(avatar_split_clause,[],[f3069,f3054,f3411])).

fof(f3411,plain,
    ( spl5_297
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_297])])).

fof(f3069,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f106,f3055,f122])).

fof(f3389,plain,
    ( spl5_294
    | ~ spl5_20
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f991,f909,f205,f3387])).

fof(f3387,plain,
    ( spl5_294
  <=> k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_294])])).

fof(f991,plain,
    ( k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1
    | ~ spl5_20
    | ~ spl5_108 ),
    inference(forward_demodulation,[],[f985,f282])).

fof(f282,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f111])).

fof(f985,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f112])).

fof(f3366,plain,
    ( spl5_242
    | spl5_254
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f485,f479,f2905,f2212])).

fof(f2212,plain,
    ( spl5_242
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).

fof(f2905,plain,
    ( spl5_254
  <=> r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).

fof(f485,plain,
    ( r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_54 ),
    inference(resolution,[],[f480,f219])).

fof(f3364,plain,
    ( ~ spl5_293
    | ~ spl5_280 ),
    inference(avatar_split_clause,[],[f3315,f3270,f3362])).

fof(f3362,plain,
    ( spl5_293
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_293])])).

fof(f3270,plain,
    ( spl5_280
  <=> r2_hidden(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_280])])).

fof(f3315,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_280 ),
    inference(unit_resulting_resolution,[],[f3271,f107])).

fof(f3271,plain,
    ( r2_hidden(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_280 ),
    inference(avatar_component_clause,[],[f3270])).

fof(f3357,plain,
    ( ~ spl5_291
    | ~ spl5_278 ),
    inference(avatar_split_clause,[],[f3304,f3263,f3355])).

fof(f3355,plain,
    ( spl5_291
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_291])])).

fof(f3263,plain,
    ( spl5_278
  <=> r2_hidden(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_278])])).

fof(f3304,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_278 ),
    inference(unit_resulting_resolution,[],[f3264,f107])).

fof(f3264,plain,
    ( r2_hidden(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_278 ),
    inference(avatar_component_clause,[],[f3263])).

fof(f3350,plain,
    ( ~ spl5_289
    | ~ spl5_276 ),
    inference(avatar_split_clause,[],[f3293,f3256,f3348])).

fof(f3256,plain,
    ( spl5_276
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_276])])).

fof(f3293,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)))
    | ~ spl5_276 ),
    inference(unit_resulting_resolution,[],[f3257,f107])).

fof(f3257,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_276 ),
    inference(avatar_component_clause,[],[f3256])).

fof(f3343,plain,
    ( spl5_286
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f483,f479,f3341])).

fof(f3336,plain,
    ( ~ spl5_285
    | ~ spl5_274 ),
    inference(avatar_split_clause,[],[f3283,f3249,f3334])).

fof(f3249,plain,
    ( spl5_274
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_274])])).

fof(f3283,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)))
    | ~ spl5_274 ),
    inference(unit_resulting_resolution,[],[f3250,f107])).

fof(f3250,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_274 ),
    inference(avatar_component_clause,[],[f3249])).

fof(f3328,plain,
    ( spl5_282
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f482,f479,f3326])).

fof(f482,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_setfam_1(sK1))
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f480,f112])).

fof(f3272,plain,
    ( spl5_280
    | ~ spl5_116
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3220,f2748,f942,f3270])).

fof(f3220,plain,
    ( r2_hidden(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_116
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f943,f109])).

fof(f3265,plain,
    ( spl5_278
    | ~ spl5_114
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3212,f2748,f935,f3263])).

fof(f935,plain,
    ( spl5_114
  <=> m1_subset_1(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f3212,plain,
    ( r2_hidden(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_114
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f936,f109])).

fof(f936,plain,
    ( m1_subset_1(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f935])).

fof(f3258,plain,
    ( spl5_276
    | ~ spl5_106
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3201,f2748,f902,f3256])).

fof(f3201,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_106
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f903,f109])).

fof(f3251,plain,
    ( spl5_274
    | ~ spl5_104
    | spl5_249 ),
    inference(avatar_split_clause,[],[f3171,f2748,f895,f3249])).

fof(f3171,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_104
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f896,f109])).

fof(f3181,plain,
    ( ~ spl5_273
    | spl5_259 ),
    inference(avatar_split_clause,[],[f2960,f2930,f3179])).

fof(f3179,plain,
    ( spl5_273
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_273])])).

fof(f2960,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k3_tarski(sK1))))
    | ~ spl5_259 ),
    inference(unit_resulting_resolution,[],[f106,f2931,f122])).

fof(f3148,plain,
    ( ~ spl5_271
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2893,f2871,f3146])).

fof(f3146,plain,
    ( spl5_271
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_271])])).

fof(f2893,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f106,f2872,f122])).

fof(f3141,plain,
    ( ~ spl5_269
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2740,f2209,f3139])).

fof(f3139,plain,
    ( spl5_269
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_269])])).

fof(f2740,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f2210,f340])).

fof(f3102,plain,
    ( spl5_266
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2738,f2209,f3100])).

fof(f3100,plain,
    ( spl5_266
  <=> r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_266])])).

fof(f2738,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f2210,f325])).

fof(f3092,plain,
    ( ~ spl5_265
    | spl5_263 ),
    inference(avatar_split_clause,[],[f3070,f3054,f3090])).

fof(f3090,plain,
    ( spl5_265
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_265])])).

fof(f3070,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f3055,f108])).

fof(f3056,plain,
    ( ~ spl5_263
    | spl5_69
    | ~ spl5_244 ),
    inference(avatar_split_clause,[],[f2824,f2218,f636,f3054])).

fof(f2824,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_69
    | ~ spl5_244 ),
    inference(unit_resulting_resolution,[],[f637,f2219,f122])).

fof(f3000,plain,
    ( ~ spl5_261
    | ~ spl5_254 ),
    inference(avatar_split_clause,[],[f2936,f2905,f2998])).

fof(f2936,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_setfam_1(sK1))
    | ~ spl5_254 ),
    inference(unit_resulting_resolution,[],[f2906,f107])).

fof(f2906,plain,
    ( r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_254 ),
    inference(avatar_component_clause,[],[f2905])).

fof(f2932,plain,
    ( ~ spl5_259
    | spl5_63
    | spl5_253 ),
    inference(avatar_split_clause,[],[f2895,f2878,f599,f2930])).

fof(f2878,plain,
    ( spl5_253
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_253])])).

fof(f2895,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1))
    | ~ spl5_63
    | ~ spl5_253 ),
    inference(unit_resulting_resolution,[],[f600,f2879,f109])).

fof(f2879,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1))
    | ~ spl5_253 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f2914,plain,
    ( ~ spl5_257
    | spl5_251 ),
    inference(avatar_split_clause,[],[f2894,f2871,f2912])).

fof(f2912,plain,
    ( spl5_257
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_257])])).

fof(f2894,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_251 ),
    inference(unit_resulting_resolution,[],[f2872,f108])).

fof(f2907,plain,
    ( spl5_254
    | ~ spl5_54
    | spl5_249 ),
    inference(avatar_split_clause,[],[f2816,f2748,f479,f2905])).

fof(f2816,plain,
    ( r2_hidden(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_54
    | ~ spl5_249 ),
    inference(unit_resulting_resolution,[],[f2749,f480,f109])).

fof(f2880,plain,
    ( ~ spl5_253
    | ~ spl5_244 ),
    inference(avatar_split_clause,[],[f2828,f2218,f2878])).

fof(f2828,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k3_tarski(sK1))
    | ~ spl5_244 ),
    inference(unit_resulting_resolution,[],[f2219,f107])).

fof(f2873,plain,
    ( ~ spl5_251
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2741,f2209,f2871])).

fof(f2741,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f2210,f873])).

fof(f2750,plain,
    ( ~ spl5_249
    | ~ spl5_6
    | spl5_243 ),
    inference(avatar_split_clause,[],[f2743,f2209,f151,f2748])).

fof(f2743,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_243 ),
    inference(unit_resulting_resolution,[],[f152,f2210,f120])).

fof(f2674,plain,
    ( spl5_246
    | ~ spl5_2
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2662,f955,f952,f137,f2672])).

fof(f2672,plain,
    ( spl5_246
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_246])])).

fof(f952,plain,
    ( spl5_118
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f955,plain,
    ( spl5_120
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2662,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(backward_demodulation,[],[f2659,f2650])).

fof(f2650,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl5_2
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f2649,f138])).

fof(f2649,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_118
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f2648,f956])).

fof(f956,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f955])).

fof(f2648,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_118 ),
    inference(resolution,[],[f953,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f953,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f952])).

fof(f2659,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f2654,f94])).

fof(f94,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t3_boole)).

fof(f2654,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k4_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_120 ),
    inference(unit_resulting_resolution,[],[f956,f112])).

fof(f2666,plain,
    ( ~ spl5_120
    | spl5_125
    | spl5_243 ),
    inference(avatar_contradiction_clause,[],[f2665])).

fof(f2665,plain,
    ( $false
    | ~ spl5_120
    | ~ spl5_125
    | ~ spl5_243 ),
    inference(subsumption_resolution,[],[f2664,f2210])).

fof(f2664,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_120
    | ~ spl5_125 ),
    inference(subsumption_resolution,[],[f2658,f999])).

fof(f2658,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_120 ),
    inference(resolution,[],[f956,f219])).

fof(f2645,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | spl5_43
    | ~ spl5_108
    | ~ spl5_118
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2644])).

fof(f2644,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_108
    | ~ spl5_118
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f953,f2509])).

fof(f2509,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2438,f180])).

fof(f2438,plain,
    ( ~ v4_pre_topc(k3_tarski(k1_xboole_0),sK0)
    | ~ spl5_20
    | ~ spl5_43
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f395])).

fof(f2435,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_20
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2244,f95])).

fof(f2244,plain,
    ( k4_xboole_0(k1_xboole_0,k3_subset_1(k1_xboole_0,sK1)) = sK1
    | ~ spl5_20
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f991])).

fof(f2213,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_242 ),
    inference(avatar_component_clause,[],[f2212])).

fof(f2622,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2621])).

fof(f2621,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2321,f2517])).

fof(f2517,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2516,f180])).

fof(f2516,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_tarski(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2515,f2435])).

fof(f2515,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_tarski(sK1))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2514,f200])).

fof(f2514,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k3_tarski(sK1)) )
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2444,f180])).

fof(f2444,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k3_tarski(sK1)) )
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f603])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_tarski(sK1))
        | r2_hidden(X0,k3_tarski(sK1)) )
    | ~ spl5_63 ),
    inference(resolution,[],[f600,f109])).

fof(f2321,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(k3_subset_1(k1_xboole_0,sK1))),k1_xboole_0)
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1653])).

fof(f1653,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_220 ),
    inference(unit_resulting_resolution,[],[f1623,f110])).

fof(f2598,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2597])).

fof(f2597,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2310,f2517])).

fof(f2310,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k3_subset_1(k1_xboole_0,sK1))),k1_xboole_0)
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1627])).

fof(f1627,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_218 ),
    inference(unit_resulting_resolution,[],[f1616,f110])).

fof(f2592,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2591])).

fof(f2591,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2307,f2517])).

fof(f2307,plain,
    ( m1_subset_1(k3_tarski(k3_subset_1(k1_xboole_0,sK1)),k1_xboole_0)
    | ~ spl5_220
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1623])).

fof(f2590,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2589])).

fof(f2589,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2306,f2517])).

fof(f2306,plain,
    ( m1_subset_1(k1_setfam_1(k3_subset_1(k1_xboole_0,sK1)),k1_xboole_0)
    | ~ spl5_218
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1616])).

fof(f2584,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_116
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2583])).

fof(f2583,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_116
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2259,f2517])).

fof(f2259,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))),k1_xboole_0)
    | ~ spl5_116
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1140])).

fof(f1140,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f943,f110])).

fof(f2582,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_114
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2581])).

fof(f2581,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_114
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2257,f2517])).

fof(f2257,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))),k1_xboole_0)
    | ~ spl5_114
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f1136])).

fof(f1136,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_114 ),
    inference(unit_resulting_resolution,[],[f936,f110])).

fof(f2566,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_106
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2565])).

fof(f2565,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_106
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2496,f2517])).

fof(f2496,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_106
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f2234])).

fof(f2234,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_xboole_0)
    | ~ spl5_106
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f903])).

fof(f2564,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_104
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2563])).

fof(f2563,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_104
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2495,f2517])).

fof(f2495,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_104
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f2233])).

fof(f2233,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_xboole_0)
    | ~ spl5_104
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f896])).

fof(f2562,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_52
    | spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2561])).

fof(f2561,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_52
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2493,f2517])).

fof(f2493,plain,
    ( m1_subset_1(k3_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_52
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f2223])).

fof(f2223,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_xboole_0)
    | ~ spl5_52
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f457])).

fof(f2541,plain,
    ( ~ spl5_20
    | ~ spl5_34
    | ~ spl5_88
    | ~ spl5_100
    | ~ spl5_108
    | spl5_113
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2540])).

fof(f2540,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_34
    | ~ spl5_88
    | ~ spl5_100
    | ~ spl5_108
    | ~ spl5_113
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2458,f2389])).

fof(f2389,plain,
    ( v1_tops_2(k1_xboole_0,sK0)
    | ~ spl5_34
    | ~ spl5_88
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2387,f756])).

fof(f756,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl5_88
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f2387,plain,
    ( k7_setfam_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_34
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2386,f308])).

fof(f308,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl5_34
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f2386,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k7_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2230,f2385])).

fof(f2385,plain,
    ( k3_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1)) = k1_xboole_0
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2229,f95])).

fof(f2229,plain,
    ( k3_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f837])).

fof(f2230,plain,
    ( k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))) = k7_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl5_100
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2213,f838])).

fof(f2458,plain,
    ( ~ v1_tops_2(k1_xboole_0,sK0)
    | ~ spl5_20
    | ~ spl5_108
    | ~ spl5_113
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f920])).

fof(f920,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl5_113
  <=> ~ v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f2531,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | ~ spl5_38
    | spl5_71
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2530])).

fof(f2530,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_38
    | ~ spl5_71
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2529,f356])).

fof(f2529,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_71
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2450,f180])).

fof(f2450,plain,
    ( ~ r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_71
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f649])).

fof(f2527,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | ~ spl5_28
    | spl5_69
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2526])).

fof(f2526,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_28
    | ~ spl5_69
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2525,f259])).

fof(f2525,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_69
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2448,f180])).

fof(f2448,plain,
    ( ~ m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_69
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f637])).

fof(f2520,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_64
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2519])).

fof(f2519,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_64
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2518,f200])).

fof(f2518,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_64
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2445,f180])).

fof(f2445,plain,
    ( r2_hidden(sK2(k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_64
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f609])).

fof(f2513,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2512])).

fof(f2512,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2511,f152])).

fof(f2511,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(forward_demodulation,[],[f2443,f180])).

fof(f2443,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_63
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f600])).

fof(f2508,plain,
    ( ~ spl5_12
    | ~ spl5_20
    | ~ spl5_34
    | ~ spl5_100
    | ~ spl5_108
    | spl5_111
    | ~ spl5_242 ),
    inference(avatar_contradiction_clause,[],[f2507])).

fof(f2507,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_34
    | ~ spl5_100
    | ~ spl5_108
    | ~ spl5_111
    | ~ spl5_242 ),
    inference(subsumption_resolution,[],[f2437,f2395])).

fof(f2395,plain,
    ( ~ v2_tops_2(k1_xboole_0,sK0)
    | ~ spl5_34
    | ~ spl5_100
    | ~ spl5_111
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2387,f917])).

fof(f917,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f916])).

fof(f916,plain,
    ( spl5_111
  <=> ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f2437,plain,
    ( v2_tops_2(k1_xboole_0,sK0)
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_108
    | ~ spl5_242 ),
    inference(backward_demodulation,[],[f2435,f173])).

fof(f173,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_12
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2220,plain,
    ( spl5_242
    | spl5_244
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f462,f456,f2218,f2212])).

fof(f462,plain,
    ( r2_hidden(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_52 ),
    inference(resolution,[],[f457,f219])).

fof(f2207,plain,
    ( spl5_240
    | ~ spl5_2
    | ~ spl5_102
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1441,f935,f851,f137,f2205])).

fof(f851,plain,
    ( spl5_102
  <=> v3_pre_topc(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1441,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ spl5_2
    | ~ spl5_102
    | ~ spl5_114 ),
    inference(unit_resulting_resolution,[],[f138,f852,f936,f714])).

fof(f714,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f713,f110])).

fof(f713,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f100,f111])).

fof(f852,plain,
    ( v3_pre_topc(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f851])).

fof(f2200,plain,
    ( ~ spl5_239
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1163,f1147,f2198])).

fof(f2198,plain,
    ( spl5_239
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).

fof(f1163,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f472,f1148,f122])).

fof(f2193,plain,
    ( ~ spl5_237
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1162,f1147,f2191])).

fof(f2191,plain,
    ( spl5_237
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f1162,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))))
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f449,f1148,f122])).

fof(f2183,plain,
    ( spl5_234
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f460,f456,f2181])).

fof(f2171,plain,(
    spl5_232 ),
    inference(avatar_split_clause,[],[f2154,f2169])).

fof(f2169,plain,
    ( spl5_232
  <=> k6_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f2154,plain,(
    k6_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f106,f884])).

fof(f2132,plain,(
    spl5_230 ),
    inference(avatar_split_clause,[],[f2101,f2130])).

fof(f2130,plain,
    ( spl5_230
  <=> k5_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_230])])).

fof(f2101,plain,(
    k5_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f106,f881])).

fof(f2125,plain,
    ( spl5_228
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f459,f456,f2123])).

fof(f2123,plain,
    ( spl5_228
  <=> k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).

fof(f459,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_tarski(sK1))
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f457,f112])).

fof(f2088,plain,
    ( ~ spl5_227
    | spl5_121 ),
    inference(avatar_split_clause,[],[f1095,f958,f2086])).

fof(f2086,plain,
    ( spl5_227
  <=> ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_227])])).

fof(f1095,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f959,f552,f122])).

fof(f1650,plain,
    ( ~ spl5_225
    | spl5_223 ),
    inference(avatar_split_clause,[],[f1643,f1635,f1648])).

fof(f1648,plain,
    ( spl5_225
  <=> ~ r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).

fof(f1643,plain,
    ( ~ r2_hidden(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f1636,f108])).

fof(f1637,plain,
    ( ~ spl5_223
    | spl5_121
    | ~ spl5_218 ),
    inference(avatar_split_clause,[],[f1630,f1615,f958,f1635])).

fof(f1630,plain,
    ( ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_121
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1629,f959])).

fof(f1629,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_218 ),
    inference(superposition,[],[f1616,f1062])).

fof(f1624,plain,
    ( spl5_220
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f993,f909,f1622])).

fof(f993,plain,
    ( m1_subset_1(k3_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_108 ),
    inference(backward_demodulation,[],[f979,f981])).

fof(f981,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f115])).

fof(f1617,plain,
    ( spl5_218
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f992,f909,f1615])).

fof(f992,plain,
    ( m1_subset_1(k1_setfam_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_108 ),
    inference(backward_demodulation,[],[f980,f982])).

fof(f982,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK0),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f910,f116])).

fof(f1609,plain,
    ( ~ spl5_217
    | spl5_45 ),
    inference(avatar_split_clause,[],[f1092,f411,f1607])).

fof(f1607,plain,
    ( spl5_217
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).

fof(f1092,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f552,f122])).

fof(f1578,plain,
    ( ~ spl5_215
    | spl5_45 ),
    inference(avatar_split_clause,[],[f528,f411,f1576])).

fof(f1576,plain,
    ( spl5_215
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f528,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f472,f122])).

fof(f1571,plain,
    ( ~ spl5_213
    | spl5_45 ),
    inference(avatar_split_clause,[],[f495,f411,f1569])).

fof(f1569,plain,
    ( spl5_213
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f495,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f449,f122])).

fof(f1549,plain,
    ( ~ spl5_211
    | spl5_199 ),
    inference(avatar_split_clause,[],[f1504,f1477,f1547])).

fof(f1547,plain,
    ( spl5_211
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f1504,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f1478,f108])).

fof(f1542,plain,
    ( ~ spl5_209
    | spl5_197 ),
    inference(avatar_split_clause,[],[f1486,f1470,f1540])).

fof(f1540,plain,
    ( spl5_209
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f1486,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_197 ),
    inference(unit_resulting_resolution,[],[f1471,f108])).

fof(f1532,plain,
    ( ~ spl5_207
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1106,f1072,f1530])).

fof(f1530,plain,
    ( spl5_207
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f1106,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f106,f1073,f122])).

fof(f1525,plain,
    ( ~ spl5_205
    | spl5_83 ),
    inference(avatar_split_clause,[],[f1094,f709,f1523])).

fof(f1523,plain,
    ( spl5_205
  <=> ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f1094,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f552,f122])).

fof(f1518,plain,
    ( ~ spl5_203
    | spl5_83 ),
    inference(avatar_split_clause,[],[f717,f709,f1516])).

fof(f1516,plain,
    ( spl5_203
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f717,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f472,f710,f122])).

fof(f1511,plain,
    ( ~ spl5_201
    | spl5_83 ),
    inference(avatar_split_clause,[],[f716,f709,f1509])).

fof(f1509,plain,
    ( spl5_201
  <=> ~ r2_hidden(u1_struct_0(sK0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f716,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f449,f710,f122])).

fof(f1479,plain,
    ( ~ spl5_199
    | ~ spl5_14
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1211,f1208,f179,f1477])).

fof(f1211,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_14
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f1209,f1027])).

fof(f1472,plain,
    ( ~ spl5_197
    | ~ spl5_38
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1182,f1177,f355,f1470])).

fof(f1182,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_38
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f356,f1178,f122])).

fof(f1457,plain,
    ( ~ spl5_195
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1038,f1033,f1455])).

fof(f1455,plain,
    ( spl5_195
  <=> ~ r2_hidden(sK1,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).

fof(f1038,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f472,f1034,f122])).

fof(f1450,plain,
    ( ~ spl5_193
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1037,f1033,f1448])).

fof(f1448,plain,
    ( spl5_193
  <=> ~ r2_hidden(sK1,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f1037,plain,
    ( ~ r2_hidden(sK1,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f449,f1034,f122])).

fof(f1440,plain,
    ( ~ spl5_191
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1187,f1177,f1438])).

fof(f1438,plain,
    ( spl5_191
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f1187,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f106,f1178,f122])).

fof(f1433,plain,
    ( ~ spl5_189
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1093,f636,f1431])).

fof(f1431,plain,
    ( spl5_189
  <=> ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).

fof(f1093,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f552,f122])).

fof(f1426,plain,
    ( ~ spl5_187
    | spl5_69 ),
    inference(avatar_split_clause,[],[f641,f636,f1424])).

fof(f1424,plain,
    ( spl5_187
  <=> ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f641,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f472,f637,f122])).

fof(f1419,plain,
    ( ~ spl5_185
    | spl5_69 ),
    inference(avatar_split_clause,[],[f640,f636,f1417])).

fof(f1417,plain,
    ( spl5_185
  <=> ~ r2_hidden(k3_tarski(sK1),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f640,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f449,f637,f122])).

fof(f1394,plain,(
    spl5_182 ),
    inference(avatar_split_clause,[],[f1316,f1392])).

fof(f1392,plain,
    ( spl5_182
  <=> k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f1316,plain,(
    k1_setfam_1(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f472,f1062])).

fof(f1387,plain,(
    spl5_180 ),
    inference(avatar_split_clause,[],[f1315,f1385])).

fof(f1385,plain,
    ( spl5_180
  <=> k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f1315,plain,(
    k1_setfam_1(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f449,f1062])).

fof(f1380,plain,(
    spl5_178 ),
    inference(avatar_split_clause,[],[f1314,f1378])).

fof(f1378,plain,
    ( spl5_178
  <=> k1_setfam_1(k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1314,plain,(
    k1_setfam_1(k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f552,f1062])).

fof(f1373,plain,(
    spl5_176 ),
    inference(avatar_split_clause,[],[f1300,f1371])).

fof(f1371,plain,
    ( spl5_176
  <=> k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f1300,plain,(
    k3_tarski(k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f472,f1025])).

fof(f1365,plain,(
    spl5_174 ),
    inference(avatar_split_clause,[],[f1299,f1363])).

fof(f1363,plain,
    ( spl5_174
  <=> k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f1299,plain,(
    k3_tarski(k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f449,f1025])).

fof(f1358,plain,(
    spl5_172 ),
    inference(avatar_split_clause,[],[f1298,f1356])).

fof(f1356,plain,
    ( spl5_172
  <=> k3_tarski(k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1298,plain,(
    k3_tarski(k7_setfam_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) = k1_xboole_0 ),
    inference(unit_resulting_resolution,[],[f552,f1025])).

fof(f1351,plain,
    ( ~ spl5_171
    | spl5_169 ),
    inference(avatar_split_clause,[],[f1344,f1330,f1349])).

fof(f1349,plain,
    ( spl5_171
  <=> ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f1344,plain,
    ( ~ r2_hidden(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_169 ),
    inference(unit_resulting_resolution,[],[f1331,f108])).

fof(f1332,plain,
    ( ~ spl5_169
    | ~ spl5_114
    | spl5_121 ),
    inference(avatar_split_clause,[],[f1325,f958,f935,f1330])).

fof(f1325,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_114
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f1319,f959])).

fof(f1319,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_114 ),
    inference(superposition,[],[f936,f1062])).

fof(f1277,plain,
    ( ~ spl5_167
    | spl5_121 ),
    inference(avatar_split_clause,[],[f968,f958,f1275])).

fof(f1275,plain,
    ( spl5_167
  <=> ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f968,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f472,f959,f122])).

fof(f1270,plain,
    ( ~ spl5_165
    | spl5_121 ),
    inference(avatar_split_clause,[],[f967,f958,f1268])).

fof(f1268,plain,
    ( spl5_165
  <=> ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f967,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f449,f959,f122])).

fof(f1263,plain,
    ( ~ spl5_163
    | spl5_159 ),
    inference(avatar_split_clause,[],[f1239,f1224,f1261])).

fof(f1261,plain,
    ( spl5_163
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f1239,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_159 ),
    inference(unit_resulting_resolution,[],[f1225,f108])).

fof(f1233,plain,
    ( ~ spl5_161
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1219,f1208,f1231])).

fof(f1231,plain,
    ( spl5_161
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f1219,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f1209,f108])).

fof(f1226,plain,
    ( ~ spl5_159
    | ~ spl5_38
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1159,f1147,f355,f1224])).

fof(f1159,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_38
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f356,f1148,f122])).

fof(f1210,plain,
    ( ~ spl5_157
    | ~ spl5_14
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1180,f1177,f179,f1208])).

fof(f1180,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_14
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f1178,f1027])).

fof(f1203,plain,
    ( ~ spl5_155
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1164,f1147,f1201])).

fof(f1201,plain,
    ( spl5_155
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f1164,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f106,f1148,f122])).

fof(f1196,plain,
    ( ~ spl5_153
    | spl5_151 ),
    inference(avatar_split_clause,[],[f1188,f1177,f1194])).

fof(f1194,plain,
    ( spl5_153
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f1188,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_151 ),
    inference(unit_resulting_resolution,[],[f1178,f108])).

fof(f1179,plain,
    ( ~ spl5_151
    | ~ spl5_14
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1157,f1147,f179,f1177])).

fof(f1157,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_14
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f1148,f1027])).

fof(f1172,plain,
    ( ~ spl5_149
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1165,f1147,f1170])).

fof(f1165,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f1148,f108])).

fof(f1156,plain,
    ( spl5_146
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f328,f205,f1154])).

fof(f1154,plain,
    ( spl5_146
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f328,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f112])).

fof(f1149,plain,
    ( ~ spl5_145
    | ~ spl5_14
    | spl5_121 ),
    inference(avatar_split_clause,[],[f1142,f958,f179,f1147])).

fof(f1142,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_14
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f959,f1027])).

fof(f1127,plain,
    ( spl5_142
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f282,f205,f1125])).

fof(f1125,plain,
    ( spl5_142
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1114,plain,
    ( ~ spl5_141
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1107,f1072,f1112])).

fof(f1112,plain,
    ( spl5_141
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f1107,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f1073,f108])).

fof(f1081,plain,
    ( ~ spl5_139
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1039,f1033,f1079])).

fof(f1079,plain,
    ( spl5_139
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f1039,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f106,f1034,f122])).

fof(f1074,plain,
    ( ~ spl5_137
    | ~ spl5_38
    | spl5_121 ),
    inference(avatar_split_clause,[],[f964,f958,f355,f1072])).

fof(f964,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_38
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f356,f959,f122])).

fof(f1054,plain,
    ( ~ spl5_135
    | ~ spl5_108
    | spl5_121 ),
    inference(avatar_split_clause,[],[f987,f958,f909,f1052])).

fof(f1052,plain,
    ( spl5_135
  <=> ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f987,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl5_108
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f959,f910,f122])).

fof(f1047,plain,
    ( ~ spl5_133
    | spl5_131 ),
    inference(avatar_split_clause,[],[f1040,f1033,f1045])).

fof(f1045,plain,
    ( spl5_133
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f1040,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f1034,f108])).

fof(f1035,plain,
    ( ~ spl5_131
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1022,f636,f1033])).

fof(f1022,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f448])).

fof(f1014,plain,
    ( ~ spl5_129
    | spl5_121 ),
    inference(avatar_split_clause,[],[f970,f958,f1012])).

fof(f1012,plain,
    ( spl5_129
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f970,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f106,f959,f122])).

fof(f1007,plain,
    ( ~ spl5_127
    | ~ spl5_100
    | spl5_121 ),
    inference(avatar_split_clause,[],[f966,f958,f818,f1005])).

fof(f966,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_100
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f819,f959,f122])).

fof(f1000,plain,
    ( ~ spl5_125
    | spl5_121 ),
    inference(avatar_split_clause,[],[f971,f958,f998])).

fof(f971,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f959,f108])).

fof(f978,plain,
    ( ~ spl5_123
    | ~ spl5_20
    | spl5_121 ),
    inference(avatar_split_clause,[],[f969,f958,f205,f976])).

fof(f976,plain,
    ( spl5_123
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f969,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl5_20
    | ~ spl5_121 ),
    inference(unit_resulting_resolution,[],[f206,f959,f122])).

fof(f960,plain,
    ( spl5_118
    | ~ spl5_121
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f946,f151,f137,f130,f958,f952])).

fof(f946,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f594,f152])).

fof(f944,plain,
    ( spl5_116
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f843,f818,f942])).

fof(f843,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_100 ),
    inference(backward_demodulation,[],[f831,f833])).

fof(f833,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f115])).

fof(f937,plain,
    ( spl5_114
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f842,f818,f935])).

fof(f842,plain,
    ( m1_subset_1(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_100 ),
    inference(backward_demodulation,[],[f832,f834])).

fof(f834,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f819,f116])).

fof(f924,plain,
    ( ~ spl5_111
    | spl5_112
    | ~ spl5_2
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f826,f818,f811,f137,f922,f916])).

fof(f922,plain,
    ( spl5_112
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f826,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f825,f138])).

fof(f825,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f821,f819])).

fof(f821,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_98 ),
    inference(superposition,[],[f101,f812])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t16_tops_2)).

fof(f911,plain,
    ( spl5_108
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f223,f205,f909])).

fof(f223,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f110])).

fof(f904,plain,
    ( spl5_106
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f484,f479,f902])).

fof(f484,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f480,f110])).

fof(f897,plain,
    ( spl5_104
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f461,f456,f895])).

fof(f461,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f457,f110])).

fof(f853,plain,
    ( spl5_102
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_72
    | ~ spl5_88
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f846,f818,f755,f661,f137,f130,f851])).

fof(f661,plain,
    ( spl5_72
  <=> v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f846,plain,
    ( v3_pre_topc(k1_setfam_1(k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_72
    | ~ spl5_88
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f829,f832])).

fof(f829,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_72
    | ~ spl5_88
    | ~ spl5_100 ),
    inference(unit_resulting_resolution,[],[f131,f138,f662,f756,f819,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_finset_1(X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v1_tops_2(X1,X0) )
           => v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t27_tops_2)).

fof(f662,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f661])).

fof(f820,plain,
    ( spl5_100
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f551,f205,f818])).

fof(f551,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f118])).

fof(f813,plain,
    ( spl5_98
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f509,f205,f811])).

fof(f509,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f117])).

fof(f798,plain,
    ( ~ spl5_97
    | spl5_83 ),
    inference(avatar_split_clause,[],[f718,f709,f796])).

fof(f796,plain,
    ( spl5_97
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f718,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f106,f710,f122])).

fof(f783,plain,
    ( ~ spl5_95
    | spl5_69 ),
    inference(avatar_split_clause,[],[f642,f636,f781])).

fof(f781,plain,
    ( spl5_95
  <=> ~ r2_hidden(k3_tarski(sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f642,plain,
    ( ~ r2_hidden(k3_tarski(sK1),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f106,f637,f122])).

fof(f772,plain,
    ( ~ spl5_93
    | ~ spl5_2
    | spl5_43
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f712,f456,f394,f137,f770])).

fof(f770,plain,
    ( spl5_93
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f712,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_43
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f138,f395,f457,f100])).

fof(f764,plain,
    ( ~ spl5_91
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f734,f692,f762])).

fof(f762,plain,
    ( spl5_91
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f692,plain,
    ( spl5_80
  <=> r2_hidden(sK2(k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f734,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k3_tarski(sK1)))
    | ~ spl5_80 ),
    inference(unit_resulting_resolution,[],[f693,f107])).

fof(f693,plain,
    ( r2_hidden(sK2(k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f692])).

fof(f757,plain,
    ( spl5_88
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f748,f205,f172,f137,f755])).

fof(f748,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f138,f173,f206,f101])).

fof(f747,plain,
    ( ~ spl5_87
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f698,f685,f745])).

fof(f745,plain,
    ( spl5_87
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f685,plain,
    ( spl5_78
  <=> r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f698,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))
    | ~ spl5_78 ),
    inference(unit_resulting_resolution,[],[f686,f107])).

fof(f686,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f685])).

fof(f726,plain,
    ( ~ spl5_85
    | spl5_83 ),
    inference(avatar_split_clause,[],[f719,f709,f724])).

fof(f724,plain,
    ( spl5_85
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f719,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_83 ),
    inference(unit_resulting_resolution,[],[f710,f108])).

fof(f711,plain,
    ( ~ spl5_83
    | ~ spl5_6
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f695,f685,f151,f709])).

fof(f695,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_78 ),
    inference(unit_resulting_resolution,[],[f152,f686,f123])).

fof(f694,plain,
    ( spl5_80
    | spl5_67
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f679,f669,f627,f692])).

fof(f669,plain,
    ( spl5_74
  <=> m1_subset_1(sK2(k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f679,plain,
    ( r2_hidden(sK2(k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl5_67
    | ~ spl5_74 ),
    inference(unit_resulting_resolution,[],[f628,f670,f109])).

fof(f670,plain,
    ( m1_subset_1(sK2(k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f669])).

fof(f687,plain,
    ( spl5_78
    | spl5_67 ),
    inference(avatar_split_clause,[],[f630,f627,f685])).

fof(f630,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f106,f628,f109])).

fof(f678,plain,
    ( ~ spl5_77
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f616,f608,f676])).

fof(f676,plain,
    ( spl5_77
  <=> ~ r2_hidden(k3_tarski(sK1),sK2(k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f616,plain,
    ( ~ r2_hidden(k3_tarski(sK1),sK2(k3_tarski(sK1)))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f609,f107])).

fof(f671,plain,
    ( spl5_74
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f611,f608,f456,f669])).

fof(f611,plain,
    ( m1_subset_1(sK2(k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f457,f609,f122])).

fof(f663,plain,
    ( spl5_72
    | ~ spl5_4
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f655,f205,f188,f144,f661])).

fof(f144,plain,
    ( spl5_4
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f188,plain,
    ( spl5_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f655,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_4
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f189,f145,f206,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
              | ~ v1_finset_1(X1) )
            & ( v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t13_tops_2)).

fof(f145,plain,
    ( v1_finset_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f189,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f650,plain,
    ( ~ spl5_71
    | spl5_69 ),
    inference(avatar_split_clause,[],[f643,f636,f648])).

fof(f643,plain,
    ( ~ r2_hidden(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f637,f108])).

fof(f638,plain,
    ( ~ spl5_69
    | ~ spl5_6
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f612,f608,f151,f636])).

fof(f612,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f152,f609,f123])).

fof(f629,plain,
    ( ~ spl5_67
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f613,f608,f456,f627])).

fof(f613,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_52
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f457,f609,f123])).

fof(f610,plain,
    ( spl5_64
    | spl5_63 ),
    inference(avatar_split_clause,[],[f602,f599,f608])).

fof(f602,plain,
    ( r2_hidden(sK2(k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f106,f600,f109])).

fof(f601,plain,
    ( ~ spl5_63
    | ~ spl5_0
    | ~ spl5_2
    | spl5_43
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f592,f456,f394,f137,f130,f599])).

fof(f592,plain,
    ( ~ v1_xboole_0(k3_tarski(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_43
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f131,f138,f395,f457,f104])).

fof(f561,plain,
    ( spl5_60
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f543,f151,f559])).

fof(f559,plain,
    ( spl5_60
  <=> k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f543,plain,
    ( k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f530,f325])).

fof(f530,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f152,f472,f123])).

fof(f524,plain,
    ( spl5_58
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f513,f151,f522])).

fof(f522,plain,
    ( spl5_58
  <=> k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f513,plain,
    ( k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) = k1_xboole_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f497,f325])).

fof(f497,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_tarski(sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f152,f449,f123])).

fof(f492,plain,
    ( ~ spl5_57
    | spl5_45 ),
    inference(avatar_split_clause,[],[f418,f411,f490])).

fof(f490,plain,
    ( spl5_57
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f418,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f106,f412,f122])).

fof(f481,plain,
    ( spl5_54
    | ~ spl5_20
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f473,f440,f205,f479])).

fof(f473,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f466,f441])).

fof(f466,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f116])).

fof(f458,plain,
    ( spl5_52
    | ~ spl5_20
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f450,f433,f205,f456])).

fof(f450,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f444,f434])).

fof(f444,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f115])).

fof(f442,plain,
    ( spl5_50
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f415,f205,f440])).

fof(f415,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f114])).

fof(f435,plain,
    ( spl5_48
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f379,f205,f433])).

fof(f379,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f206,f113])).

fof(f426,plain,
    ( ~ spl5_47
    | spl5_45 ),
    inference(avatar_split_clause,[],[f419,f411,f424])).

fof(f424,plain,
    ( spl5_47
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f419,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f412,f108])).

fof(f413,plain,
    ( ~ spl5_45
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f397,f355,f151,f411])).

fof(f397,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f152,f356,f123])).

fof(f396,plain,
    ( ~ spl5_43
    | ~ spl5_20
    | spl5_23 ),
    inference(avatar_split_clause,[],[f382,f212,f205,f394])).

fof(f212,plain,
    ( spl5_23
  <=> ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f382,plain,
    ( ~ v4_pre_topc(k3_tarski(sK1),sK0)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f379,f213])).

fof(f213,plain,
    ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f377,plain,
    ( ~ spl5_41
    | ~ spl5_6
    | spl5_37 ),
    inference(avatar_split_clause,[],[f365,f346,f151,f375])).

fof(f375,plain,
    ( spl5_41
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f346,plain,
    ( spl5_37
  <=> k1_zfmisc_1(k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f365,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f152,f347,f120])).

fof(f347,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f346])).

fof(f357,plain,
    ( spl5_36
    | spl5_38
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f323,f258,f355,f349])).

fof(f349,plain,
    ( spl5_36
  <=> k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f323,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl5_28 ),
    inference(resolution,[],[f219,f259])).

fof(f309,plain,
    ( spl5_34
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f292,f277,f307])).

fof(f277,plain,
    ( spl5_32
  <=> v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f292,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f278,f103])).

fof(f278,plain,
    ( v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( spl5_32
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f272,f267,f151,f277])).

fof(f267,plain,
    ( spl5_30
  <=> m1_subset_1(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f272,plain,
    ( v1_xboole_0(k3_subset_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f106,f271,f109])).

fof(f271,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f152,f268,f123])).

fof(f268,plain,
    ( m1_subset_1(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f269,plain,
    ( spl5_30
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f261,f258,f267])).

fof(f261,plain,
    ( m1_subset_1(k3_subset_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_28 ),
    inference(unit_resulting_resolution,[],[f259,f110])).

fof(f260,plain,
    ( spl5_28
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f253,f250,f258])).

fof(f250,plain,
    ( spl5_26
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f253,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_26 ),
    inference(superposition,[],[f106,f251])).

fof(f251,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f250])).

fof(f252,plain,
    ( spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f237,f228,f250])).

fof(f228,plain,
    ( spl5_24
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f237,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f229,f103])).

fof(f229,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl5_24
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f221,f151,f228])).

fof(f221,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f106,f220,f109])).

fof(f220,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f152,f106,f123])).

fof(f214,plain,(
    ~ spl5_23 ),
    inference(avatar_split_clause,[],[f91,f212])).

fof(f91,plain,(
    ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    & v1_finset_1(sK1)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
            & v1_finset_1(X1)
            & v2_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),sK1),X0)
        & v1_finset_1(sK1)
        & v2_tops_2(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ( v1_finset_1(X1)
                & v2_tops_2(X1,X0) )
             => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v2_tops_2(X1,X0) )
           => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t28_tops_2)).

fof(f207,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f88,f205])).

fof(f88,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f197,plain,
    ( spl5_18
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f183,f165,f195])).

fof(f195,plain,
    ( spl5_18
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f165,plain,
    ( spl5_10
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f183,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f166,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',dt_l1_pre_topc)).

fof(f166,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f190,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f182,f137,f188])).

fof(f182,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f138,f98])).

fof(f181,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f93,f179])).

fof(f93,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',t2_zfmisc_1)).

fof(f174,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f89,f172])).

fof(f89,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f167,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f125,f165])).

fof(f125,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f84])).

fof(f84,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',existence_l1_pre_topc)).

fof(f160,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f124,f158])).

fof(f158,plain,
    ( spl5_8
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f124,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f82])).

fof(f82,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',existence_l1_struct_0)).

fof(f153,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f92,f151])).

fof(f92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t28_tops_2.p',fc1_xboole_0)).

fof(f146,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f90,f144])).

fof(f90,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f139,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f87,f137])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f132,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f86,f130])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
