%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t17_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:21 EDT 2019

% Result     : Theorem 143.34s
% Output     : Refutation 143.41s
% Verified   : 
% Statistics : Number of formulae       : 2190 (15979 expanded)
%              Number of leaves         :  483 (5469 expanded)
%              Depth                    :   24
%              Number of atoms          : 7976 (49544 expanded)
%              Number of equality atoms :  753 (9826 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f104,f117,f135,f154,f167,f183,f184,f203,f228,f252,f259,f314,f336,f362,f376,f390,f515,f651,f656,f696,f703,f710,f717,f725,f758,f762,f781,f782,f975,f978,f1023,f1024,f1031,f1038,f1045,f1086,f1088,f1112,f1219,f1251,f1258,f1282,f1573,f1602,f1606,f1607,f1966,f1975,f1978,f1987,f1990,f1993,f1996,f1997,f1998,f1999,f2000,f2002,f2004,f2006,f2054,f2067,f2122,f2201,f2232,f2315,f2319,f2392,f2415,f2729,f2745,f2746,f2900,f2904,f3204,f3209,f3791,f4183,f4222,f4326,f4337,f4344,f4345,f4346,f4347,f4350,f4351,f4352,f4355,f4367,f4375,f4381,f4527,f4578,f4582,f4636,f4869,f4891,f4892,f4973,f4988,f5051,f5270,f5312,f5313,f5361,f5365,f5366,f5398,f5399,f5789,f5809,f5920,f6169,f6223,f6248,f6254,f6274,f6338,f6344,f6459,f6591,f6601,f6611,f6621,f6622,f6632,f6639,f6649,f6653,f6663,f6673,f6683,f6687,f6697,f6701,f6711,f6721,f6731,f6747,f6751,f6767,f6821,f6828,f6835,f6882,f7011,f7055,f7150,f7154,f7155,f7225,f7239,f7257,f7396,f7442,f7453,f7465,f7479,f7486,f7538,f7570,f7865,f7923,f8020,f8134,f8142,f8149,f8276,f8357,f8415,f8417,f8425,f8433,f8519,f8527,f8649,f8819,f8826,f8833,f8840,f8844,f8851,f8986,f8996,f9019,f9025,f9031,f9037,f9749,f9756,f9763,f9767,f9774,f9913,f10008,f10825,f10826,f12636,f12637,f12638,f12642,f12646,f12650,f12654,f12658,f12662,f12666,f12670,f12671,f12675,f12855,f13073,f13085,f13091,f13162,f13203,f13210,f13226,f13401,f13872,f13876,f13883,f13887,f13893,f13899,f13906,f13920,f13924,f13930,f13936,f13943,f13950,f13956,f13967,f13974,f13984,f13993,f14001,f14007,f14018,f14026,f14035,f14043,f14050,f14056,f14062,f14069,f14076,f14085,f14095,f14119,f14130,f14137,f14144,f14150,f14162,f14174,f14183,f14192,f14200,f14817,f14821,f14833,f14851,f14963,f14968,f14976,f14991,f15001,f15177,f15178,f15181,f15182,f15185,f15186,f15187,f15190,f15192,f15193,f15294,f15298,f15299,f15306,f15313,f15319,f15320,f15327,f15334,f15341,f15348,f15355,f15362,f15369,f15378,f15739,f15746,f15755,f15771,f15785,f15828,f15889,f15994,f16067,f16068,f16075,f16171,f16585,f16592,f16657,f16683,f16716,f16959,f16963,f17351,f17358,f17365,f17502,f17715,f17859,f17864,f17866,f17871,f17950,f17954,f17962,f18455,f18615,f18912,f18928,f19260,f19578,f19597,f19673,f19833,f19840,f19926,f19945,f19964,f19985,f20212,f20213,f20231,f20232,f20239,f20246,f20561,f20730,f20770,f20779,f20906,f21631,f22136,f22142,f22851,f22852,f22859,f23225,f23233,f23247,f23255,f24210,f26517,f28417,f28623,f28631,f30393,f30400,f30407,f30414,f30439,f30513,f30520,f30527,f30528,f30599,f30792,f30805,f35200,f35209,f36781,f40719,f40726,f40733,f40740,f41224,f41229,f42016,f42241,f42383,f42586,f42593,f42959,f42960,f42964,f42999,f43006,f43013,f43656,f43779,f43820,f43829,f44044,f44049,f44056,f44057,f44059,f48677,f48811,f48830,f49828,f49834,f54496,f55131,f55139,f55158,f55159,f55172,f55458])).

fof(f55458,plain,
    ( spl8_166
    | ~ spl8_1
    | ~ spl8_419
    | ~ spl8_614 ),
    inference(avatar_split_clause,[],[f55457,f17713,f13083,f64,f4339])).

fof(f4339,plain,
    ( spl8_166
  <=> r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).

fof(f64,plain,
    ( spl8_1
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f13083,plain,
    ( spl8_419
  <=> ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_419])])).

fof(f17713,plain,
    ( spl8_614
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK1,k4_xboole_0(sK2,sK3)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_614])])).

fof(f55457,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_614 ),
    inference(duplicate_literal_removal,[],[f55453])).

fof(f55453,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_614 ),
    inference(resolution,[],[f17714,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t7_subset_1)).

fof(f17714,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl8_614 ),
    inference(avatar_component_clause,[],[f17713])).

fof(f55172,plain,
    ( ~ spl8_839
    | ~ spl8_835
    | ~ spl8_841
    | spl8_833 ),
    inference(avatar_split_clause,[],[f55149,f55129,f55170,f55137,f55164])).

fof(f55164,plain,
    ( spl8_839
  <=> ~ r2_hidden(sK3,sK4(sK1,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_839])])).

fof(f55137,plain,
    ( spl8_835
  <=> ~ m1_subset_1(sK4(sK1,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_835])])).

fof(f55170,plain,
    ( spl8_841
  <=> ~ r2_hidden(sK4(sK1,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_841])])).

fof(f55129,plain,
    ( spl8_833
  <=> ~ r2_hidden(sK4(sK1,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_833])])).

fof(f55149,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,sK3),sK2)
    | ~ m1_subset_1(sK4(sK1,sK1,sK3),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK1,sK3))
    | ~ spl8_833 ),
    inference(resolution,[],[f55130,f119])).

fof(f119,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(sK3,X1) ) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t17_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',antisymmetry_r2_hidden)).

fof(f55130,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ spl8_833 ),
    inference(avatar_component_clause,[],[f55129])).

fof(f55159,plain,
    ( ~ spl8_837
    | ~ spl8_216
    | spl8_833 ),
    inference(avatar_split_clause,[],[f55148,f55129,f6161,f55156])).

fof(f55156,plain,
    ( spl8_837
  <=> ~ r2_hidden(sK4(sK1,sK1,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_837])])).

fof(f6161,plain,
    ( spl8_216
  <=> k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_216])])).

fof(f55148,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,sK3),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_833 ),
    inference(resolution,[],[f55130,f17168])).

fof(f17168,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK1)
        | ~ r2_hidden(X8,k1_xboole_0) )
    | ~ spl8_216 ),
    inference(resolution,[],[f15599,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',d5_xboole_0)).

fof(f15599,plain,
    ( ! [X30] :
        ( sP5(X30,sK2,sK1)
        | ~ r2_hidden(X30,k1_xboole_0) )
    | ~ spl8_216 ),
    inference(superposition,[],[f59,f6162])).

fof(f6162,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl8_216 ),
    inference(avatar_component_clause,[],[f6161])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f55158,plain,
    ( ~ spl8_837
    | spl8_76
    | ~ spl8_592
    | spl8_833 ),
    inference(avatar_split_clause,[],[f55151,f55129,f16655,f649,f55156])).

fof(f649,plain,
    ( spl8_76
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f16655,plain,
    ( spl8_592
  <=> k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_592])])).

fof(f55151,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),k1_xboole_0)
    | ~ spl8_592
    | ~ spl8_833 ),
    inference(forward_demodulation,[],[f55145,f16656])).

fof(f16656,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ spl8_592 ),
    inference(avatar_component_clause,[],[f16655])).

fof(f55145,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),k1_xboole_0)
    | ~ spl8_833 ),
    inference(resolution,[],[f55130,f4199])).

fof(f4199,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X4,X5,X3),X4)
      | k4_xboole_0(X4,X5) = X3
      | ~ r2_hidden(sK4(X4,X5,X3),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f4198,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t3_boole)).

fof(f4198,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X4,X5) = X3
      | r2_hidden(sK4(X4,X5,X3),X4)
      | ~ r2_hidden(sK4(X4,X5,k4_xboole_0(X3,k1_xboole_0)),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f2972,f51])).

fof(f2972,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X4,X5,X3),X4)
      | k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X4,X5)
      | ~ r2_hidden(sK4(X4,X5,k4_xboole_0(X3,k1_xboole_0)),k1_xboole_0) ) ),
    inference(superposition,[],[f1513,f51])).

fof(f1513,plain,(
    ! [X21,X19,X20,X18] :
      ( r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X21)),X18)
      | k4_xboole_0(X18,X19) = k4_xboole_0(X20,X21)
      | ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X21)),X21) ) ),
    inference(resolution,[],[f418,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f418,plain,(
    ! [X6,X8,X7,X9] :
      ( sP5(sK4(X6,X7,k4_xboole_0(X8,X9)),X9,X8)
      | r2_hidden(sK4(X6,X7,k4_xboole_0(X8,X9)),X6)
      | k4_xboole_0(X6,X7) = k4_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f282,f59])).

fof(f282,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X5)
      | k4_xboole_0(X3,X4) = X5
      | r2_hidden(sK4(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f55139,plain,
    ( ~ spl8_835
    | ~ spl8_833
    | spl8_76
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f55132,f16655,f1211,f649,f55129,f55137])).

fof(f1211,plain,
    ( spl8_116
  <=> k4_xboole_0(sK3,sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f55132,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK1,sK1,sK3),sK0)
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f55121,f16656])).

fof(f55121,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK1,sK1,sK3),sK0)
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f55101])).

fof(f55101,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | k4_xboole_0(sK1,sK1) = sK3
    | ~ m1_subset_1(sK4(sK1,sK1,sK3),sK0)
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ spl8_116 ),
    inference(resolution,[],[f30035,f421])).

fof(f421,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK4(X15,X16,sK3),X15)
      | k4_xboole_0(X15,X16) = sK3
      | ~ m1_subset_1(sK4(X15,X16,sK3),sK0)
      | ~ r2_hidden(sK4(X15,X16,sK3),sK1) ) ),
    inference(resolution,[],[f282,f31])).

fof(f31,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30035,plain,
    ( ! [X31] :
        ( ~ r2_hidden(sK4(X31,sK1,sK3),sK1)
        | k4_xboole_0(X31,sK1) = sK3
        | ~ r2_hidden(sK4(X31,sK1,sK3),X31) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f30034,f1212])).

fof(f1212,plain,
    ( k4_xboole_0(sK3,sK1) = sK3
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f30034,plain,
    ( ! [X31] :
        ( k4_xboole_0(X31,sK1) = sK3
        | ~ r2_hidden(sK4(X31,sK1,sK3),sK1)
        | ~ r2_hidden(sK4(X31,sK1,k4_xboole_0(sK3,sK1)),X31) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f29990,f1212])).

fof(f29990,plain,
    ( ! [X31] :
        ( ~ r2_hidden(sK4(X31,sK1,sK3),sK1)
        | k4_xboole_0(sK3,sK1) = k4_xboole_0(X31,sK1)
        | ~ r2_hidden(sK4(X31,sK1,k4_xboole_0(sK3,sK1)),X31) )
    | ~ spl8_116 ),
    inference(superposition,[],[f11571,f1212])).

fof(f11571,plain,(
    ! [X19,X20,X18] :
      ( ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X19)),X19)
      | k4_xboole_0(X18,X19) = k4_xboole_0(X20,X19)
      | ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X19)),X18) ) ),
    inference(duplicate_literal_removal,[],[f11545])).

fof(f11545,plain,(
    ! [X19,X20,X18] :
      ( ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X19)),X19)
      | k4_xboole_0(X18,X19) = k4_xboole_0(X20,X19)
      | ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X19)),X18)
      | k4_xboole_0(X18,X19) = k4_xboole_0(X20,X19)
      | ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X19)),X19) ) ),
    inference(resolution,[],[f2867,f281])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f42,f39])).

fof(f2867,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))
      | ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),X1)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X1)
      | ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f2853])).

fof(f2853,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X2,X1)
      | ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),X1)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X1)
      | ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))
      | ~ r2_hidden(sK4(X0,X1,k4_xboole_0(X2,X1)),X0) ) ),
    inference(resolution,[],[f1479,f287])).

fof(f287,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X4)
      | k4_xboole_0(X3,X4) = X5
      | ~ r2_hidden(sK4(X3,X4,X5),X5)
      | ~ r2_hidden(sK4(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(sK4(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1479,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X21)),X21)
      | k4_xboole_0(X18,X19) = k4_xboole_0(X20,X21)
      | ~ r2_hidden(sK4(X18,X19,k4_xboole_0(X20,X21)),X19) ) ),
    inference(resolution,[],[f409,f39])).

fof(f409,plain,(
    ! [X6,X8,X7,X9] :
      ( sP5(sK4(X6,X7,k4_xboole_0(X8,X9)),X9,X8)
      | ~ r2_hidden(sK4(X6,X7,k4_xboole_0(X8,X9)),X7)
      | k4_xboole_0(X6,X7) = k4_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f281,f59])).

fof(f55131,plain,
    ( ~ spl8_833
    | spl8_76
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f55124,f16655,f1211,f649,f55129])).

fof(f55124,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f55122,f16656])).

fof(f55122,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f55100])).

fof(f55100,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK1,sK1,sK3),sK1)
    | ~ spl8_116 ),
    inference(resolution,[],[f30035,f2577])).

fof(f2577,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK4(X4,X5,sK3),X4)
        | k4_xboole_0(X4,X5) = sK3
        | ~ r2_hidden(sK4(X4,X5,sK3),sK1) )
    | ~ spl8_116 ),
    inference(resolution,[],[f2541,f282])).

fof(f2541,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl8_116 ),
    inference(resolution,[],[f2445,f39])).

fof(f2445,plain,
    ( ! [X3] :
        ( sP5(X3,sK1,sK3)
        | ~ r2_hidden(X3,sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f59,f1212])).

fof(f54496,plain,
    ( ~ spl8_699
    | spl8_76
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f54495,f16655,f1211,f649,f20904])).

fof(f20904,plain,
    ( spl8_699
  <=> ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_699])])).

fof(f54495,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),sK1)
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f54494,f16656])).

fof(f54494,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),sK1)
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f54471,f1212])).

fof(f54471,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),sK1)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK1)
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(superposition,[],[f18867,f16656])).

fof(f18867,plain,
    ( ! [X37] :
        ( ~ r2_hidden(sK4(sK3,X37,k4_xboole_0(X37,X37)),sK1)
        | k4_xboole_0(sK3,X37) = k4_xboole_0(X37,X37) )
    | ~ spl8_116 ),
    inference(resolution,[],[f6917,f2541])).

fof(f6917,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,k4_xboole_0(X1,X1)),X0)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X1,X1) ) ),
    inference(duplicate_literal_removal,[],[f6883])).

fof(f6883,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X1)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X1,X1)
      | r2_hidden(sK4(X0,X1,k4_xboole_0(X1,X1)),X0) ) ),
    inference(resolution,[],[f2933,f1514])).

fof(f1514,plain,(
    ! [X24,X23,X25,X22] :
      ( r2_hidden(sK4(X22,X23,k4_xboole_0(X24,X25)),X24)
      | k4_xboole_0(X22,X23) = k4_xboole_0(X24,X25)
      | r2_hidden(sK4(X22,X23,k4_xboole_0(X24,X25)),X22) ) ),
    inference(resolution,[],[f418,f38])).

fof(f2933,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(X9,X10,k4_xboole_0(X11,X11)),X10)
      | k4_xboole_0(X9,X10) = k4_xboole_0(X11,X11) ) ),
    inference(duplicate_literal_removal,[],[f2908])).

fof(f2908,plain,(
    ! [X10,X11,X9] :
      ( k4_xboole_0(X9,X10) = k4_xboole_0(X11,X11)
      | ~ r2_hidden(sK4(X9,X10,k4_xboole_0(X11,X11)),X10)
      | k4_xboole_0(X9,X10) = k4_xboole_0(X11,X11)
      | ~ r2_hidden(sK4(X9,X10,k4_xboole_0(X11,X11)),X10) ) ),
    inference(resolution,[],[f1480,f1479])).

fof(f1480,plain,(
    ! [X24,X23,X25,X22] :
      ( r2_hidden(sK4(X22,X23,k4_xboole_0(X24,X25)),X24)
      | k4_xboole_0(X22,X23) = k4_xboole_0(X24,X25)
      | ~ r2_hidden(sK4(X22,X23,k4_xboole_0(X24,X25)),X23) ) ),
    inference(resolution,[],[f409,f38])).

fof(f49834,plain,
    ( spl8_20
    | spl8_830
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f49830,f18910,f49832,f137])).

fof(f137,plain,
    ( spl8_20
  <=> r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f49832,plain,
    ( spl8_830
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X6,sK0)
        | ~ sP5(sK3,k1_xboole_0,X6)
        | ~ sP5(sK1,k1_xboole_0,X6)
        | ~ r2_hidden(k4_xboole_0(X5,sK2),X6)
        | ~ r2_hidden(sK2,X5)
        | ~ r2_hidden(X6,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_830])])).

fof(f18910,plain,
    ( spl8_632
  <=> k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_632])])).

fof(f49830,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X6,sK0)
        | ~ r2_hidden(X6,X5)
        | r2_hidden(sK2,sK2)
        | ~ r2_hidden(sK2,X5)
        | ~ r2_hidden(k4_xboole_0(X5,sK2),X6)
        | ~ sP5(sK1,k1_xboole_0,X6)
        | ~ sP5(sK3,k1_xboole_0,X6) )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f49829,f51])).

fof(f49829,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,X5)
        | r2_hidden(sK2,sK2)
        | ~ r2_hidden(sK2,X5)
        | ~ r2_hidden(k4_xboole_0(X5,sK2),X6)
        | ~ m1_subset_1(k4_xboole_0(X6,k1_xboole_0),sK0)
        | ~ sP5(sK1,k1_xboole_0,X6)
        | ~ sP5(sK3,k1_xboole_0,X6) )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f49785,f51])).

fof(f49785,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK2,sK2)
        | ~ r2_hidden(sK2,X5)
        | ~ r2_hidden(k4_xboole_0(X5,sK2),X6)
        | ~ r2_hidden(k4_xboole_0(X6,k1_xboole_0),X5)
        | ~ m1_subset_1(k4_xboole_0(X6,k1_xboole_0),sK0)
        | ~ sP5(sK1,k1_xboole_0,X6)
        | ~ sP5(sK3,k1_xboole_0,X6) )
    | ~ spl8_632 ),
    inference(resolution,[],[f44825,f8751])).

fof(f8751,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(k4_xboole_0(X21,sK2),X23)
      | ~ r2_hidden(k4_xboole_0(X21,sK2),X22)
      | ~ r2_hidden(k4_xboole_0(X22,X23),X21)
      | ~ m1_subset_1(k4_xboole_0(X22,X23),sK0)
      | ~ sP5(sK1,X23,X22)
      | ~ sP5(sK3,X23,X22) ) ),
    inference(resolution,[],[f2107,f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_xboole_0(X0,X1),sK2)
      | ~ m1_subset_1(k4_xboole_0(X0,X1),sK0)
      | ~ sP5(sK1,X1,X0)
      | ~ sP5(sK3,X1,X0) ) ),
    inference(resolution,[],[f338,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f338,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3,k4_xboole_0(X5,X4))
      | ~ r2_hidden(k4_xboole_0(X5,X4),sK2)
      | ~ m1_subset_1(k4_xboole_0(X5,X4),sK0)
      | ~ sP5(sK1,X4,X5) ) ),
    inference(resolution,[],[f230,f119])).

fof(f230,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_xboole_0(X5,X4),X3)
      | ~ sP5(X3,X4,X5) ) ),
    inference(resolution,[],[f60,f57])).

fof(f2107,plain,(
    ! [X14,X12,X15,X13] :
      ( r2_hidden(k4_xboole_0(X15,X14),X13)
      | ~ r2_hidden(k4_xboole_0(X12,X13),X15)
      | r2_hidden(k4_xboole_0(X12,X13),X14)
      | ~ r2_hidden(k4_xboole_0(X15,X14),X12) ) ),
    inference(resolution,[],[f918,f37])).

fof(f918,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP5(k4_xboole_0(X8,X9),X10,X11)
      | r2_hidden(k4_xboole_0(X11,X10),X9)
      | ~ r2_hidden(k4_xboole_0(X11,X10),X8) ) ),
    inference(resolution,[],[f337,f37])).

fof(f337,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(k4_xboole_0(X3,X2),X1,X0)
      | ~ sP5(k4_xboole_0(X0,X1),X2,X3) ) ),
    inference(resolution,[],[f230,f60])).

fof(f44825,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_xboole_0(X8,X9),k1_xboole_0)
        | r2_hidden(sK2,X9)
        | ~ r2_hidden(sK2,X8) )
    | ~ spl8_632 ),
    inference(resolution,[],[f44661,f2119])).

fof(f2119,plain,(
    ! [X21,X19,X20] :
      ( ~ r2_hidden(k4_xboole_0(X21,X20),X19)
      | r2_hidden(X19,X20)
      | ~ r2_hidden(X19,X21) ) ),
    inference(forward_demodulation,[],[f2118,f51])).

fof(f2118,plain,(
    ! [X21,X19,X20] :
      ( r2_hidden(X19,X20)
      | ~ r2_hidden(k4_xboole_0(X19,k1_xboole_0),X21)
      | ~ r2_hidden(k4_xboole_0(X21,X20),X19) ) ),
    inference(forward_demodulation,[],[f2109,f51])).

fof(f2109,plain,(
    ! [X21,X19,X20] :
      ( r2_hidden(k4_xboole_0(X19,k1_xboole_0),X20)
      | ~ r2_hidden(k4_xboole_0(X19,k1_xboole_0),X21)
      | ~ r2_hidden(k4_xboole_0(X21,X20),X19) ) ),
    inference(resolution,[],[f918,f186])).

fof(f186,plain,(
    ! [X2,X3] :
      ( sP5(X3,k1_xboole_0,X2)
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f59,f51])).

fof(f44661,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_632 ),
    inference(resolution,[],[f43200,f38])).

fof(f43200,plain,
    ( ! [X162] :
        ( sP5(X162,sK2,sK2)
        | ~ r2_hidden(X162,k1_xboole_0) )
    | ~ spl8_632 ),
    inference(superposition,[],[f59,f18911])).

fof(f18911,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ spl8_632 ),
    inference(avatar_component_clause,[],[f18910])).

fof(f49828,plain,
    ( spl8_16
    | spl8_828
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f49824,f18910,f49826,f124])).

fof(f124,plain,
    ( spl8_16
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f49826,plain,
    ( spl8_828
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X4,sK0)
        | ~ sP5(sK2,k1_xboole_0,X4)
        | ~ r2_hidden(k4_xboole_0(X3,sK1),X4)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_828])])).

fof(f49824,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,sK0)
        | ~ r2_hidden(X4,X3)
        | r2_hidden(sK2,sK1)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK1),X4)
        | ~ sP5(sK2,k1_xboole_0,X4) )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f49823,f51])).

fof(f49823,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,X3)
        | r2_hidden(sK2,sK1)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK1),X4)
        | ~ m1_subset_1(k4_xboole_0(X4,k1_xboole_0),sK0)
        | ~ sP5(sK2,k1_xboole_0,X4) )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f49784,f51])).

fof(f49784,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2,sK1)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK1),X4)
        | ~ r2_hidden(k4_xboole_0(X4,k1_xboole_0),X3)
        | ~ m1_subset_1(k4_xboole_0(X4,k1_xboole_0),sK0)
        | ~ sP5(sK2,k1_xboole_0,X4) )
    | ~ spl8_632 ),
    inference(resolution,[],[f44825,f8750])).

fof(f8750,plain,(
    ! [X19,X20,X18] :
      ( r2_hidden(k4_xboole_0(X18,sK1),X20)
      | ~ r2_hidden(k4_xboole_0(X18,sK1),X19)
      | ~ r2_hidden(k4_xboole_0(X19,X20),X18)
      | ~ m1_subset_1(k4_xboole_0(X19,X20),sK0)
      | ~ sP5(sK2,X20,X19) ) ),
    inference(resolution,[],[f2107,f232])).

fof(f232,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(k4_xboole_0(X10,X9),sK1)
      | ~ m1_subset_1(k4_xboole_0(X10,X9),sK0)
      | ~ sP5(sK2,X9,X10) ) ),
    inference(resolution,[],[f60,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48830,plain,
    ( ~ spl8_823
    | ~ spl8_825
    | ~ spl8_827
    | spl8_817 ),
    inference(avatar_split_clause,[],[f48802,f48669,f48828,f48822,f48816])).

fof(f48816,plain,
    ( spl8_823
  <=> ~ r2_hidden(sK3,sK4(sK3,sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_823])])).

fof(f48822,plain,
    ( spl8_825
  <=> ~ m1_subset_1(sK4(sK3,sK2,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_825])])).

fof(f48828,plain,
    ( spl8_827
  <=> ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_827])])).

fof(f48669,plain,
    ( spl8_817
  <=> ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_817])])).

fof(f48802,plain,
    ( ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),sK2)
    | ~ m1_subset_1(sK4(sK3,sK2,k1_xboole_0),sK0)
    | ~ r2_hidden(sK3,sK4(sK3,sK2,k1_xboole_0))
    | ~ spl8_817 ),
    inference(resolution,[],[f48670,f119])).

fof(f48670,plain,
    ( ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),sK1)
    | ~ spl8_817 ),
    inference(avatar_component_clause,[],[f48669])).

fof(f48811,plain,
    ( ~ spl8_821
    | ~ spl8_216
    | spl8_817 ),
    inference(avatar_split_clause,[],[f48801,f48669,f6161,f48809])).

fof(f48809,plain,
    ( spl8_821
  <=> ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_821])])).

fof(f48801,plain,
    ( ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_817 ),
    inference(resolution,[],[f48670,f17168])).

fof(f48677,plain,
    ( ~ spl8_817
    | spl8_818
    | ~ spl8_116
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f48644,f18910,f1211,f48675,f48669])).

fof(f48675,plain,
    ( spl8_818
  <=> k4_xboole_0(sK3,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_818])])).

fof(f48644,plain,
    ( k4_xboole_0(sK3,sK2) = k1_xboole_0
    | ~ r2_hidden(sK4(sK3,sK2,k1_xboole_0),sK1)
    | ~ spl8_116
    | ~ spl8_632 ),
    inference(resolution,[],[f43641,f2541])).

fof(f43641,plain,
    ( ! [X115] :
        ( r2_hidden(sK4(X115,sK2,k1_xboole_0),X115)
        | k4_xboole_0(X115,sK2) = k1_xboole_0 )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f43156,f18911])).

fof(f43156,plain,
    ( ! [X115] :
        ( r2_hidden(sK4(X115,sK2,k1_xboole_0),X115)
        | k4_xboole_0(sK2,sK2) = k4_xboole_0(X115,sK2) )
    | ~ spl8_632 ),
    inference(superposition,[],[f6917,f18911])).

fof(f44059,plain,
    ( ~ spl8_811
    | ~ spl8_815
    | ~ spl8_53
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43477,f18910,f6161,f306,f44054,f44042])).

fof(f44042,plain,
    ( spl8_811
  <=> ~ sP5(sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_811])])).

fof(f44054,plain,
    ( spl8_815
  <=> ~ sP5(k1_xboole_0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_815])])).

fof(f306,plain,
    ( spl8_53
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f43477,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ sP5(k1_xboole_0,sK2,sK2)
    | ~ sP5(sK2,sK2,sK2)
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(superposition,[],[f32596,f18911])).

fof(f32596,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(k4_xboole_0(X7,X6),sK1)
        | ~ sP5(k1_xboole_0,X6,X7)
        | ~ sP5(sK2,X6,X7) )
    | ~ spl8_216 ),
    inference(resolution,[],[f15630,f230])).

fof(f15630,plain,
    ( ! [X70,X69] :
        ( r2_hidden(k4_xboole_0(X70,X69),sK2)
        | ~ sP5(k1_xboole_0,X69,X70)
        | ~ r2_hidden(k4_xboole_0(X70,X69),sK1) )
    | ~ spl8_216 ),
    inference(superposition,[],[f918,f6162])).

fof(f44057,plain,
    ( ~ spl8_815
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43457,f18910,f44054])).

fof(f43457,plain,
    ( ~ sP5(k1_xboole_0,sK2,sK2)
    | ~ spl8_632 ),
    inference(superposition,[],[f23136,f18911])).

fof(f23136,plain,(
    ! [X2,X1] : ~ sP5(k4_xboole_0(X1,X2),X2,X1) ),
    inference(resolution,[],[f23048,f60])).

fof(f23048,plain,(
    ! [X3] : ~ r2_hidden(X3,X3) ),
    inference(duplicate_literal_removal,[],[f22967])).

fof(f22967,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,X3)
      | ~ r2_hidden(X3,X3) ) ),
    inference(resolution,[],[f14824,f14823])).

fof(f14823,plain,(
    ! [X26,X25] :
      ( ~ r2_hidden(X25,X26)
      | ~ r2_hidden(X25,X25) ) ),
    inference(forward_demodulation,[],[f14822,f51])).

fof(f14822,plain,(
    ! [X26,X25] :
      ( ~ r2_hidden(X25,X25)
      | ~ r2_hidden(k4_xboole_0(X25,k1_xboole_0),X26) ) ),
    inference(forward_demodulation,[],[f14799,f51])).

fof(f14799,plain,(
    ! [X26,X25] :
      ( ~ r2_hidden(k4_xboole_0(X25,k1_xboole_0),X25)
      | ~ r2_hidden(k4_xboole_0(X25,k1_xboole_0),X26) ) ),
    inference(resolution,[],[f8789,f270])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f185,f39])).

fof(f185,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t4_boole)).

fof(f8789,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_xboole_0(X0,X1),X1)
      | ~ r2_hidden(k4_xboole_0(X0,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f8779])).

fof(f8779,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_xboole_0(X0,X1),X1)
      | ~ r2_hidden(k4_xboole_0(X0,X1),X0)
      | ~ r2_hidden(k4_xboole_0(X0,X1),X0) ) ),
    inference(factoring,[],[f2107])).

fof(f14824,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X0) ) ),
    inference(forward_demodulation,[],[f14803,f51])).

fof(f14803,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(k4_xboole_0(X0,k1_xboole_0),X0) ) ),
    inference(superposition,[],[f8789,f51])).

fof(f44056,plain,
    ( ~ spl8_809
    | ~ spl8_815
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43456,f18910,f6161,f44054,f43818])).

fof(f43818,plain,
    ( spl8_809
  <=> ~ sP5(sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_809])])).

fof(f43456,plain,
    ( ~ sP5(k1_xboole_0,sK2,sK2)
    | ~ sP5(sK1,sK2,sK2)
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(superposition,[],[f22398,f18911])).

fof(f22398,plain,
    ( ! [X8,X7] :
        ( ~ sP5(k4_xboole_0(X8,X7),X7,X8)
        | ~ sP5(sK1,X7,X8) )
    | ~ spl8_216 ),
    inference(resolution,[],[f18955,f60])).

fof(f18955,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))
        | ~ sP5(sK1,X2,X1) )
    | ~ spl8_216 ),
    inference(resolution,[],[f18936,f60])).

fof(f18936,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_hidden(X0,X0) )
    | ~ spl8_216 ),
    inference(resolution,[],[f18763,f186])).

fof(f18763,plain,
    ( ! [X0] :
        ( ~ sP5(sK1,k1_xboole_0,X0)
        | ~ r2_hidden(X0,X0) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f18745,f51])).

fof(f18745,plain,
    ( ! [X0] :
        ( ~ sP5(sK1,k1_xboole_0,X0)
        | ~ r2_hidden(k4_xboole_0(X0,k1_xboole_0),X0) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17257,f8789])).

fof(f17257,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(k4_xboole_0(X9,X10),k1_xboole_0)
        | ~ sP5(sK1,X10,X9) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17168,f230])).

fof(f44049,plain,
    ( ~ spl8_811
    | ~ spl8_53
    | spl8_812
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f44045,f18910,f6161,f44047,f306,f44042])).

fof(f44047,plain,
    ( spl8_812
  <=> ! [X546] : ~ r2_hidden(k1_xboole_0,X546) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_812])])).

fof(f44045,plain,
    ( ! [X546] :
        ( ~ r2_hidden(k1_xboole_0,X546)
        | ~ r2_hidden(k1_xboole_0,sK1)
        | ~ sP5(sK2,sK2,sK2) )
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f43453,f18911])).

fof(f43453,plain,
    ( ! [X546] :
        ( ~ r2_hidden(k1_xboole_0,sK1)
        | ~ r2_hidden(k4_xboole_0(sK2,sK2),X546)
        | ~ sP5(sK2,sK2,sK2) )
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(superposition,[],[f19153,f18911])).

fof(f19153,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(k4_xboole_0(X2,X3),sK1)
        | ~ r2_hidden(k4_xboole_0(X2,X3),X4)
        | ~ sP5(sK2,X3,X2) )
    | ~ spl8_216 ),
    inference(resolution,[],[f19038,f60])).

fof(f19038,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,X2) )
    | ~ spl8_216 ),
    inference(resolution,[],[f18541,f270])).

fof(f18541,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(sK2,X1) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17614,f57])).

fof(f17614,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK2)
        | r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl8_216 ),
    inference(resolution,[],[f15600,f37])).

fof(f15600,plain,
    ( ! [X31] :
        ( ~ sP5(X31,sK2,sK1)
        | r2_hidden(X31,k1_xboole_0) )
    | ~ spl8_216 ),
    inference(superposition,[],[f60,f6162])).

fof(f44044,plain,
    ( ~ spl8_811
    | spl8_126
    | ~ spl8_53
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f44037,f18910,f6161,f306,f1597,f44042])).

fof(f1597,plain,
    ( spl8_126
  <=> r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f44037,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ sP5(sK2,sK2,sK2)
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f43450,f18911])).

fof(f43450,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k4_xboole_0(sK2,sK2),sK1)
    | ~ sP5(sK2,sK2,sK2)
    | ~ spl8_216
    | ~ spl8_632 ),
    inference(superposition,[],[f18546,f18911])).

fof(f18546,plain,
    ( ! [X10,X9] :
        ( r2_hidden(k4_xboole_0(X9,X10),k1_xboole_0)
        | ~ r2_hidden(k4_xboole_0(X9,X10),sK1)
        | ~ sP5(sK2,X10,X9) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17614,f230])).

fof(f43829,plain,
    ( ~ spl8_809
    | spl8_196
    | ~ spl8_116
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43327,f18910,f1211,f5268,f43818])).

fof(f5268,plain,
    ( spl8_196
  <=> ! [X97] : ~ sP5(k1_xboole_0,k4_xboole_0(sK3,X97),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).

fof(f43327,plain,
    ( ! [X364] :
        ( ~ sP5(k1_xboole_0,k4_xboole_0(sK3,X364),sK1)
        | ~ sP5(sK1,sK2,sK2) )
    | ~ spl8_116
    | ~ spl8_632 ),
    inference(superposition,[],[f5184,f18911])).

fof(f5184,plain,
    ( ! [X45,X46,X44] :
        ( ~ sP5(k4_xboole_0(X46,X45),k4_xboole_0(sK3,X44),sK1)
        | ~ sP5(sK1,X45,X46) )
    | ~ spl8_116 ),
    inference(superposition,[],[f337,f5148])).

fof(f5148,plain,
    ( ! [X1] : k4_xboole_0(sK1,k4_xboole_0(sK3,X1)) = sK1
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f5125])).

fof(f5125,plain,
    ( ! [X1] :
        ( k4_xboole_0(sK1,k4_xboole_0(sK3,X1)) = sK1
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X1)) = sK1 )
    | ~ spl8_116 ),
    inference(resolution,[],[f4324,f422])).

fof(f422,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f282])).

fof(f4324,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,k4_xboole_0(sK3,X0),sK1),sK1)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = sK1 )
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f4322])).

fof(f4322,plain,
    ( ! [X0] :
        ( k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = sK1
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK3,X0),sK1),sK1)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = sK1
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK3,X0),sK1),sK1) )
    | ~ spl8_116 ),
    inference(resolution,[],[f4314,f1716])).

fof(f1716,plain,(
    ! [X23,X21,X22,X20] :
      ( r2_hidden(sK4(X20,k4_xboole_0(X21,X22),X23),X21)
      | ~ r2_hidden(sK4(X20,k4_xboole_0(X21,X22),X23),X20)
      | k4_xboole_0(X20,k4_xboole_0(X21,X22)) = X23
      | ~ r2_hidden(sK4(X20,k4_xboole_0(X21,X22),X23),X23) ) ),
    inference(resolution,[],[f431,f38])).

fof(f431,plain,(
    ! [X6,X8,X7,X9] :
      ( sP5(sK4(X6,k4_xboole_0(X7,X8),X9),X8,X7)
      | ~ r2_hidden(sK4(X6,k4_xboole_0(X7,X8),X9),X9)
      | ~ r2_hidden(sK4(X6,k4_xboole_0(X7,X8),X9),X6)
      | k4_xboole_0(X6,k4_xboole_0(X7,X8)) = X9 ) ),
    inference(resolution,[],[f287,f59])).

fof(f4314,plain,
    ( ! [X18] :
        ( ~ r2_hidden(sK4(sK1,X18,sK1),sK3)
        | k4_xboole_0(sK1,X18) = sK1 )
    | ~ spl8_116 ),
    inference(resolution,[],[f2778,f3967])).

fof(f3967,plain,
    ( ! [X0,X1] :
        ( ~ sP5(X0,X1,sK1)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_116 ),
    inference(resolution,[],[f3916,f60])).

fof(f3916,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,k4_xboole_0(sK1,X7))
        | ~ r2_hidden(X6,sK3) )
    | ~ spl8_116 ),
    inference(resolution,[],[f3706,f39])).

fof(f3706,plain,
    ( ! [X6,X7] :
        ( sP5(X7,k4_xboole_0(sK1,X6),sK3)
        | ~ r2_hidden(X7,sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f59,f3648])).

fof(f3648,plain,
    ( ! [X2] : k4_xboole_0(sK3,k4_xboole_0(sK1,X2)) = sK3
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f3627])).

fof(f3627,plain,
    ( ! [X2] :
        ( k4_xboole_0(sK3,k4_xboole_0(sK1,X2)) = sK3
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X2)) = sK3 )
    | ~ spl8_116 ),
    inference(resolution,[],[f3594,f422])).

fof(f3594,plain,
    ( ! [X41] :
        ( ~ r2_hidden(sK4(sK3,k4_xboole_0(sK1,X41),sK3),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X41)) = sK3 )
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f3566])).

fof(f3566,plain,
    ( ! [X41] :
        ( ~ r2_hidden(sK4(sK3,k4_xboole_0(sK1,X41),sK3),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X41)) = sK3
        | ~ r2_hidden(sK4(sK3,k4_xboole_0(sK1,X41),sK3),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X41)) = sK3 )
    | ~ spl8_116 ),
    inference(resolution,[],[f1716,f2575])).

fof(f2575,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK3,X1,sK3),sK1)
        | k4_xboole_0(sK3,X1) = sK3 )
    | ~ spl8_116 ),
    inference(resolution,[],[f2541,f422])).

fof(f2778,plain,(
    ! [X2,X3] :
      ( sP5(sK4(X2,X3,X2),k1_xboole_0,X2)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(forward_demodulation,[],[f2763,f51])).

fof(f2763,plain,(
    ! [X2,X3] :
      ( sP5(sK4(X2,X3,X2),k1_xboole_0,X2)
      | k4_xboole_0(X2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3) ) ),
    inference(superposition,[],[f614,f51])).

fof(f614,plain,(
    ! [X6,X8,X7] :
      ( sP5(sK4(k4_xboole_0(X6,X7),X8,k4_xboole_0(X6,X7)),X7,X6)
      | k4_xboole_0(X6,X7) = k4_xboole_0(k4_xboole_0(X6,X7),X8) ) ),
    inference(resolution,[],[f422,f59])).

fof(f43820,plain,
    ( ~ spl8_809
    | ~ spl8_171
    | ~ spl8_106
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43317,f18910,f1040,f4522,f43818])).

fof(f4522,plain,
    ( spl8_171
  <=> ~ sP5(k1_xboole_0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_171])])).

fof(f1040,plain,
    ( spl8_106
  <=> k4_xboole_0(sK1,sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f43317,plain,
    ( ~ sP5(k1_xboole_0,sK3,sK1)
    | ~ sP5(sK1,sK2,sK2)
    | ~ spl8_106
    | ~ spl8_632 ),
    inference(superposition,[],[f4442,f18911])).

fof(f4442,plain,
    ( ! [X19,X20] :
        ( ~ sP5(k4_xboole_0(X20,X19),sK3,sK1)
        | ~ sP5(sK1,X19,X20) )
    | ~ spl8_106 ),
    inference(superposition,[],[f337,f1041])).

fof(f1041,plain,
    ( k4_xboole_0(sK1,sK3) = sK1
    | ~ spl8_106 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f43779,plain,
    ( spl8_806
    | spl8_562
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43775,f18910,f15774,f43777])).

fof(f43777,plain,
    ( spl8_806
  <=> ! [X327] :
        ( ~ r2_hidden(sK2,sK6(X327,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X327)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_806])])).

fof(f15774,plain,
    ( spl8_562
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_562])])).

fof(f43775,plain,
    ( ! [X327] :
        ( r1_tarski(sK2,k1_xboole_0)
        | ~ r2_hidden(sK2,sK6(X327,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X327)) )
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f43298,f18911])).

fof(f43298,plain,
    ( ! [X327] :
        ( ~ r2_hidden(sK2,sK6(X327,sK2,k1_xboole_0))
        | r1_tarski(sK2,k4_xboole_0(sK2,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X327)) )
    | ~ spl8_632 ),
    inference(superposition,[],[f3468,f18911])).

fof(f3468,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK6(X2,X0,k4_xboole_0(X0,X1)))
      | r1_tarski(X0,k4_xboole_0(X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(global_subsumption,[],[f245,f3467])).

fof(f3467,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X1,sK6(X2,X0,k4_xboole_0(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f3453])).

fof(f3453,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X1,sK6(X2,X0,k4_xboole_0(X0,X1)))
      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f1666,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1666,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(sK6(X13,X10,k4_xboole_0(X11,X12)),X11)
      | ~ m1_subset_1(k4_xboole_0(X11,X12),k1_zfmisc_1(X13))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X13))
      | r1_tarski(X10,k4_xboole_0(X11,X12))
      | ~ r2_hidden(X12,sK6(X13,X10,k4_xboole_0(X11,X12))) ) ),
    inference(resolution,[],[f466,f57])).

fof(f466,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X1,X0,k4_xboole_0(X2,X3)),X3)
      | r1_tarski(X0,k4_xboole_0(X2,X3))
      | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK6(X1,X0,k4_xboole_0(X2,X3)),X2) ) ),
    inference(resolution,[],[f274,f37])).

fof(f274,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ sP5(sK6(X4,X5,k4_xboole_0(X2,X3)),X3,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | r1_tarski(X5,k4_xboole_0(X2,X3))
      | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f56,f60])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f52,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',redefinition_k7_subset_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',dt_k7_subset_1)).

fof(f43656,plain,
    ( ~ spl8_805
    | spl8_192
    | ~ spl8_106
    | ~ spl8_632 ),
    inference(avatar_split_clause,[],[f43649,f18910,f1040,f5043,f43654])).

fof(f43654,plain,
    ( spl8_805
  <=> ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_805])])).

fof(f5043,plain,
    ( spl8_192
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_192])])).

fof(f43649,plain,
    ( k1_xboole_0 = sK1
    | ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK2,sK2)
    | ~ spl8_106
    | ~ spl8_632 ),
    inference(forward_demodulation,[],[f43198,f18911])).

fof(f43198,plain,
    ( ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK2,sK2)
    | k4_xboole_0(sK2,sK2) = sK1
    | ~ spl8_106
    | ~ spl8_632 ),
    inference(superposition,[],[f40750,f18911])).

fof(f40750,plain,
    ( ! [X7] :
        ( ~ sP5(sK4(sK1,sK3,k4_xboole_0(X7,X7)),X7,X7)
        | k4_xboole_0(X7,X7) = sK1 )
    | ~ spl8_106 ),
    inference(resolution,[],[f16511,f60])).

fof(f16511,plain,
    ( ! [X376] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X376,X376)),k4_xboole_0(X376,X376))
        | k4_xboole_0(X376,X376) = sK1 )
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f16510])).

fof(f16510,plain,
    ( ! [X376] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X376,X376)),k4_xboole_0(X376,X376))
        | k4_xboole_0(X376,X376) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X376,X376)),k4_xboole_0(X376,X376)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f16509,f6914])).

fof(f6914,plain,(
    ! [X6] : k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6)) ),
    inference(duplicate_literal_removal,[],[f6886])).

fof(f6886,plain,(
    ! [X6] :
      ( k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6))
      | k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6)) ) ),
    inference(resolution,[],[f2933,f422])).

fof(f16509,plain,
    ( ! [X376] :
        ( k4_xboole_0(X376,X376) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X376,X376)),k4_xboole_0(X376,X376))
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(k4_xboole_0(X376,X376),k4_xboole_0(X376,X376))),k4_xboole_0(X376,X376)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f16319,f6914])).

fof(f16319,plain,
    ( ! [X376] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X376,X376)),k4_xboole_0(X376,X376))
        | k4_xboole_0(k4_xboole_0(X376,X376),k4_xboole_0(X376,X376)) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(k4_xboole_0(X376,X376),k4_xboole_0(X376,X376))),k4_xboole_0(X376,X376)) )
    | ~ spl8_106 ),
    inference(superposition,[],[f5014,f6914])).

fof(f5014,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))
        | k4_xboole_0(X4,X5) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),X5) )
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f5013])).

fof(f5013,plain,
    ( ! [X4,X5] :
        ( k4_xboole_0(X4,X5) = sK1
        | k4_xboole_0(X4,X5) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),X5) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f5006,f1041])).

fof(f5006,plain,
    ( ! [X4,X5] :
        ( k4_xboole_0(X4,X5) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),k4_xboole_0(X4,X5))
        | k4_xboole_0(sK1,sK3) = k4_xboole_0(X4,X5)
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(X4,X5)),X5) )
    | ~ spl8_106 ),
    inference(resolution,[],[f4736,f1513])).

fof(f4736,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(sK1,sK3,X8),sK1)
        | sK1 = X8
        | ~ r2_hidden(sK4(sK1,sK3,X8),X8) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4722,f1041])).

fof(f4722,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(sK1,sK3,X8),sK1)
        | ~ r2_hidden(sK4(sK1,sK3,X8),X8)
        | k4_xboole_0(sK1,sK3) = X8 )
    | ~ spl8_106 ),
    inference(resolution,[],[f4435,f43])).

fof(f4435,plain,
    ( ! [X10] :
        ( sP5(X10,sK3,sK1)
        | ~ r2_hidden(X10,sK1) )
    | ~ spl8_106 ),
    inference(superposition,[],[f59,f1041])).

fof(f43013,plain,
    ( ~ spl8_803
    | ~ spl8_632
    | spl8_769 ),
    inference(avatar_split_clause,[],[f42975,f30803,f18910,f43011])).

fof(f43011,plain,
    ( spl8_803
  <=> ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_803])])).

fof(f30803,plain,
    ( spl8_769
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_769])])).

fof(f42975,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),sK2)
    | ~ spl8_632
    | ~ spl8_769 ),
    inference(backward_demodulation,[],[f18911,f30804])).

fof(f30804,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK2)
    | ~ spl8_769 ),
    inference(avatar_component_clause,[],[f30803])).

fof(f43006,plain,
    ( ~ spl8_801
    | ~ spl8_632
    | spl8_747 ),
    inference(avatar_split_clause,[],[f42974,f30395,f18910,f43004])).

fof(f43004,plain,
    ( spl8_801
  <=> ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_801])])).

fof(f30395,plain,
    ( spl8_747
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_747])])).

fof(f42974,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_632
    | ~ spl8_747 ),
    inference(backward_demodulation,[],[f18911,f30396])).

fof(f30396,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),k1_xboole_0)
    | ~ spl8_747 ),
    inference(avatar_component_clause,[],[f30395])).

fof(f42999,plain,
    ( ~ spl8_799
    | ~ spl8_632
    | spl8_743 ),
    inference(avatar_split_clause,[],[f42973,f30388,f18910,f42997])).

fof(f42997,plain,
    ( spl8_799
  <=> ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_799])])).

fof(f30388,plain,
    ( spl8_743
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_743])])).

fof(f42973,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k1_xboole_0),sK1)
    | ~ spl8_632
    | ~ spl8_743 ),
    inference(backward_demodulation,[],[f18911,f30389])).

fof(f30389,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1)
    | ~ spl8_743 ),
    inference(avatar_component_clause,[],[f30388])).

fof(f42964,plain,
    ( spl8_632
    | spl8_796
    | ~ spl8_794 ),
    inference(avatar_split_clause,[],[f42792,f42591,f42962,f18910])).

fof(f42962,plain,
    ( spl8_796
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_796])])).

fof(f42591,plain,
    ( spl8_794
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_794])])).

fof(f42792,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | k4_xboole_0(sK2,sK2) = k1_xboole_0 )
    | ~ spl8_794 ),
    inference(resolution,[],[f42592,f6460])).

fof(f6460,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X2,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k4_xboole_0(X2,X2) = X0 ) ),
    inference(resolution,[],[f1957,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',d10_xboole_0)).

fof(f1957,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k4_xboole_0(X6,X6),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f1457,f245])).

fof(f1457,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f1440])).

fof(f1440,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(X0,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f444,f443])).

fof(f443,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK6(X6,k4_xboole_0(X4,X5),X7),X5)
      | r1_tarski(k4_xboole_0(X4,X5),X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ m1_subset_1(k4_xboole_0(X4,X5),k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f269,f39])).

fof(f269,plain,(
    ! [X10,X8,X11,X9] :
      ( sP5(sK6(X9,k4_xboole_0(X10,X11),X8),X11,X10)
      | ~ m1_subset_1(k4_xboole_0(X10,X11),k1_zfmisc_1(X9))
      | r1_tarski(k4_xboole_0(X10,X11),X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f55,f59])).

fof(f444,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK6(X10,k4_xboole_0(X8,X9),X11),X8)
      | r1_tarski(k4_xboole_0(X8,X9),X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ m1_subset_1(k4_xboole_0(X8,X9),k1_zfmisc_1(X10)) ) ),
    inference(resolution,[],[f269,f38])).

fof(f42592,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK2))
    | ~ spl8_794 ),
    inference(avatar_component_clause,[],[f42591])).

fof(f42960,plain,
    ( spl8_632
    | ~ spl8_793
    | ~ spl8_794 ),
    inference(avatar_split_clause,[],[f42793,f42591,f42584,f18910])).

fof(f42584,plain,
    ( spl8_793
  <=> ~ r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_793])])).

fof(f42793,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0)
    | k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ spl8_794 ),
    inference(resolution,[],[f42592,f48])).

fof(f42959,plain,
    ( ~ spl8_83
    | ~ spl8_2
    | spl8_793 ),
    inference(avatar_split_clause,[],[f42958,f42584,f74,f698])).

fof(f698,plain,
    ( spl8_83
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f74,plain,
    ( spl8_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f42958,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_2
    | ~ spl8_793 ),
    inference(resolution,[],[f42635,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f42635,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) )
    | ~ spl8_793 ),
    inference(resolution,[],[f42585,f1957])).

fof(f42585,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0)
    | ~ spl8_793 ),
    inference(avatar_component_clause,[],[f42584])).

fof(f42593,plain,
    ( spl8_794
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_784 ),
    inference(avatar_split_clause,[],[f42575,f42005,f6336,f6161,f42591])).

fof(f6336,plain,
    ( spl8_234
  <=> ! [X0] :
        ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_234])])).

fof(f42005,plain,
    ( spl8_784
  <=> m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_784])])).

fof(f42575,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK2))
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_784 ),
    inference(resolution,[],[f42006,f15197])).

fof(f15197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(backward_demodulation,[],[f6162,f6337])).

fof(f6337,plain,
    ( ! [X0] :
        ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl8_234 ),
    inference(avatar_component_clause,[],[f6336])).

fof(f42006,plain,
    ( m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_784 ),
    inference(avatar_component_clause,[],[f42005])).

fof(f42586,plain,
    ( ~ spl8_793
    | spl8_632
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_784 ),
    inference(avatar_split_clause,[],[f42574,f42005,f6336,f6161,f18910,f42584])).

fof(f42574,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_784 ),
    inference(resolution,[],[f42006,f15295])).

fof(f15295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(forward_demodulation,[],[f15198,f6162])).

fof(f15198,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(backward_demodulation,[],[f6162,f6400])).

fof(f6400,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = X0 )
    | ~ spl8_234 ),
    inference(resolution,[],[f6337,f48])).

fof(f42383,plain,
    ( spl8_788
    | ~ spl8_791
    | ~ spl8_786 ),
    inference(avatar_split_clause,[],[f42367,f42014,f42381,f42375])).

fof(f42375,plain,
    ( spl8_788
  <=> k4_xboole_0(sK2,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_788])])).

fof(f42381,plain,
    ( spl8_791
  <=> ~ r1_tarski(sK1,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_791])])).

fof(f42014,plain,
    ( spl8_786
  <=> r1_tarski(k4_xboole_0(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_786])])).

fof(f42367,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK2,sK2))
    | k4_xboole_0(sK2,sK2) = sK1
    | ~ spl8_786 ),
    inference(resolution,[],[f42015,f48])).

fof(f42015,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK2),sK1)
    | ~ spl8_786 ),
    inference(avatar_component_clause,[],[f42014])).

fof(f42241,plain,
    ( ~ spl8_3
    | spl8_785 ),
    inference(avatar_split_clause,[],[f42237,f42008,f71])).

fof(f71,plain,
    ( spl8_3
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f42008,plain,
    ( spl8_785
  <=> ~ m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_785])])).

fof(f42237,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_785 ),
    inference(resolution,[],[f42009,f245])).

fof(f42009,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_785 ),
    inference(avatar_component_clause,[],[f42008])).

fof(f42016,plain,
    ( ~ spl8_785
    | spl8_786 ),
    inference(avatar_split_clause,[],[f42000,f42014,f42008])).

fof(f42000,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK2),sK1)
    | ~ m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f41643,f8192])).

fof(f8192,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f8150])).

fof(f8150,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)
      | k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f2756,f2755])).

fof(f2755,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X12,X13),X14,k4_xboole_0(X12,X13)),X13)
      | k4_xboole_0(X12,X13) = k4_xboole_0(k4_xboole_0(X12,X13),X14) ) ),
    inference(resolution,[],[f614,f39])).

fof(f2756,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(sK4(k4_xboole_0(X15,X16),X17,k4_xboole_0(X15,X16)),X15)
      | k4_xboole_0(X15,X16) = k4_xboole_0(k4_xboole_0(X15,X16),X17) ) ),
    inference(resolution,[],[f614,f38])).

fof(f41643,plain,(
    ! [X2] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X2),sK3),sK1)
      | ~ m1_subset_1(k4_xboole_0(sK2,X2),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f18168,f245])).

fof(f18168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK1) ) ),
    inference(global_subsumption,[],[f36,f18167])).

fof(f18167,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f18158])).

fof(f18158,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK1) ) ),
    inference(resolution,[],[f10711,f54])).

fof(f10711,plain,(
    ! [X68,X67] :
      ( ~ m1_subset_1(sK6(X68,k4_xboole_0(k4_xboole_0(sK2,X67),sK3),sK1),sK0)
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X68))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),k1_zfmisc_1(X68)) ) ),
    inference(duplicate_literal_removal,[],[f10674])).

fof(f10674,plain,(
    ! [X68,X67] :
      ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),k1_zfmisc_1(X68))
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X68))
      | ~ m1_subset_1(sK6(X68,k4_xboole_0(k4_xboole_0(sK2,X67),sK3),sK1),sK0)
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X68))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK2,X67),sK3),k1_zfmisc_1(X68)) ) ),
    inference(resolution,[],[f3392,f5940])).

fof(f5940,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK6(X7,k4_xboole_0(X8,sK3),sK1),sK2)
      | ~ m1_subset_1(sK6(X7,k4_xboole_0(X8,sK3),sK1),sK0)
      | r1_tarski(k4_xboole_0(X8,sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X7))
      | ~ m1_subset_1(k4_xboole_0(X8,sK3),k1_zfmisc_1(X7)) ) ),
    inference(duplicate_literal_removal,[],[f5924])).

fof(f5924,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(sK6(X7,k4_xboole_0(X8,sK3),sK1),sK0)
      | ~ r2_hidden(sK6(X7,k4_xboole_0(X8,sK3),sK1),sK2)
      | r1_tarski(k4_xboole_0(X8,sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X7))
      | ~ m1_subset_1(k4_xboole_0(X8,sK3),k1_zfmisc_1(X7))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X7))
      | ~ m1_subset_1(k4_xboole_0(X8,sK3),k1_zfmisc_1(X7))
      | r1_tarski(k4_xboole_0(X8,sK3),sK1) ) ),
    inference(resolution,[],[f4611,f56])).

fof(f4611,plain,(
    ! [X45,X43,X44] :
      ( r2_hidden(sK6(X43,k4_xboole_0(X44,sK3),X45),sK1)
      | ~ m1_subset_1(sK6(X43,k4_xboole_0(X44,sK3),X45),sK0)
      | ~ r2_hidden(sK6(X43,k4_xboole_0(X44,sK3),X45),sK2)
      | r1_tarski(k4_xboole_0(X44,sK3),X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | ~ m1_subset_1(k4_xboole_0(X44,sK3),k1_zfmisc_1(X43)) ) ),
    inference(resolution,[],[f32,f443])).

fof(f3392,plain,(
    ! [X28,X26,X29,X27,X25] :
      ( r2_hidden(sK6(X26,k4_xboole_0(k4_xboole_0(X27,X28),X29),X25),X27)
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(X27,X28),X29),k1_zfmisc_1(X26))
      | r1_tarski(k4_xboole_0(k4_xboole_0(X27,X28),X29),X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26)) ) ),
    inference(resolution,[],[f1445,f38])).

fof(f1445,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( sP5(sK6(X22,k4_xboole_0(k4_xboole_0(X18,X19),X20),X21),X19,X18)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(X18,X19),X20),k1_zfmisc_1(X22))
      | r1_tarski(k4_xboole_0(k4_xboole_0(X18,X19),X20),X21) ) ),
    inference(resolution,[],[f444,f59])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f41229,plain,
    ( ~ spl8_783
    | spl8_192
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f41228,f1040,f5043,f41222])).

fof(f41222,plain,
    ( spl8_783
  <=> ~ sP5(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_783])])).

fof(f41228,plain,
    ( k1_xboole_0 = sK1
    | ~ sP5(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f41208,f50])).

fof(f41208,plain,
    ( ~ sP5(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = sK1
    | ~ spl8_106 ),
    inference(superposition,[],[f40750,f50])).

fof(f41224,plain,
    ( ~ spl8_783
    | spl8_192
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f41217,f1040,f5043,f41222])).

fof(f41217,plain,
    ( k1_xboole_0 = sK1
    | ~ sP5(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f41201,f50])).

fof(f41201,plain,
    ( ~ sP5(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = sK1
    | ~ spl8_106 ),
    inference(superposition,[],[f40750,f51])).

fof(f40740,plain,
    ( spl8_780
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f40736,f1211,f649,f40738])).

fof(f40738,plain,
    ( spl8_780
  <=> ! [X51,X53,X52] :
        ( ~ r2_hidden(sK3,X52)
        | r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),k4_xboole_0(sK1,X51))
        | ~ r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_780])])).

fof(f40736,plain,
    ( ! [X52,X53,X51] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK3,X52)
        | ~ r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),k4_xboole_0(sK1,X51)) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40735,f3648])).

fof(f40735,plain,
    ( ! [X52,X53,X51] :
        ( ~ r2_hidden(sK3,X52)
        | ~ r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),k4_xboole_0(sK1,X51))
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X51)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40734,f3648])).

fof(f40734,plain,
    ( ! [X52,X53,X51] :
        ( ~ r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),k4_xboole_0(sK1,X51))
        | ~ r2_hidden(k4_xboole_0(sK3,k4_xboole_0(sK1,X51)),X52)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X51)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40671,f3648])).

fof(f40671,plain,
    ( ! [X52,X53,X51] :
        ( r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,sK3)),k4_xboole_0(sK1,X51))
        | ~ r2_hidden(k4_xboole_0(X52,sK4(k1_xboole_0,X53,k4_xboole_0(sK3,k4_xboole_0(sK1,X51)))),sK3)
        | ~ r2_hidden(k4_xboole_0(sK3,k4_xboole_0(sK1,X51)),X52)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X51)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8768,f3648])).

fof(f8768,plain,(
    ! [X78,X76,X79,X77] :
      ( r2_hidden(k4_xboole_0(X76,sK4(k1_xboole_0,X77,k4_xboole_0(X78,X79))),X79)
      | ~ r2_hidden(k4_xboole_0(X76,sK4(k1_xboole_0,X77,k4_xboole_0(X78,X79))),X78)
      | ~ r2_hidden(k4_xboole_0(X78,X79),X76)
      | k4_xboole_0(X78,X79) = k1_xboole_0 ) ),
    inference(resolution,[],[f2107,f1931])).

fof(f1931,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK4(k1_xboole_0,X12,X11))
      | k1_xboole_0 = X11 ) ),
    inference(duplicate_literal_removal,[],[f1930])).

fof(f1930,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 = X11
      | ~ r2_hidden(X11,sK4(k1_xboole_0,X12,X11))
      | k1_xboole_0 = X11 ) ),
    inference(forward_demodulation,[],[f1928,f50])).

fof(f1928,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK4(k1_xboole_0,X12,X11))
      | k1_xboole_0 = X11
      | k4_xboole_0(k1_xboole_0,X12) = X11 ) ),
    inference(duplicate_literal_removal,[],[f1919])).

fof(f1919,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK4(k1_xboole_0,X12,X11))
      | k1_xboole_0 = X11
      | k4_xboole_0(k1_xboole_0,X12) = X11
      | ~ r2_hidden(X11,sK4(k1_xboole_0,X12,X11)) ) ),
    inference(resolution,[],[f1242,f416])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(resolution,[],[f282,f57])).

fof(f1242,plain,(
    ! [X28,X26,X27] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X26,X27),X28)
      | ~ r2_hidden(X27,sK4(k1_xboole_0,X26,X27))
      | k1_xboole_0 = X27 ) ),
    inference(forward_demodulation,[],[f1233,f50])).

fof(f1233,plain,(
    ! [X28,X26,X27] :
      ( k4_xboole_0(k1_xboole_0,X26) = X27
      | ~ r2_hidden(X27,sK4(k1_xboole_0,X26,X27))
      | ~ r2_hidden(sK4(k1_xboole_0,X26,X27),X28) ) ),
    inference(resolution,[],[f416,f270])).

fof(f40733,plain,
    ( spl8_778
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f40729,f1211,f649,f40731])).

fof(f40731,plain,
    ( spl8_778
  <=> ! [X49,X50] :
        ( ~ r2_hidden(sK3,X49)
        | r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_778])])).

fof(f40729,plain,
    ( ! [X50,X49] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK3,X49)
        | ~ r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK1) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40728,f1212])).

fof(f40728,plain,
    ( ! [X50,X49] :
        ( ~ r2_hidden(sK3,X49)
        | ~ r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK1)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40727,f1212])).

fof(f40727,plain,
    ( ! [X50,X49] :
        ( ~ r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(sK3,sK1),X49)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40670,f1212])).

fof(f40670,plain,
    ( ! [X50,X49] :
        ( r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(X49,sK4(k1_xboole_0,X50,k4_xboole_0(sK3,sK1))),sK3)
        | ~ r2_hidden(k4_xboole_0(sK3,sK1),X49)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8768,f1212])).

fof(f40726,plain,
    ( spl8_776
    | spl8_192
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f40722,f1040,f5043,f40724])).

fof(f40724,plain,
    ( spl8_776
  <=> ! [X48,X47] :
        ( ~ r2_hidden(sK1,X47)
        | r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_776])])).

fof(f40722,plain,
    ( ! [X47,X48] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(sK1,X47)
        | ~ r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK3) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f40721,f1041])).

fof(f40721,plain,
    ( ! [X47,X48] :
        ( ~ r2_hidden(sK1,X47)
        | ~ r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK3)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0 )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f40720,f1041])).

fof(f40720,plain,
    ( ! [X47,X48] :
        ( ~ r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(sK1,sK3),X47)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0 )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f40669,f1041])).

fof(f40669,plain,
    ( ! [X47,X48] :
        ( r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(X47,sK4(k1_xboole_0,X48,k4_xboole_0(sK1,sK3))),sK1)
        | ~ r2_hidden(k4_xboole_0(sK1,sK3),X47)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0 )
    | ~ spl8_106 ),
    inference(superposition,[],[f8768,f1041])).

fof(f40719,plain,
    ( spl8_774
    | spl8_192
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f40715,f1211,f5043,f40717])).

fof(f40717,plain,
    ( spl8_774
  <=> ! [X40,X42,X41] :
        ( ~ r2_hidden(sK1,X41)
        | r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),k4_xboole_0(sK3,X40))
        | ~ r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_774])])).

fof(f40715,plain,
    ( ! [X41,X42,X40] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(sK1,X41)
        | ~ r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),k4_xboole_0(sK3,X40)) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40714,f5148])).

fof(f40714,plain,
    ( ! [X41,X42,X40] :
        ( ~ r2_hidden(sK1,X41)
        | ~ r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),k4_xboole_0(sK3,X40))
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X40)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40713,f5148])).

fof(f40713,plain,
    ( ! [X41,X42,X40] :
        ( ~ r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),k4_xboole_0(sK3,X40))
        | ~ r2_hidden(k4_xboole_0(sK1,k4_xboole_0(sK3,X40)),X41)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X40)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f40666,f5148])).

fof(f40666,plain,
    ( ! [X41,X42,X40] :
        ( r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,sK1)),k4_xboole_0(sK3,X40))
        | ~ r2_hidden(k4_xboole_0(X41,sK4(k1_xboole_0,X42,k4_xboole_0(sK1,k4_xboole_0(sK3,X40)))),sK1)
        | ~ r2_hidden(k4_xboole_0(sK1,k4_xboole_0(sK3,X40)),X41)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X40)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8768,f5148])).

fof(f36781,plain,
    ( spl8_34
    | spl8_772
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f36764,f1211,f36779,f192])).

fof(f192,plain,
    ( spl8_34
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f36779,plain,
    ( spl8_772
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_xboole_0(X2,sK1),X2)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK3),X2)
        | ~ r2_hidden(k4_xboole_0(X2,sK1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_772])])).

fof(f36764,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_xboole_0(X2,sK1),X2)
        | ~ r2_hidden(k4_xboole_0(X2,sK1),X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK3),X2)
        | r2_hidden(sK1,sK3)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl8_116 ),
    inference(resolution,[],[f36648,f8745])).

fof(f8745,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_xboole_0(X0,X1),X3)
      | ~ r2_hidden(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(k4_xboole_0(X2,X3),X0)
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f2107,f2119])).

fof(f36648,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(X1,sK1),sK3)
        | ~ r2_hidden(k4_xboole_0(X1,sK1),X1) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f36629,f5148])).

fof(f36629,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_xboole_0(X1,sK1),sK3)
        | ~ r2_hidden(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK3,X0))),X1) )
    | ~ spl8_116 ),
    inference(superposition,[],[f14796,f5148])).

fof(f14796,plain,
    ( ! [X21,X20] :
        ( ~ r2_hidden(k4_xboole_0(X20,k4_xboole_0(sK1,X21)),sK3)
        | ~ r2_hidden(k4_xboole_0(X20,k4_xboole_0(sK1,X21)),X20) )
    | ~ spl8_116 ),
    inference(resolution,[],[f8789,f3916])).

fof(f35209,plain,
    ( ~ spl8_771
    | spl8_126
    | ~ spl8_53
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f35202,f16655,f6161,f306,f1597,f35207])).

fof(f35207,plain,
    ( spl8_771
  <=> ~ sP5(sK2,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_771])])).

fof(f35202,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ sP5(sK2,sK1,sK1)
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f35183,f16656])).

fof(f35183,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k4_xboole_0(sK1,sK1),sK1)
    | ~ sP5(sK2,sK1,sK1)
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(superposition,[],[f18546,f16656])).

fof(f35200,plain,
    ( spl8_50
    | spl8_126
    | ~ spl8_53
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f35199,f6161,f306,f1597,f300])).

fof(f300,plain,
    ( spl8_50
  <=> ! [X0] : ~ sP5(sK2,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f35199,plain,
    ( ! [X17] :
        ( ~ r2_hidden(k1_xboole_0,sK1)
        | r2_hidden(k1_xboole_0,k1_xboole_0)
        | ~ sP5(sK2,X17,k1_xboole_0) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f35181,f50])).

fof(f35181,plain,
    ( ! [X17] :
        ( r2_hidden(k1_xboole_0,k1_xboole_0)
        | ~ r2_hidden(k4_xboole_0(k1_xboole_0,X17),sK1)
        | ~ sP5(sK2,X17,k1_xboole_0) )
    | ~ spl8_216 ),
    inference(superposition,[],[f18546,f50])).

fof(f30805,plain,
    ( ~ spl8_767
    | ~ spl8_751
    | ~ spl8_769
    | spl8_743 ),
    inference(avatar_split_clause,[],[f30787,f30388,f30803,f30412,f30797])).

fof(f30797,plain,
    ( spl8_767
  <=> ~ r2_hidden(sK3,sK4(sK1,sK1,k4_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_767])])).

fof(f30412,plain,
    ( spl8_751
  <=> ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_751])])).

fof(f30787,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK2)
    | ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK1,k4_xboole_0(sK2,sK2)))
    | ~ spl8_743 ),
    inference(resolution,[],[f30389,f119])).

fof(f30792,plain,
    ( ~ spl8_747
    | ~ spl8_216
    | spl8_743 ),
    inference(avatar_split_clause,[],[f30786,f30388,f6161,f30395])).

fof(f30786,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_743 ),
    inference(resolution,[],[f30389,f17168])).

fof(f30599,plain,
    ( ~ spl8_763
    | ~ spl8_216
    | spl8_753 ),
    inference(avatar_split_clause,[],[f30593,f30416,f6161,f30515])).

fof(f30515,plain,
    ( spl8_763
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_763])])).

fof(f30416,plain,
    ( spl8_753
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_753])])).

fof(f30593,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_753 ),
    inference(resolution,[],[f30417,f17168])).

fof(f30417,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1)
    | ~ spl8_753 ),
    inference(avatar_component_clause,[],[f30416])).

fof(f30528,plain,
    ( ~ spl8_753
    | ~ spl8_755
    | spl8_757 ),
    inference(avatar_split_clause,[],[f30505,f30431,f30425,f30416])).

fof(f30425,plain,
    ( spl8_755
  <=> ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_755])])).

fof(f30431,plain,
    ( spl8_757
  <=> ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_757])])).

fof(f30505,plain,
    ( ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK0)
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1)
    | ~ spl8_757 ),
    inference(resolution,[],[f30432,f30])).

fof(f30432,plain,
    ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK2)
    | ~ spl8_757 ),
    inference(avatar_component_clause,[],[f30431])).

fof(f30527,plain,
    ( ~ spl8_753
    | ~ spl8_765
    | ~ spl8_216
    | spl8_757 ),
    inference(avatar_split_clause,[],[f30504,f30431,f6161,f30525,f30416])).

fof(f30525,plain,
    ( spl8_765
  <=> ~ r2_hidden(k1_xboole_0,sK4(sK1,sK1,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_765])])).

fof(f30504,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(sK1,sK1,k4_xboole_0(sK3,sK3)))
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1)
    | ~ spl8_216
    | ~ spl8_757 ),
    inference(resolution,[],[f30432,f15665])).

fof(f15665,plain,
    ( ! [X129] :
        ( r2_hidden(X129,sK2)
        | ~ r2_hidden(k1_xboole_0,X129)
        | ~ r2_hidden(X129,sK1) )
    | ~ spl8_216 ),
    inference(superposition,[],[f2119,f6162])).

fof(f30520,plain,
    ( ~ spl8_753
    | spl8_762
    | ~ spl8_216
    | spl8_757 ),
    inference(avatar_split_clause,[],[f30503,f30431,f6161,f30518,f30416])).

fof(f30518,plain,
    ( spl8_762
  <=> r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_762])])).

fof(f30503,plain,
    ( r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),k1_xboole_0)
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1)
    | ~ spl8_216
    | ~ spl8_757 ),
    inference(resolution,[],[f30432,f17614])).

fof(f30513,plain,
    ( ~ spl8_753
    | spl8_760
    | ~ spl8_436
    | spl8_757 ),
    inference(avatar_split_clause,[],[f30502,f30431,f13870,f30511,f30416])).

fof(f30511,plain,
    ( spl8_760
  <=> ! [X0] : ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_760])])).

fof(f13870,plain,
    ( spl8_436
  <=> ! [X32,X33] :
        ( ~ r2_hidden(X33,k4_xboole_0(sK1,sK2))
        | sP5(X33,X32,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_436])])).

fof(f30502,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),X0)
        | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1) )
    | ~ spl8_436
    | ~ spl8_757 ),
    inference(resolution,[],[f30432,f15055])).

fof(f15055,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,sK2)
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,sK1) )
    | ~ spl8_436 ),
    inference(resolution,[],[f14902,f37])).

fof(f14902,plain,
    ( ! [X0,X1] :
        ( ~ sP5(X0,sK2,sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f60])).

fof(f14713,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X6,X7) )
    | ~ spl8_436 ),
    inference(resolution,[],[f13871,f39])).

fof(f13871,plain,
    ( ! [X33,X32] :
        ( sP5(X33,X32,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X33,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_436 ),
    inference(avatar_component_clause,[],[f13870])).

fof(f30439,plain,
    ( spl8_752
    | ~ spl8_755
    | ~ spl8_757
    | spl8_758
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f30375,f16655,f1040,f30437,f30431,f30425,f30419])).

fof(f30419,plain,
    ( spl8_752
  <=> r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_752])])).

fof(f30437,plain,
    ( spl8_758
  <=> k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_758])])).

fof(f30375,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK2)
    | ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK0)
    | r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK3,sK3)),sK1)
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(resolution,[],[f28000,f32])).

fof(f28000,plain,
    ( ! [X78] :
        ( ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(X78,X78)),X78)
        | k4_xboole_0(X78,X78) = k1_xboole_0 )
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f27999,f1041])).

fof(f27999,plain,
    ( ! [X78] :
        ( k4_xboole_0(X78,X78) = k1_xboole_0
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK1,sK3),k4_xboole_0(X78,X78)),X78) )
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f27998,f16656])).

fof(f27998,plain,
    ( ! [X78] :
        ( k4_xboole_0(sK1,sK1) = k4_xboole_0(X78,X78)
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK1,sK3),k4_xboole_0(X78,X78)),X78) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f27940,f1041])).

fof(f27940,plain,
    ( ! [X78] :
        ( k4_xboole_0(X78,X78) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK1,sK3),k4_xboole_0(X78,X78)),X78) )
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f27909])).

fof(f27909,plain,
    ( ! [X78] :
        ( k4_xboole_0(X78,X78) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
        | ~ r2_hidden(sK4(sK1,k4_xboole_0(sK1,sK3),k4_xboole_0(X78,X78)),X78)
        | k4_xboole_0(X78,X78) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) )
    | ~ spl8_106 ),
    inference(resolution,[],[f6897,f11115])).

fof(f11115,plain,
    ( ! [X26,X24,X25] :
        ( sP5(sK4(sK1,X24,k4_xboole_0(X25,X26)),sK3,sK1)
        | ~ r2_hidden(sK4(sK1,X24,k4_xboole_0(X25,X26)),X26)
        | k4_xboole_0(sK1,X24) = k4_xboole_0(X25,X26) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f11114,f1041])).

fof(f11114,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK4(sK1,X24,k4_xboole_0(X25,X26)),X26)
        | sP5(sK4(sK1,X24,k4_xboole_0(X25,X26)),sK3,sK1)
        | k4_xboole_0(X25,X26) = k4_xboole_0(k4_xboole_0(sK1,sK3),X24) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f11060,f1041])).

fof(f11060,plain,
    ( ! [X26,X24,X25] :
        ( sP5(sK4(sK1,X24,k4_xboole_0(X25,X26)),sK3,sK1)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK3),X24,k4_xboole_0(X25,X26)),X26)
        | k4_xboole_0(X25,X26) = k4_xboole_0(k4_xboole_0(sK1,sK3),X24) )
    | ~ spl8_106 ),
    inference(superposition,[],[f2964,f1041])).

fof(f2964,plain,(
    ! [X45,X43,X41,X44,X42] :
      ( sP5(sK4(k4_xboole_0(X41,X42),X43,k4_xboole_0(X44,X45)),X42,X41)
      | ~ r2_hidden(sK4(k4_xboole_0(X41,X42),X43,k4_xboole_0(X44,X45)),X45)
      | k4_xboole_0(X44,X45) = k4_xboole_0(k4_xboole_0(X41,X42),X43) ) ),
    inference(resolution,[],[f1513,f59])).

fof(f6897,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ sP5(sK4(X28,k4_xboole_0(X29,X30),k4_xboole_0(X31,X31)),X30,X29)
      | k4_xboole_0(X31,X31) = k4_xboole_0(X28,k4_xboole_0(X29,X30)) ) ),
    inference(resolution,[],[f2933,f60])).

fof(f30414,plain,
    ( ~ spl8_743
    | ~ spl8_751
    | spl8_632
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f30374,f16655,f1040,f18910,f30412,f30388])).

fof(f30374,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ m1_subset_1(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK0)
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1)
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(resolution,[],[f28000,f30])).

fof(f30407,plain,
    ( ~ spl8_743
    | ~ spl8_749
    | spl8_632
    | ~ spl8_106
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f30373,f16655,f6161,f1040,f18910,f30405,f30388])).

fof(f30405,plain,
    ( spl8_749
  <=> ~ r2_hidden(k1_xboole_0,sK4(sK1,sK1,k4_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_749])])).

fof(f30373,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(sK1,sK1,k4_xboole_0(sK2,sK2)))
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1)
    | ~ spl8_106
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(resolution,[],[f28000,f15665])).

fof(f30400,plain,
    ( ~ spl8_743
    | spl8_746
    | spl8_632
    | ~ spl8_106
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f30372,f16655,f6161,f1040,f18910,f30398,f30388])).

fof(f30398,plain,
    ( spl8_746
  <=> r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_746])])).

fof(f30372,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),k1_xboole_0)
    | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1)
    | ~ spl8_106
    | ~ spl8_216
    | ~ spl8_592 ),
    inference(resolution,[],[f28000,f17614])).

fof(f30393,plain,
    ( ~ spl8_743
    | spl8_744
    | spl8_632
    | ~ spl8_106
    | ~ spl8_436
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f30371,f16655,f13870,f1040,f18910,f30391,f30388])).

fof(f30391,plain,
    ( spl8_744
  <=> ! [X6] : ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_744])])).

fof(f30371,plain,
    ( ! [X6] :
        ( k4_xboole_0(sK2,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),X6)
        | ~ r2_hidden(sK4(sK1,sK1,k4_xboole_0(sK2,sK2)),sK1) )
    | ~ spl8_106
    | ~ spl8_436
    | ~ spl8_592 ),
    inference(resolution,[],[f28000,f15055])).

fof(f28631,plain,
    ( spl8_740
    | spl8_582 ),
    inference(avatar_split_clause,[],[f28627,f16571,f28629])).

fof(f28629,plain,
    ( spl8_740
  <=> ! [X38] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
        | ~ r2_hidden(sK3,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
        | ~ m1_subset_1(sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_740])])).

fof(f16571,plain,
    ( spl8_582
  <=> k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_582])])).

fof(f28627,plain,(
    ! [X38] :
      ( k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
      | ~ m1_subset_1(sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f28626])).

fof(f28626,plain,(
    ! [X38] :
      ( k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ m1_subset_1(sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1))) ) ),
    inference(forward_demodulation,[],[f28593,f50])).

fof(f28593,plain,(
    ! [X38] :
      ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | k4_xboole_0(sK2,sK1) = k4_xboole_0(k1_xboole_0,X38)
      | ~ m1_subset_1(sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f28558])).

fof(f28558,plain,(
    ! [X38] :
      ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k4_xboole_0(k1_xboole_0,X38)
      | ~ m1_subset_1(sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(k1_xboole_0,X38,k4_xboole_0(sK2,sK1))) ) ),
    inference(resolution,[],[f8947,f9220])).

fof(f9220,plain,(
    ! [X45,X43,X44] :
      ( ~ r2_hidden(sK4(X43,X44,k4_xboole_0(X45,sK1)),sK2)
      | ~ r2_hidden(X43,sK4(X43,X44,k4_xboole_0(X45,sK1)))
      | k4_xboole_0(X45,sK1) = k4_xboole_0(X43,X44)
      | ~ m1_subset_1(sK4(X43,X44,k4_xboole_0(X45,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(X43,X44,k4_xboole_0(X45,sK1))) ) ),
    inference(resolution,[],[f2962,f119])).

fof(f2962,plain,(
    ! [X35,X33,X36,X34] :
      ( ~ r2_hidden(sK4(X33,X34,k4_xboole_0(X35,X36)),X36)
      | k4_xboole_0(X33,X34) = k4_xboole_0(X35,X36)
      | ~ r2_hidden(X33,sK4(X33,X34,k4_xboole_0(X35,X36))) ) ),
    inference(resolution,[],[f1513,f57])).

fof(f8947,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(sK4(k1_xboole_0,X18,k4_xboole_0(X16,X17)),X16)
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X18,k4_xboole_0(X16,X17)))
      | k4_xboole_0(X16,X17) = k1_xboole_0 ) ),
    inference(resolution,[],[f1889,f38])).

fof(f1889,plain,(
    ! [X14,X15,X16] :
      ( sP5(sK4(k1_xboole_0,X14,k4_xboole_0(X15,X16)),X16,X15)
      | k4_xboole_0(X15,X16) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X14,k4_xboole_0(X15,X16))) ) ),
    inference(resolution,[],[f428,f59])).

fof(f428,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3,X4),X4)
      | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X3,X4))
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f425,f50])).

fof(f425,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X3,X4))
      | r2_hidden(sK4(k1_xboole_0,X3,X4),X4)
      | k4_xboole_0(k1_xboole_0,X3) = X4 ) ),
    inference(resolution,[],[f341,f42])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1,X0,k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f230,f50])).

fof(f28623,plain,
    ( ~ spl8_735
    | ~ spl8_737
    | ~ spl8_739
    | spl8_582 ),
    inference(avatar_split_clause,[],[f28604,f16571,f28621,f28615,f28609])).

fof(f28609,plain,
    ( spl8_735
  <=> ~ m1_subset_1(sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_735])])).

fof(f28615,plain,
    ( spl8_737
  <=> ~ r2_hidden(sK3,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_737])])).

fof(f28621,plain,
    ( spl8_739
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_739])])).

fof(f28604,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | ~ r2_hidden(sK3,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f28603])).

fof(f28603,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK3,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(forward_demodulation,[],[f28535,f50])).

fof(f28535,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK3,sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK4(k1_xboole_0,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(resolution,[],[f8947,f8598])).

fof(f8598,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(X2,X3,k4_xboole_0(sK2,sK1)),X3)
      | ~ r2_hidden(sK3,sK4(X2,X3,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k4_xboole_0(X2,X3)
      | ~ m1_subset_1(sK4(X2,X3,k4_xboole_0(sK2,sK1)),sK0) ) ),
    inference(duplicate_literal_removal,[],[f8571])).

fof(f8571,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4(X2,X3,k4_xboole_0(sK2,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(X2,X3,k4_xboole_0(sK2,sK1)))
      | k4_xboole_0(sK2,sK1) = k4_xboole_0(X2,X3)
      | ~ r2_hidden(sK4(X2,X3,k4_xboole_0(sK2,sK1)),X3)
      | k4_xboole_0(sK2,sK1) = k4_xboole_0(X2,X3)
      | ~ r2_hidden(sK4(X2,X3,k4_xboole_0(sK2,sK1)),X3) ) ),
    inference(resolution,[],[f4676,f1480])).

fof(f4676,plain,(
    ! [X57,X58,X56] :
      ( ~ r2_hidden(sK4(X56,X57,k4_xboole_0(X58,sK1)),sK2)
      | ~ m1_subset_1(sK4(X56,X57,k4_xboole_0(X58,sK1)),sK0)
      | ~ r2_hidden(sK3,sK4(X56,X57,k4_xboole_0(X58,sK1)))
      | k4_xboole_0(X58,sK1) = k4_xboole_0(X56,X57)
      | ~ r2_hidden(sK4(X56,X57,k4_xboole_0(X58,sK1)),X57) ) ),
    inference(resolution,[],[f119,f1479])).

fof(f28417,plain,
    ( spl8_22
    | spl8_732
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f28355,f1211,f28415,f143])).

fof(f143,plain,
    ( spl8_22
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f28415,plain,
    ( spl8_732
  <=> ! [X44,X43] :
        ( ~ r2_hidden(k4_xboole_0(X43,sK3),X44)
        | ~ r2_hidden(k4_xboole_0(X43,sK3),X43)
        | ~ r2_hidden(sK3,X44)
        | ~ r2_hidden(k4_xboole_0(X44,sK1),X43) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_732])])).

fof(f28355,plain,
    ( ! [X43,X44] :
        ( ~ r2_hidden(k4_xboole_0(X43,sK3),X44)
        | ~ r2_hidden(k4_xboole_0(X44,sK1),X43)
        | r2_hidden(sK3,sK1)
        | ~ r2_hidden(sK3,X44)
        | ~ r2_hidden(k4_xboole_0(X43,sK3),X43) )
    | ~ spl8_116 ),
    inference(resolution,[],[f8745,f14801])).

fof(f14801,plain,
    ( ! [X28] :
        ( ~ r2_hidden(k4_xboole_0(X28,sK3),sK1)
        | ~ r2_hidden(k4_xboole_0(X28,sK3),X28) )
    | ~ spl8_116 ),
    inference(resolution,[],[f8789,f2541])).

fof(f26517,plain,
    ( spl8_562
    | spl8_730
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f26513,f16655,f26515,f15774])).

fof(f26515,plain,
    ( spl8_730
  <=> ! [X2] :
        ( ~ r2_hidden(sK1,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK6(X2,sK2,k1_xboole_0),sK0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_730])])).

fof(f26513,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK6(X2,sK2,k1_xboole_0))
        | r1_tarski(sK2,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK6(X2,sK2,k1_xboole_0),sK0)
        | ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) )
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f26512,f16656])).

fof(f26512,plain,
    ( ! [X2] :
        ( r1_tarski(sK2,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK6(X2,sK2,k1_xboole_0),sK0)
        | ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | ~ r2_hidden(sK1,sK6(X2,sK2,k4_xboole_0(sK1,sK1))) )
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f26511,f16656])).

fof(f26511,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK6(X2,sK2,k1_xboole_0),sK0)
        | ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | r1_tarski(sK2,k4_xboole_0(sK1,sK1))
        | ~ r2_hidden(sK1,sK6(X2,sK2,k4_xboole_0(sK1,sK1))) )
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f26510,f16656])).

fof(f26510,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK6(X2,sK2,k1_xboole_0),sK0)
        | ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | r1_tarski(sK2,k4_xboole_0(sK1,sK1))
        | ~ r2_hidden(sK1,sK6(X2,sK2,k4_xboole_0(sK1,sK1))) )
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f26500,f16656])).

fof(f26500,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3,sK6(X2,sK2,k1_xboole_0))
        | ~ m1_subset_1(sK6(X2,sK2,k4_xboole_0(sK1,sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | r1_tarski(sK2,k4_xboole_0(sK1,sK1))
        | ~ r2_hidden(sK1,sK6(X2,sK2,k4_xboole_0(sK1,sK1))) )
    | ~ spl8_592 ),
    inference(superposition,[],[f9884,f16656])).

fof(f9884,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,sK6(X0,sK2,k4_xboole_0(sK1,X1)))
      | ~ m1_subset_1(sK6(X0,sK2,k4_xboole_0(sK1,X1)),sK0)
      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,k4_xboole_0(sK1,X1))
      | ~ r2_hidden(X1,sK6(X0,sK2,k4_xboole_0(sK1,X1))) ) ),
    inference(duplicate_literal_removal,[],[f9869])).

fof(f9869,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0,sK2,k4_xboole_0(sK1,X1)),sK0)
      | ~ r2_hidden(sK3,sK6(X0,sK2,k4_xboole_0(sK1,X1)))
      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,k4_xboole_0(sK1,X1))
      | ~ r2_hidden(X1,sK6(X0,sK2,k4_xboole_0(sK1,X1)))
      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,k4_xboole_0(sK1,X1)) ) ),
    inference(resolution,[],[f4684,f55])).

fof(f4684,plain,(
    ! [X76,X77,X75] :
      ( ~ r2_hidden(sK6(X75,X76,k4_xboole_0(sK1,X77)),sK2)
      | ~ m1_subset_1(sK6(X75,X76,k4_xboole_0(sK1,X77)),sK0)
      | ~ r2_hidden(sK3,sK6(X75,X76,k4_xboole_0(sK1,X77)))
      | ~ m1_subset_1(k4_xboole_0(sK1,X77),k1_zfmisc_1(X75))
      | ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | r1_tarski(X76,k4_xboole_0(sK1,X77))
      | ~ r2_hidden(X77,sK6(X75,X76,k4_xboole_0(sK1,X77))) ) ),
    inference(resolution,[],[f119,f1666])).

fof(f24210,plain,
    ( ~ spl8_723
    | ~ spl8_725
    | ~ spl8_727
    | spl8_728
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f24185,f1040,f24208,f24202,f24196,f24190])).

fof(f24190,plain,
    ( spl8_723
  <=> ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_723])])).

fof(f24196,plain,
    ( spl8_725
  <=> ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_725])])).

fof(f24202,plain,
    ( spl8_727
  <=> ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_727])])).

fof(f24208,plain,
    ( spl8_728
  <=> k4_xboole_0(sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_728])])).

fof(f24185,plain,
    ( k4_xboole_0(sK2,sK1) = sK1
    | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f24184])).

fof(f24184,plain,
    ( k4_xboole_0(sK2,sK1) = sK1
    | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = sK1
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f24167,f1041])).

fof(f24167,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = sK1
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f24153])).

fof(f24153,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = sK1
    | ~ spl8_106 ),
    inference(resolution,[],[f9220,f6176])).

fof(f6176,plain,
    ( ! [X10,X11] :
        ( r2_hidden(sK4(sK1,sK3,k4_xboole_0(X10,X11)),X10)
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(X10,X11)))
        | k4_xboole_0(X10,X11) = sK1 )
    | ~ spl8_106 ),
    inference(resolution,[],[f5027,f38])).

fof(f5027,plain,
    ( ! [X6,X5] :
        ( sP5(sK4(sK1,sK3,k4_xboole_0(X5,X6)),X6,X5)
        | k4_xboole_0(X5,X6) = sK1
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(X5,X6))) )
    | ~ spl8_106 ),
    inference(resolution,[],[f4788,f59])).

fof(f4788,plain,
    ( ! [X5] :
        ( r2_hidden(sK4(sK1,sK3,X5),X5)
        | ~ r2_hidden(sK1,sK4(sK1,sK3,X5))
        | sK1 = X5 )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4775,f1041])).

fof(f4775,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK1,sK4(sK1,sK3,X5))
        | r2_hidden(sK4(sK1,sK3,X5),X5)
        | k4_xboole_0(sK1,sK3) = X5 )
    | ~ spl8_106 ),
    inference(resolution,[],[f4437,f42])).

fof(f4437,plain,
    ( ! [X12] :
        ( ~ sP5(X12,sK3,sK1)
        | ~ r2_hidden(sK1,X12) )
    | ~ spl8_106 ),
    inference(superposition,[],[f230,f1041])).

fof(f23255,plain,
    ( spl8_76
    | spl8_720
    | ~ spl8_719
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f23251,f6161,f1211,f23245,f23253,f649])).

fof(f23253,plain,
    ( spl8_720
  <=> ! [X25,X26] :
        ( ~ r2_hidden(sK3,X26)
        | r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25))
        | ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_720])])).

fof(f23245,plain,
    ( spl8_719
  <=> ~ m1_subset_1(sK4(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_719])])).

fof(f23251,plain,
    ( ! [X26,X25] :
        ( ~ m1_subset_1(sK4(sK1,sK2,sK3),sK0)
        | ~ r2_hidden(sK3,X26)
        | k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25)) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23250,f3648])).

fof(f23250,plain,
    ( ! [X26,X25] :
        ( ~ r2_hidden(sK3,X26)
        | k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25))
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,k4_xboole_0(sK1,X25))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23249,f3648])).

fof(f23249,plain,
    ( ! [X26,X25] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25))
        | ~ r2_hidden(k4_xboole_0(sK3,k4_xboole_0(sK1,X25)),X26)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,k4_xboole_0(sK1,X25))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23248,f3648])).

fof(f23248,plain,
    ( ! [X26,X25] :
        ( ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25))
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X25)) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK3,k4_xboole_0(sK1,X25)),X26)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,k4_xboole_0(sK1,X25))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23182,f3648])).

fof(f23182,plain,
    ( ! [X26,X25] :
        ( r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,sK3)),k4_xboole_0(sK1,X25))
        | ~ r2_hidden(k4_xboole_0(X26,sK4(sK1,sK2,k4_xboole_0(sK3,k4_xboole_0(sK1,X25)))),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X25)) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK3,k4_xboole_0(sK1,X25)),X26)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,k4_xboole_0(sK1,X25))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(superposition,[],[f15228,f3648])).

fof(f15228,plain,
    ( ! [X99,X100,X98] :
        ( r2_hidden(k4_xboole_0(X98,sK4(sK1,sK2,k4_xboole_0(X99,X100))),X100)
        | ~ r2_hidden(k4_xboole_0(X98,sK4(sK1,sK2,k4_xboole_0(X99,X100))),X99)
        | k4_xboole_0(X99,X100) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(X99,X100),X98)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(X99,X100)),sK0) )
    | ~ spl8_216 ),
    inference(backward_demodulation,[],[f6162,f8773])).

fof(f8773,plain,(
    ! [X99,X100,X98] :
      ( ~ r2_hidden(k4_xboole_0(X98,sK4(sK1,sK2,k4_xboole_0(X99,X100))),X99)
      | r2_hidden(k4_xboole_0(X98,sK4(sK1,sK2,k4_xboole_0(X99,X100))),X100)
      | ~ r2_hidden(k4_xboole_0(X99,X100),X98)
      | k4_xboole_0(sK1,sK2) = k4_xboole_0(X99,X100)
      | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(X99,X100)),sK0) ) ),
    inference(resolution,[],[f2107,f5341])).

fof(f5341,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK4(sK1,sK2,X5))
      | k4_xboole_0(sK1,sK2) = X5
      | ~ m1_subset_1(sK4(sK1,sK2,X5),sK0) ) ),
    inference(duplicate_literal_removal,[],[f5320])).

fof(f5320,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK4(sK1,sK2,X5),sK0)
      | k4_xboole_0(sK1,sK2) = X5
      | ~ r2_hidden(X5,sK4(sK1,sK2,X5))
      | k4_xboole_0(sK1,sK2) = X5
      | ~ r2_hidden(X5,sK4(sK1,sK2,X5)) ) ),
    inference(resolution,[],[f4403,f416])).

fof(f4403,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(X8,sK2,X9),sK1)
      | ~ m1_subset_1(sK4(X8,sK2,X9),sK0)
      | k4_xboole_0(X8,sK2) = X9
      | ~ r2_hidden(X9,sK4(X8,sK2,X9)) ) ),
    inference(resolution,[],[f30,f407])).

fof(f407,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(resolution,[],[f281,f57])).

fof(f23247,plain,
    ( spl8_76
    | spl8_716
    | ~ spl8_719
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f23237,f6161,f1211,f23245,f23239,f649])).

fof(f23239,plain,
    ( spl8_716
  <=> ! [X24] :
        ( ~ r2_hidden(sK3,X24)
        | r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_716])])).

fof(f23237,plain,
    ( ! [X24] :
        ( ~ m1_subset_1(sK4(sK1,sK2,sK3),sK0)
        | ~ r2_hidden(sK3,X24)
        | k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23236,f1212])).

fof(f23236,plain,
    ( ! [X24] :
        ( ~ r2_hidden(sK3,X24)
        | k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,sK1)),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23235,f1212])).

fof(f23235,plain,
    ( ! [X24] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(sK3,sK1),X24)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,sK1)),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23234,f1212])).

fof(f23234,plain,
    ( ! [X24] :
        ( ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK3)
        | r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK3,sK1),X24)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,sK1)),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23181,f1212])).

fof(f23181,plain,
    ( ! [X24] :
        ( r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,sK3)),sK1)
        | ~ r2_hidden(k4_xboole_0(X24,sK4(sK1,sK2,k4_xboole_0(sK3,sK1))),sK3)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK3,sK1),X24)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK3,sK1)),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(superposition,[],[f15228,f1212])).

fof(f23233,plain,
    ( spl8_192
    | spl8_714
    | ~ spl8_713
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f23229,f6161,f1040,f23223,f23231,f5043])).

fof(f23231,plain,
    ( spl8_714
  <=> ! [X23] :
        ( ~ r2_hidden(sK1,X23)
        | r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_714])])).

fof(f23223,plain,
    ( spl8_713
  <=> ~ m1_subset_1(sK4(sK1,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_713])])).

fof(f23229,plain,
    ( ! [X23] :
        ( ~ m1_subset_1(sK4(sK1,sK2,sK1),sK0)
        | ~ r2_hidden(sK1,X23)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23228,f1041])).

fof(f23228,plain,
    ( ! [X23] :
        ( ~ r2_hidden(sK1,X23)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK3)),sK0) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23227,f1041])).

fof(f23227,plain,
    ( ! [X23] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(sK1,sK3),X23)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK3)),sK0) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23226,f1041])).

fof(f23226,plain,
    ( ! [X23] :
        ( ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK1,sK3),X23)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK3)),sK0) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23180,f1041])).

fof(f23180,plain,
    ( ! [X23] :
        ( r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,sK1)),sK3)
        | ~ r2_hidden(k4_xboole_0(X23,sK4(sK1,sK2,k4_xboole_0(sK1,sK3))),sK1)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK1,sK3),X23)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK3)),sK0) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(superposition,[],[f15228,f1041])).

fof(f23225,plain,
    ( spl8_192
    | spl8_710
    | ~ spl8_713
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f23215,f6161,f1211,f23223,f23217,f5043])).

fof(f23217,plain,
    ( spl8_710
  <=> ! [X20,X19] :
        ( ~ r2_hidden(sK1,X20)
        | r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19))
        | ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_710])])).

fof(f23215,plain,
    ( ! [X19,X20] :
        ( ~ m1_subset_1(sK4(sK1,sK2,sK1),sK0)
        | ~ r2_hidden(sK1,X20)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19)) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23214,f5148])).

fof(f23214,plain,
    ( ! [X19,X20] :
        ( ~ r2_hidden(sK1,X20)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19))
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,k4_xboole_0(sK3,X19))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23213,f5148])).

fof(f23213,plain,
    ( ! [X19,X20] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19))
        | ~ r2_hidden(k4_xboole_0(sK1,k4_xboole_0(sK3,X19)),X20)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,k4_xboole_0(sK3,X19))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23212,f5148])).

fof(f23212,plain,
    ( ! [X19,X20] :
        ( ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),sK1)
        | r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19))
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X19)) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK1,k4_xboole_0(sK3,X19)),X20)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,k4_xboole_0(sK3,X19))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f23177,f5148])).

fof(f23177,plain,
    ( ! [X19,X20] :
        ( r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,sK1)),k4_xboole_0(sK3,X19))
        | ~ r2_hidden(k4_xboole_0(X20,sK4(sK1,sK2,k4_xboole_0(sK1,k4_xboole_0(sK3,X19)))),sK1)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X19)) = k1_xboole_0
        | ~ r2_hidden(k4_xboole_0(sK1,k4_xboole_0(sK3,X19)),X20)
        | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,k4_xboole_0(sK3,X19))),sK0) )
    | ~ spl8_116
    | ~ spl8_216 ),
    inference(superposition,[],[f15228,f5148])).

fof(f22859,plain,
    ( ~ spl8_709
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f22833,f1202,f22857])).

fof(f22857,plain,
    ( spl8_709
  <=> ~ r2_hidden(sK4(sK3,sK1,sK3),sK4(sK3,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_709])])).

fof(f1202,plain,
    ( spl8_114
  <=> r2_hidden(sK4(sK3,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f22833,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,sK3),sK4(sK3,sK1,sK3))
    | ~ spl8_114 ),
    inference(resolution,[],[f14823,f1203])).

fof(f1203,plain,
    ( r2_hidden(sK4(sK3,sK1,sK3),sK3)
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f22852,plain,
    ( ~ spl8_707
    | ~ spl8_546 ),
    inference(avatar_split_clause,[],[f22830,f15353,f22849])).

fof(f22849,plain,
    ( spl8_707
  <=> ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK4(sK1,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_707])])).

fof(f15353,plain,
    ( spl8_546
  <=> r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_546])])).

fof(f22830,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK4(sK1,sK3,k1_xboole_0))
    | ~ spl8_546 ),
    inference(resolution,[],[f14823,f15354])).

fof(f15354,plain,
    ( r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK2)
    | ~ spl8_546 ),
    inference(avatar_component_clause,[],[f15353])).

fof(f22851,plain,
    ( ~ spl8_707
    | ~ spl8_542 ),
    inference(avatar_split_clause,[],[f22829,f15339,f22849])).

fof(f15339,plain,
    ( spl8_542
  <=> r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_542])])).

fof(f22829,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK4(sK1,sK3,k1_xboole_0))
    | ~ spl8_542 ),
    inference(resolution,[],[f14823,f15340])).

fof(f15340,plain,
    ( r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK1)
    | ~ spl8_542 ),
    inference(avatar_component_clause,[],[f15339])).

fof(f22142,plain,
    ( spl8_42
    | spl8_704
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f22138,f6161,f22140,f217])).

fof(f217,plain,
    ( spl8_42
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f22140,plain,
    ( spl8_704
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X4,sK0)
        | ~ sP5(sK3,k1_xboole_0,X4)
        | ~ sP5(sK1,k1_xboole_0,X4)
        | ~ r2_hidden(k4_xboole_0(X3,sK2),X4)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_704])])).

fof(f22138,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,sK0)
        | ~ r2_hidden(X4,X3)
        | r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK2),X4)
        | ~ sP5(sK1,k1_xboole_0,X4)
        | ~ sP5(sK3,k1_xboole_0,X4) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f22137,f51])).

fof(f22137,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,X3)
        | r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK2),X4)
        | ~ m1_subset_1(k4_xboole_0(X4,k1_xboole_0),sK0)
        | ~ sP5(sK1,k1_xboole_0,X4)
        | ~ sP5(sK3,k1_xboole_0,X4) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f22112,f51])).

fof(f22112,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(k4_xboole_0(X3,sK2),X4)
        | ~ r2_hidden(k4_xboole_0(X4,k1_xboole_0),X3)
        | ~ m1_subset_1(k4_xboole_0(X4,k1_xboole_0),sK0)
        | ~ sP5(sK1,k1_xboole_0,X4)
        | ~ sP5(sK3,k1_xboole_0,X4) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17256,f8751])).

fof(f17256,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(k4_xboole_0(X7,X8),k1_xboole_0)
        | r2_hidden(sK1,X8)
        | ~ r2_hidden(sK1,X7) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17168,f2119])).

fof(f22136,plain,
    ( spl8_40
    | spl8_702
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f22132,f6161,f22134,f211])).

fof(f211,plain,
    ( spl8_40
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f22134,plain,
    ( spl8_702
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ sP5(sK2,k1_xboole_0,X2)
        | ~ r2_hidden(k4_xboole_0(X1,sK1),X2)
        | ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_702])])).

fof(f22132,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r2_hidden(X2,X1)
        | r2_hidden(sK1,sK1)
        | ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(k4_xboole_0(X1,sK1),X2)
        | ~ sP5(sK2,k1_xboole_0,X2) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f22131,f51])).

fof(f22131,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | r2_hidden(sK1,sK1)
        | ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(k4_xboole_0(X1,sK1),X2)
        | ~ m1_subset_1(k4_xboole_0(X2,k1_xboole_0),sK0)
        | ~ sP5(sK2,k1_xboole_0,X2) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f22111,f51])).

fof(f22111,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK1,sK1)
        | ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(k4_xboole_0(X1,sK1),X2)
        | ~ r2_hidden(k4_xboole_0(X2,k1_xboole_0),X1)
        | ~ m1_subset_1(k4_xboole_0(X2,k1_xboole_0),sK0)
        | ~ sP5(sK2,k1_xboole_0,X2) )
    | ~ spl8_216 ),
    inference(resolution,[],[f17256,f8750])).

fof(f21631,plain,
    ( ~ spl8_701
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f21624,f16655,f21629])).

fof(f21629,plain,
    ( spl8_701
  <=> ~ sP5(k1_xboole_0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_701])])).

fof(f21624,plain,
    ( ~ sP5(k1_xboole_0,sK1,sK1)
    | ~ spl8_592 ),
    inference(duplicate_literal_removal,[],[f21619])).

fof(f21619,plain,
    ( ~ sP5(k1_xboole_0,sK1,sK1)
    | ~ sP5(k1_xboole_0,sK1,sK1)
    | ~ spl8_592 ),
    inference(superposition,[],[f20398,f16656])).

fof(f20398,plain,
    ( ! [X85,X84] :
        ( ~ sP5(k4_xboole_0(X85,X84),sK1,sK1)
        | ~ sP5(k1_xboole_0,X84,X85) )
    | ~ spl8_592 ),
    inference(superposition,[],[f337,f16656])).

fof(f20906,plain,
    ( ~ spl8_697
    | ~ spl8_699
    | ~ spl8_216
    | spl8_685 ),
    inference(avatar_split_clause,[],[f20891,f20229,f6161,f20904,f20898])).

fof(f20898,plain,
    ( spl8_697
  <=> ~ r2_hidden(sK2,sK4(sK3,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_697])])).

fof(f20229,plain,
    ( spl8_685
  <=> ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_685])])).

fof(f20891,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),sK1)
    | ~ r2_hidden(sK2,sK4(sK3,sK1,k1_xboole_0))
    | ~ spl8_216
    | ~ spl8_685 ),
    inference(resolution,[],[f20230,f18541])).

fof(f20230,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_685 ),
    inference(avatar_component_clause,[],[f20229])).

fof(f20779,plain,
    ( ~ spl8_695
    | spl8_196
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f20513,f16655,f1211,f5268,f20768])).

fof(f20768,plain,
    ( spl8_695
  <=> ~ sP5(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_695])])).

fof(f20513,plain,
    ( ! [X275] :
        ( ~ sP5(k1_xboole_0,k4_xboole_0(sK3,X275),sK1)
        | ~ sP5(sK1,sK1,sK1) )
    | ~ spl8_116
    | ~ spl8_592 ),
    inference(superposition,[],[f5184,f16656])).

fof(f20770,plain,
    ( ~ spl8_695
    | ~ spl8_171
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f20503,f16655,f1040,f4522,f20768])).

fof(f20503,plain,
    ( ~ sP5(k1_xboole_0,sK3,sK1)
    | ~ sP5(sK1,sK1,sK1)
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(superposition,[],[f4442,f16656])).

fof(f20730,plain,
    ( spl8_692
    | spl8_574
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f20726,f16655,f15992,f20728])).

fof(f20728,plain,
    ( spl8_692
  <=> ! [X239] :
        ( ~ r2_hidden(sK1,sK6(X239,sK1,k1_xboole_0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X239)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_692])])).

fof(f15992,plain,
    ( spl8_574
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_574])])).

fof(f20726,plain,
    ( ! [X239] :
        ( r1_tarski(sK1,k1_xboole_0)
        | ~ r2_hidden(sK1,sK6(X239,sK1,k1_xboole_0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X239)) )
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f20485,f16656])).

fof(f20485,plain,
    ( ! [X239] :
        ( ~ r2_hidden(sK1,sK6(X239,sK1,k1_xboole_0))
        | r1_tarski(sK1,k4_xboole_0(sK1,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X239)) )
    | ~ spl8_592 ),
    inference(superposition,[],[f3468,f16656])).

fof(f20561,plain,
    ( ~ spl8_691
    | spl8_192
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(avatar_split_clause,[],[f20554,f16655,f1040,f5043,f20559])).

fof(f20559,plain,
    ( spl8_691
  <=> ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_691])])).

fof(f20554,plain,
    ( k1_xboole_0 = sK1
    | ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK1,sK1)
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(forward_demodulation,[],[f20349,f16656])).

fof(f20349,plain,
    ( ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK1,sK1)
    | k4_xboole_0(sK1,sK1) = sK1
    | ~ spl8_106
    | ~ spl8_592 ),
    inference(superposition,[],[f9904,f16656])).

fof(f9904,plain,
    ( ! [X6] :
        ( ~ sP5(sK4(sK1,sK3,k4_xboole_0(sK1,X6)),X6,sK1)
        | k4_xboole_0(sK1,X6) = sK1 )
    | ~ spl8_106 ),
    inference(resolution,[],[f6966,f60])).

fof(f6966,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,X9)),k4_xboole_0(sK1,X9))
        | k4_xboole_0(sK1,X9) = sK1 )
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f6965])).

fof(f6965,plain,
    ( ! [X9] :
        ( k4_xboole_0(sK1,X9) = sK1
        | k4_xboole_0(sK1,X9) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,X9)),k4_xboole_0(sK1,X9)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f6931,f1041])).

fof(f6931,plain,
    ( ! [X9] :
        ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,X9)
        | k4_xboole_0(sK1,X9) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,X9)),k4_xboole_0(sK1,X9)) )
    | ~ spl8_106 ),
    inference(resolution,[],[f3016,f4736])).

fof(f3016,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,k4_xboole_0(X0,X2)),X0)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X0,X2) ) ),
    inference(factoring,[],[f1514])).

fof(f20246,plain,
    ( ~ spl8_689
    | ~ spl8_592
    | spl8_661 ),
    inference(avatar_split_clause,[],[f20221,f19838,f16655,f20244])).

fof(f20244,plain,
    ( spl8_689
  <=> ~ sP5(sK4(sK3,sK1,k1_xboole_0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_689])])).

fof(f19838,plain,
    ( spl8_661
  <=> ~ sP5(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_661])])).

fof(f20221,plain,
    ( ~ sP5(sK4(sK3,sK1,k1_xboole_0),sK1,sK1)
    | ~ spl8_592
    | ~ spl8_661 ),
    inference(backward_demodulation,[],[f16656,f19839])).

fof(f19839,plain,
    ( ~ sP5(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),sK1,sK1)
    | ~ spl8_661 ),
    inference(avatar_component_clause,[],[f19838])).

fof(f20239,plain,
    ( ~ spl8_687
    | ~ spl8_592
    | spl8_655 ),
    inference(avatar_split_clause,[],[f20219,f19665,f16655,f20237])).

fof(f20237,plain,
    ( spl8_687
  <=> ~ m1_subset_1(sK4(sK3,sK3,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_687])])).

fof(f19665,plain,
    ( spl8_655
  <=> ~ m1_subset_1(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_655])])).

fof(f20219,plain,
    ( ~ m1_subset_1(sK4(sK3,sK3,k1_xboole_0),sK0)
    | ~ spl8_592
    | ~ spl8_655 ),
    inference(backward_demodulation,[],[f16656,f19666])).

fof(f19666,plain,
    ( ~ m1_subset_1(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK0)
    | ~ spl8_655 ),
    inference(avatar_component_clause,[],[f19665])).

fof(f20232,plain,
    ( ~ spl8_587
    | ~ spl8_592
    | spl8_649 ),
    inference(avatar_split_clause,[],[f20218,f19589,f16655,f16583])).

fof(f16583,plain,
    ( spl8_587
  <=> ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_587])])).

fof(f19589,plain,
    ( spl8_649
  <=> ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_649])])).

fof(f20218,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0)
    | ~ spl8_592
    | ~ spl8_649 ),
    inference(backward_demodulation,[],[f16656,f19590])).

fof(f19590,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK1,sK1)),sK0)
    | ~ spl8_649 ),
    inference(avatar_component_clause,[],[f19589])).

fof(f20231,plain,
    ( ~ spl8_685
    | ~ spl8_592
    | spl8_635 ),
    inference(avatar_split_clause,[],[f20217,f18920,f16655,f20229])).

fof(f18920,plain,
    ( spl8_635
  <=> ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_635])])).

fof(f20217,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_592
    | ~ spl8_635 ),
    inference(backward_demodulation,[],[f16656,f18921])).

fof(f18921,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1))
    | ~ spl8_635 ),
    inference(avatar_component_clause,[],[f18920])).

fof(f20213,plain,
    ( spl8_592
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f20204,f6161,f16655])).

fof(f20204,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ spl8_216 ),
    inference(duplicate_literal_removal,[],[f20195])).

fof(f20195,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ spl8_216 ),
    inference(resolution,[],[f15933,f4045])).

fof(f4045,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X0,k1_xboole_0),X1)
      | k4_xboole_0(X0,X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f4021])).

fof(f4021,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = k1_xboole_0
      | k4_xboole_0(X0,X0) = k1_xboole_0
      | ~ r2_hidden(sK4(X0,X0,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f2217,f419])).

fof(f419,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(sK4(X10,X11,k1_xboole_0),X10)
      | k4_xboole_0(X10,X11) = k1_xboole_0
      | ~ r2_hidden(sK4(X10,X11,k1_xboole_0),X12) ) ),
    inference(resolution,[],[f282,f270])).

fof(f2217,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK4(X5,X6,k1_xboole_0),X6)
      | k4_xboole_0(X5,X6) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f2205])).

fof(f2205,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK4(X5,X6,k1_xboole_0),X6)
      | k4_xboole_0(X5,X6) = k1_xboole_0
      | k4_xboole_0(X5,X6) = k1_xboole_0
      | ~ r2_hidden(sK4(X5,X6,k1_xboole_0),X6) ) ),
    inference(resolution,[],[f410,f281])).

fof(f410,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,k1_xboole_0),X12)
      | ~ r2_hidden(sK4(X10,X11,k1_xboole_0),X11)
      | k4_xboole_0(X10,X11) = k1_xboole_0 ) ),
    inference(resolution,[],[f281,f270])).

fof(f15933,plain,
    ( ! [X159] :
        ( r2_hidden(sK4(sK1,X159,k1_xboole_0),sK1)
        | k4_xboole_0(sK1,X159) = k1_xboole_0 )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15681,f6162])).

fof(f15681,plain,
    ( ! [X159] :
        ( r2_hidden(sK4(sK1,X159,k1_xboole_0),sK1)
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,X159) )
    | ~ spl8_216 ),
    inference(superposition,[],[f3016,f6162])).

fof(f20212,plain,
    ( spl8_592
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f20208,f6161,f16655])).

fof(f20208,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ spl8_216 ),
    inference(duplicate_literal_removal,[],[f20190])).

fof(f20190,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ spl8_216 ),
    inference(resolution,[],[f15933,f2217])).

fof(f19985,plain,
    ( ~ spl8_679
    | ~ spl8_681
    | ~ spl8_683
    | spl8_582 ),
    inference(avatar_split_clause,[],[f19966,f16571,f19983,f19977,f19971])).

fof(f19971,plain,
    ( spl8_679
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_679])])).

fof(f19977,plain,
    ( spl8_681
  <=> ~ m1_subset_1(sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_681])])).

fof(f19983,plain,
    ( spl8_683
  <=> ~ r2_hidden(sK3,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_683])])).

fof(f19966,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK3,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) ),
    inference(duplicate_literal_removal,[],[f19965])).

fof(f19965,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK3,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f19876,f50])).

fof(f19876,plain,
    ( ~ r2_hidden(sK3,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0)
    | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(resolution,[],[f8598,f428])).

fof(f19964,plain,
    ( ~ spl8_673
    | spl8_674
    | ~ spl8_677 ),
    inference(avatar_split_clause,[],[f19896,f19962,f19956,f19950])).

fof(f19950,plain,
    ( spl8_673
  <=> ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_673])])).

fof(f19956,plain,
    ( spl8_674
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_674])])).

fof(f19962,plain,
    ( spl8_677
  <=> ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_677])])).

fof(f19896,plain,
    ( ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),sK2)
    | ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f19874])).

fof(f19874,plain,
    ( ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),sK2)
    | ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),sK2,k4_xboole_0(sK2,sK1)),sK0)
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),sK2) ),
    inference(resolution,[],[f8598,f2756])).

fof(f19945,plain,
    ( ~ spl8_667
    | spl8_668
    | ~ spl8_671 ),
    inference(avatar_split_clause,[],[f19907,f19943,f19937,f19931])).

fof(f19931,plain,
    ( spl8_667
  <=> ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_667])])).

fof(f19937,plain,
    ( spl8_668
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_668])])).

fof(f19943,plain,
    ( spl8_671
  <=> ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_671])])).

fof(f19907,plain,
    ( ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f19863])).

fof(f19863,plain,
    ( ~ r2_hidden(sK3,sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK4(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)),sK0)
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f8598,f422])).

fof(f19926,plain,
    ( ~ spl8_663
    | spl8_644
    | ~ spl8_665 ),
    inference(avatar_split_clause,[],[f19908,f19924,f19576,f19918])).

fof(f19918,plain,
    ( spl8_663
  <=> ~ m1_subset_1(sK4(sK2,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_663])])).

fof(f19576,plain,
    ( spl8_644
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_644])])).

fof(f19924,plain,
    ( spl8_665
  <=> ~ r2_hidden(sK3,sK4(sK2,sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_665])])).

fof(f19908,plain,
    ( ~ r2_hidden(sK3,sK4(sK2,sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK2,sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f19862])).

fof(f19862,plain,
    ( ~ r2_hidden(sK3,sK4(sK2,sK2,k4_xboole_0(sK2,sK1)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK2,sK2,k4_xboole_0(sK2,sK1)),sK0)
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f8598,f3016])).

fof(f19840,plain,
    ( ~ spl8_661
    | spl8_635 ),
    inference(avatar_split_clause,[],[f19822,f18920,f19838])).

fof(f19822,plain,
    ( ~ sP5(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),sK1,sK1)
    | ~ spl8_635 ),
    inference(resolution,[],[f18921,f60])).

fof(f19833,plain,
    ( spl8_636
    | ~ spl8_659
    | ~ spl8_116
    | spl8_635 ),
    inference(avatar_split_clause,[],[f19816,f18920,f1211,f19831,f18926])).

fof(f18926,plain,
    ( spl8_636
  <=> k4_xboole_0(sK1,sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_636])])).

fof(f19831,plain,
    ( spl8_659
  <=> ~ r2_hidden(sK3,sK4(sK3,sK1,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_659])])).

fof(f19816,plain,
    ( ~ r2_hidden(sK3,sK4(sK3,sK1,k4_xboole_0(sK1,sK1)))
    | k4_xboole_0(sK1,sK1) = sK3
    | ~ spl8_116
    | ~ spl8_635 ),
    inference(resolution,[],[f18921,f2620])).

fof(f2620,plain,
    ( ! [X5] :
        ( r2_hidden(sK4(sK3,sK1,X5),X5)
        | ~ r2_hidden(sK3,sK4(sK3,sK1,X5))
        | sK3 = X5 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f2611,f1212])).

fof(f2611,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK3,sK4(sK3,sK1,X5))
        | r2_hidden(sK4(sK3,sK1,X5),X5)
        | k4_xboole_0(sK3,sK1) = X5 )
    | ~ spl8_116 ),
    inference(resolution,[],[f2447,f42])).

fof(f2447,plain,
    ( ! [X5] :
        ( ~ sP5(X5,sK1,sK3)
        | ~ r2_hidden(sK3,X5) )
    | ~ spl8_116 ),
    inference(superposition,[],[f230,f1212])).

fof(f19673,plain,
    ( spl8_652
    | ~ spl8_655
    | ~ spl8_657 ),
    inference(avatar_split_clause,[],[f19646,f19671,f19665,f19659])).

fof(f19659,plain,
    ( spl8_652
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_652])])).

fof(f19671,plain,
    ( spl8_657
  <=> ~ r2_hidden(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_657])])).

fof(f19646,plain,
    ( ~ r2_hidden(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK2)
    | ~ m1_subset_1(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK0)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(duplicate_literal_removal,[],[f19623])).

fof(f19623,plain,
    ( ~ r2_hidden(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK2)
    | ~ m1_subset_1(sK4(sK3,sK3,k4_xboole_0(sK1,sK1)),sK0)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(resolution,[],[f6900,f6915])).

fof(f6915,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(X4,X4,k4_xboole_0(X5,X5)),X5)
      | k4_xboole_0(X4,X4) = k4_xboole_0(X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f6885])).

fof(f6885,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X4) = k4_xboole_0(X5,X5)
      | k4_xboole_0(X4,X4) = k4_xboole_0(X5,X5)
      | ~ r2_hidden(sK4(X4,X4,k4_xboole_0(X5,X5)),X5) ) ),
    inference(resolution,[],[f2933,f1513])).

fof(f6900,plain,(
    ! [X37,X36] :
      ( r2_hidden(sK4(X36,sK3,k4_xboole_0(X37,X37)),sK1)
      | ~ r2_hidden(sK4(X36,sK3,k4_xboole_0(X37,X37)),sK2)
      | ~ m1_subset_1(sK4(X36,sK3,k4_xboole_0(X37,X37)),sK0)
      | k4_xboole_0(X36,sK3) = k4_xboole_0(X37,X37) ) ),
    inference(resolution,[],[f2933,f32])).

fof(f19597,plain,
    ( ~ spl8_647
    | ~ spl8_649
    | spl8_650 ),
    inference(avatar_split_clause,[],[f19553,f19595,f19589,f19583])).

fof(f19583,plain,
    ( spl8_647
  <=> ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_647])])).

fof(f19595,plain,
    ( spl8_650
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_650])])).

fof(f19553,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK1,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK1,sK1))) ),
    inference(duplicate_literal_removal,[],[f19527])).

fof(f19527,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK1,sK1)),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK1,sK1)))
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f6898,f6917])).

fof(f6898,plain,(
    ! [X33,X32] :
      ( ~ r2_hidden(sK4(X32,sK1,k4_xboole_0(X33,X33)),sK2)
      | k4_xboole_0(X32,sK1) = k4_xboole_0(X33,X33)
      | ~ m1_subset_1(sK4(X32,sK1,k4_xboole_0(X33,X33)),sK0)
      | ~ r2_hidden(sK3,sK4(X32,sK1,k4_xboole_0(X33,X33))) ) ),
    inference(resolution,[],[f2933,f119])).

fof(f19578,plain,
    ( ~ spl8_641
    | ~ spl8_643
    | spl8_644 ),
    inference(avatar_split_clause,[],[f19554,f19576,f19570,f19564])).

fof(f19564,plain,
    ( spl8_641
  <=> ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_641])])).

fof(f19570,plain,
    ( spl8_643
  <=> ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_643])])).

fof(f19554,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK2,sK2)),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK2,sK2))) ),
    inference(duplicate_literal_removal,[],[f19526])).

fof(f19526,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK2,sK1,k4_xboole_0(sK2,sK2)),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k4_xboole_0(sK2,sK2)))
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f6898,f3016])).

fof(f19260,plain,
    ( spl8_166
    | spl8_638
    | ~ spl8_106
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f19241,f13870,f1040,f19258,f4339])).

fof(f19258,plain,
    ( spl8_638
  <=> ! [X172,X171] :
        ( ~ r2_hidden(sK6(X171,sK1,k4_xboole_0(sK2,sK3)),X172)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X171))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X171))
        | ~ r2_hidden(sK6(X171,sK1,k4_xboole_0(sK2,sK3)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_638])])).

fof(f19241,plain,
    ( ! [X171,X172] :
        ( ~ r2_hidden(sK6(X171,sK1,k4_xboole_0(sK2,sK3)),X172)
        | ~ r2_hidden(sK6(X171,sK1,k4_xboole_0(sK2,sK3)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X171))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X171)) )
    | ~ spl8_106
    | ~ spl8_436 ),
    inference(resolution,[],[f15055,f4557])).

fof(f4557,plain,
    ( ! [X94,X93] :
        ( ~ r2_hidden(sK6(X93,sK1,k4_xboole_0(X94,sK3)),X94)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X93))
        | r1_tarski(sK1,k4_xboole_0(X94,sK3))
        | ~ m1_subset_1(k4_xboole_0(X94,sK3),k1_zfmisc_1(X93)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4556,f1041])).

fof(f4556,plain,
    ( ! [X94,X93] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X93))
        | ~ r2_hidden(sK6(X93,sK1,k4_xboole_0(X94,sK3)),X94)
        | ~ m1_subset_1(k4_xboole_0(X94,sK3),k1_zfmisc_1(X93))
        | r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(X94,sK3)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4482,f1041])).

fof(f4482,plain,
    ( ! [X94,X93] :
        ( ~ r2_hidden(sK6(X93,sK1,k4_xboole_0(X94,sK3)),X94)
        | ~ m1_subset_1(k4_xboole_0(X94,sK3),k1_zfmisc_1(X93))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(X93))
        | r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(X94,sK3)) )
    | ~ spl8_106 ),
    inference(superposition,[],[f1680,f1041])).

fof(f1680,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X3,k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)),X2)
      | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X3))
      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ) ),
    inference(duplicate_literal_removal,[],[f1663])).

fof(f1663,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
      | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X3))
      | ~ r2_hidden(sK6(X3,k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)),X2)
      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
      | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f466,f443])).

fof(f18928,plain,
    ( ~ spl8_635
    | spl8_636
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f18915,f1211,f18926,f18920])).

fof(f18915,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1))
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f18914])).

fof(f18914,plain,
    ( k4_xboole_0(sK1,sK1) = sK3
    | k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1))
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f18858,f1212])).

fof(f18858,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK1)
    | k4_xboole_0(sK1,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1))
    | ~ spl8_116 ),
    inference(resolution,[],[f6917,f2553])).

fof(f2553,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK4(sK3,sK1,X6),sK3)
        | sK3 = X6
        | ~ r2_hidden(sK4(sK3,sK1,X6),X6) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f2543,f1212])).

fof(f2543,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK4(sK3,sK1,X6),sK3)
        | ~ r2_hidden(sK4(sK3,sK1,X6),X6)
        | k4_xboole_0(sK3,sK1) = X6 )
    | ~ spl8_116 ),
    inference(resolution,[],[f2445,f43])).

fof(f18912,plain,
    ( ~ spl8_631
    | spl8_632
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f18899,f6161,f18910,f18904])).

fof(f18904,plain,
    ( spl8_631
  <=> ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_631])])).

fof(f18899,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0
    | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK2,sK2)),sK0)
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f18881,f6162])).

fof(f18881,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK2,sK2)),sK0) ),
    inference(duplicate_literal_removal,[],[f18851])).

fof(f18851,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK2)
    | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK2,sK2)),sK0)
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f6917,f6899])).

fof(f6899,plain,(
    ! [X35,X34] :
      ( ~ r2_hidden(sK4(X34,sK2,k4_xboole_0(X35,X35)),sK1)
      | ~ m1_subset_1(sK4(X34,sK2,k4_xboole_0(X35,X35)),sK0)
      | k4_xboole_0(X34,sK2) = k4_xboole_0(X35,X35) ) ),
    inference(resolution,[],[f2933,f30])).

fof(f18615,plain,
    ( spl8_166
    | spl8_628
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f18598,f6161,f1040,f18613,f4339])).

fof(f18613,plain,
    ( spl8_628
  <=> ! [X107] :
        ( r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),k1_xboole_0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X107))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X107))
        | ~ r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_628])])).

fof(f18598,plain,
    ( ! [X107] :
        ( r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),k1_xboole_0)
        | ~ r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X107))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X107)) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(resolution,[],[f17614,f4557])).

fof(f18455,plain,
    ( spl8_166
    | spl8_626
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f18438,f6161,f1040,f18453,f4339])).

fof(f18453,plain,
    ( spl8_626
  <=> ! [X107] :
        ( ~ r2_hidden(k1_xboole_0,sK6(X107,sK1,k4_xboole_0(sK2,sK3)))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X107))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X107))
        | ~ r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_626])])).

fof(f18438,plain,
    ( ! [X107] :
        ( ~ r2_hidden(k1_xboole_0,sK6(X107,sK1,k4_xboole_0(sK2,sK3)))
        | ~ r2_hidden(sK6(X107,sK1,k4_xboole_0(sK2,sK3)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X107))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X107)) )
    | ~ spl8_106
    | ~ spl8_216 ),
    inference(resolution,[],[f15665,f4557])).

fof(f17962,plain,
    ( ~ spl8_21
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f17960,f137,f140])).

fof(f140,plain,
    ( spl8_21
  <=> ~ r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f17960,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl8_20 ),
    inference(resolution,[],[f138,f57])).

fof(f138,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f17954,plain,
    ( spl8_42
    | spl8_624 ),
    inference(avatar_split_clause,[],[f17912,f17952,f217])).

fof(f17952,plain,
    ( spl8_624
  <=> ! [X16,X15] :
        ( ~ r2_hidden(k4_xboole_0(X15,sK2),X16)
        | ~ r2_hidden(sK1,X15)
        | ~ sP5(sK3,sK2,X15)
        | ~ m1_subset_1(k4_xboole_0(X15,sK2),sK0)
        | ~ sP5(sK3,sK2,X16)
        | ~ sP5(sK1,sK2,X16)
        | ~ m1_subset_1(k4_xboole_0(X16,sK2),sK0)
        | ~ r2_hidden(k4_xboole_0(X16,sK2),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_624])])).

fof(f17912,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(k4_xboole_0(X15,sK2),X16)
      | ~ r2_hidden(k4_xboole_0(X16,sK2),X15)
      | ~ m1_subset_1(k4_xboole_0(X16,sK2),sK0)
      | ~ sP5(sK1,sK2,X16)
      | ~ sP5(sK3,sK2,X16)
      | ~ m1_subset_1(k4_xboole_0(X15,sK2),sK0)
      | ~ sP5(sK3,sK2,X15)
      | r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK1,X15) ) ),
    inference(resolution,[],[f8751,f4910])).

fof(f4910,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_xboole_0(X2,X3),sK2)
      | ~ m1_subset_1(k4_xboole_0(X2,X3),sK0)
      | ~ sP5(sK3,X3,X2)
      | r2_hidden(sK1,X3)
      | ~ r2_hidden(sK1,X2) ) ),
    inference(resolution,[],[f340,f2119])).

fof(f340,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_xboole_0(X9,X8),sK1)
      | ~ r2_hidden(k4_xboole_0(X9,X8),sK2)
      | ~ m1_subset_1(k4_xboole_0(X9,X8),sK0)
      | ~ sP5(sK3,X8,X9) ) ),
    inference(resolution,[],[f230,f32])).

fof(f17950,plain,
    ( spl8_20
    | spl8_622 ),
    inference(avatar_split_clause,[],[f17910,f17948,f137])).

fof(f17948,plain,
    ( spl8_622
  <=> ! [X11,X12] :
        ( ~ r2_hidden(k4_xboole_0(X11,sK2),X12)
        | ~ r2_hidden(sK2,X11)
        | ~ m1_subset_1(k4_xboole_0(X11,sK2),sK0)
        | ~ sP5(sK3,sK1,X12)
        | ~ sP5(sK1,sK1,X12)
        | ~ m1_subset_1(k4_xboole_0(X12,sK1),sK0)
        | ~ r2_hidden(k4_xboole_0(X12,sK1),X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_622])])).

fof(f17910,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_xboole_0(X11,sK2),X12)
      | ~ r2_hidden(k4_xboole_0(X12,sK1),X11)
      | ~ m1_subset_1(k4_xboole_0(X12,sK1),sK0)
      | ~ sP5(sK1,sK1,X12)
      | ~ sP5(sK3,sK1,X12)
      | ~ m1_subset_1(k4_xboole_0(X11,sK2),sK0)
      | r2_hidden(sK2,sK2)
      | ~ r2_hidden(sK2,X11) ) ),
    inference(resolution,[],[f8751,f4400])).

fof(f4400,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_xboole_0(X3,X4),sK1)
      | ~ m1_subset_1(k4_xboole_0(X3,X4),sK0)
      | r2_hidden(sK2,X4)
      | ~ r2_hidden(sK2,X3) ) ),
    inference(resolution,[],[f30,f2119])).

fof(f17871,plain,
    ( spl8_620
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f17867,f1211,f649,f17869])).

fof(f17869,plain,
    ( spl8_620
  <=> ! [X25,X24] : ~ r2_hidden(sK4(k1_xboole_0,X25,sK3),k4_xboole_0(sK1,X24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_620])])).

fof(f17867,plain,
    ( ! [X24,X25] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X25,sK3),k4_xboole_0(sK1,X24)) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f17843,f3648])).

fof(f17843,plain,
    ( ! [X24,X25] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X25,sK3),k4_xboole_0(sK1,X24))
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X24)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8931,f3648])).

fof(f8931,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X9,k4_xboole_0(X10,X11)),X11)
      | k4_xboole_0(X10,X11) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f8930])).

fof(f8930,plain,(
    ! [X10,X11,X9] :
      ( k4_xboole_0(X10,X11) = k1_xboole_0
      | ~ r2_hidden(sK4(k1_xboole_0,X9,k4_xboole_0(X10,X11)),X11)
      | k4_xboole_0(X10,X11) = k1_xboole_0 ) ),
    inference(forward_demodulation,[],[f8928,f50])).

fof(f8928,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X9,k4_xboole_0(X10,X11)),X11)
      | k4_xboole_0(X10,X11) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X10,X11) ) ),
    inference(duplicate_literal_removal,[],[f8896])).

fof(f8896,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X9,k4_xboole_0(X10,X11)),X11)
      | k4_xboole_0(X10,X11) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X10,X11)
      | ~ r2_hidden(sK4(k1_xboole_0,X9,k4_xboole_0(X10,X11)),X11) ) ),
    inference(resolution,[],[f2989,f1513])).

fof(f2989,plain,(
    ! [X54,X52,X55,X53] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X52,k4_xboole_0(X53,X54)),X55)
      | ~ r2_hidden(sK4(k1_xboole_0,X52,k4_xboole_0(X53,X54)),X54)
      | k4_xboole_0(X53,X54) = k1_xboole_0 ) ),
    inference(forward_demodulation,[],[f2967,f50])).

fof(f2967,plain,(
    ! [X54,X52,X55,X53] :
      ( k4_xboole_0(k1_xboole_0,X52) = k4_xboole_0(X53,X54)
      | ~ r2_hidden(sK4(k1_xboole_0,X52,k4_xboole_0(X53,X54)),X54)
      | ~ r2_hidden(sK4(k1_xboole_0,X52,k4_xboole_0(X53,X54)),X55) ) ),
    inference(resolution,[],[f1513,f270])).

fof(f17866,plain,
    ( spl8_156
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f17865,f1211,f649,f3202])).

fof(f3202,plain,
    ( spl8_156
  <=> ! [X19] : ~ r2_hidden(sK4(k1_xboole_0,X19,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f17865,plain,
    ( ! [X23] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X23,sK3),sK1) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f17842,f1212])).

fof(f17842,plain,
    ( ! [X23] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X23,sK3),sK1)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8931,f1212])).

fof(f17864,plain,
    ( spl8_618
    | spl8_192
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f17860,f1211,f5043,f17862])).

fof(f17862,plain,
    ( spl8_618
  <=> ! [X20,X21] : ~ r2_hidden(sK4(k1_xboole_0,X21,sK1),k4_xboole_0(sK3,X20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_618])])).

fof(f17860,plain,
    ( ! [X21,X20] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK1),k4_xboole_0(sK3,X20)) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f17840,f5148])).

fof(f17840,plain,
    ( ! [X21,X20] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X21,sK1),k4_xboole_0(sK3,X20))
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X20)) = k1_xboole_0 )
    | ~ spl8_116 ),
    inference(superposition,[],[f8931,f5148])).

fof(f17859,plain,
    ( spl8_616
    | spl8_192
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f17855,f1040,f5043,f17857])).

fof(f17857,plain,
    ( spl8_616
  <=> ! [X19] : ~ r2_hidden(sK4(k1_xboole_0,X19,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_616])])).

fof(f17855,plain,
    ( ! [X19] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(sK4(k1_xboole_0,X19,sK1),sK3) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f17839,f1041])).

fof(f17839,plain,
    ( ! [X19] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X19,sK1),sK3)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0 )
    | ~ spl8_106 ),
    inference(superposition,[],[f8931,f1041])).

fof(f17715,plain,
    ( spl8_166
    | spl8_614
    | ~ spl8_230 ),
    inference(avatar_split_clause,[],[f17711,f6272,f17713,f4339])).

fof(f6272,plain,
    ( spl8_230
  <=> ! [X8] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | ~ r2_hidden(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK1)
        | ~ m1_subset_1(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_230])])).

fof(f17711,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3)) )
    | ~ spl8_230 ),
    inference(duplicate_literal_removal,[],[f17703])).

fof(f17703,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3)) )
    | ~ spl8_230 ),
    inference(resolution,[],[f6273,f55])).

fof(f6273,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | ~ m1_subset_1(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X8)) )
    | ~ spl8_230 ),
    inference(avatar_component_clause,[],[f6272])).

fof(f17502,plain,
    ( spl8_612
    | spl8_192
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f17498,f1040,f5043,f17500])).

fof(f17500,plain,
    ( spl8_612
  <=> ! [X18,X17] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X18,sK1),sK3)
        | sP5(sK4(k1_xboole_0,X18,sK1),X17,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_612])])).

fof(f17498,plain,
    ( ! [X17,X18] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(sK4(k1_xboole_0,X18,sK1),sK3)
        | sP5(sK4(k1_xboole_0,X18,sK1),X17,k1_xboole_0) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f17497,f50])).

fof(f17497,plain,
    ( ! [X17,X18] :
        ( k4_xboole_0(k1_xboole_0,X18) = sK1
        | ~ r2_hidden(sK4(k1_xboole_0,X18,sK1),sK3)
        | sP5(sK4(k1_xboole_0,X18,sK1),X17,k1_xboole_0) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f17496,f50])).

fof(f17496,plain,
    ( ! [X17,X18] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X18,sK1),sK3)
        | sP5(sK4(k1_xboole_0,X18,sK1),X17,k1_xboole_0)
        | k4_xboole_0(k4_xboole_0(k1_xboole_0,X17),X18) = sK1 )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f17464,f50])).

fof(f17464,plain,
    ( ! [X17,X18] :
        ( sP5(sK4(k1_xboole_0,X18,sK1),X17,k1_xboole_0)
        | ~ r2_hidden(sK4(k4_xboole_0(k1_xboole_0,X17),X18,sK1),sK3)
        | k4_xboole_0(k4_xboole_0(k1_xboole_0,X17),X18) = sK1 )
    | ~ spl8_106 ),
    inference(superposition,[],[f11127,f50])).

fof(f11127,plain,
    ( ! [X26,X24,X25] :
        ( sP5(sK4(k4_xboole_0(X24,X25),X26,sK1),X25,X24)
        | ~ r2_hidden(sK4(k4_xboole_0(X24,X25),X26,sK1),sK3)
        | k4_xboole_0(k4_xboole_0(X24,X25),X26) = sK1 )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f11126,f1041])).

fof(f11126,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK4(k4_xboole_0(X24,X25),X26,sK1),sK3)
        | sP5(sK4(k4_xboole_0(X24,X25),X26,sK1),X25,X24)
        | k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(X24,X25),X26) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f11069,f1041])).

fof(f11069,plain,
    ( ! [X26,X24,X25] :
        ( sP5(sK4(k4_xboole_0(X24,X25),X26,sK1),X25,X24)
        | ~ r2_hidden(sK4(k4_xboole_0(X24,X25),X26,k4_xboole_0(sK1,sK3)),sK3)
        | k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(X24,X25),X26) )
    | ~ spl8_106 ),
    inference(superposition,[],[f2964,f1041])).

fof(f17365,plain,
    ( ~ spl8_611
    | spl8_121
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f17296,f6161,f1256,f17363])).

fof(f17363,plain,
    ( spl8_611
  <=> ~ r2_hidden(sK4(sK3,sK1,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_611])])).

fof(f1256,plain,
    ( spl8_121
  <=> ~ r2_hidden(sK4(sK3,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).

fof(f17296,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,sK3),k1_xboole_0)
    | ~ spl8_121
    | ~ spl8_216 ),
    inference(resolution,[],[f17168,f1257])).

fof(f1257,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,sK3),sK1)
    | ~ spl8_121 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f17358,plain,
    ( ~ spl8_609
    | spl8_113
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f17277,f6161,f1110,f17356])).

fof(f17356,plain,
    ( spl8_609
  <=> ~ r2_hidden(sK4(sK1,sK3,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_609])])).

fof(f1110,plain,
    ( spl8_113
  <=> ~ r2_hidden(sK4(sK1,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f17277,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,sK1),k1_xboole_0)
    | ~ spl8_113
    | ~ spl8_216 ),
    inference(resolution,[],[f17168,f1111])).

fof(f1111,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f17351,plain,
    ( ~ spl8_607
    | ~ spl8_216
    | spl8_427 ),
    inference(avatar_split_clause,[],[f17275,f13201,f6161,f17349])).

fof(f17349,plain,
    ( spl8_607
  <=> ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_607])])).

fof(f13201,plain,
    ( spl8_427
  <=> ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_427])])).

fof(f17275,plain,
    ( ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_427 ),
    inference(resolution,[],[f17168,f13202])).

fof(f13202,plain,
    ( ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl8_427 ),
    inference(avatar_component_clause,[],[f13201])).

fof(f16963,plain,
    ( spl8_40
    | spl8_604 ),
    inference(avatar_split_clause,[],[f16922,f16961,f211])).

fof(f16961,plain,
    ( spl8_604
  <=> ! [X16,X15] :
        ( ~ r2_hidden(k4_xboole_0(X15,sK1),X16)
        | ~ r2_hidden(sK1,X15)
        | ~ sP5(sK3,sK1,X15)
        | ~ m1_subset_1(k4_xboole_0(X15,sK1),sK0)
        | ~ sP5(sK2,sK2,X16)
        | ~ m1_subset_1(k4_xboole_0(X16,sK2),sK0)
        | ~ r2_hidden(k4_xboole_0(X16,sK2),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_604])])).

fof(f16922,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(k4_xboole_0(X15,sK1),X16)
      | ~ r2_hidden(k4_xboole_0(X16,sK2),X15)
      | ~ m1_subset_1(k4_xboole_0(X16,sK2),sK0)
      | ~ sP5(sK2,sK2,X16)
      | ~ m1_subset_1(k4_xboole_0(X15,sK1),sK0)
      | ~ sP5(sK3,sK1,X15)
      | r2_hidden(sK1,sK1)
      | ~ r2_hidden(sK1,X15) ) ),
    inference(resolution,[],[f8750,f4910])).

fof(f16959,plain,
    ( spl8_16
    | spl8_602 ),
    inference(avatar_split_clause,[],[f16920,f16957,f124])).

fof(f16957,plain,
    ( spl8_602
  <=> ! [X11,X12] :
        ( ~ r2_hidden(k4_xboole_0(X11,sK1),X12)
        | ~ r2_hidden(sK2,X11)
        | ~ m1_subset_1(k4_xboole_0(X11,sK1),sK0)
        | ~ sP5(sK2,sK1,X12)
        | ~ m1_subset_1(k4_xboole_0(X12,sK1),sK0)
        | ~ r2_hidden(k4_xboole_0(X12,sK1),X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_602])])).

fof(f16920,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_xboole_0(X11,sK1),X12)
      | ~ r2_hidden(k4_xboole_0(X12,sK1),X11)
      | ~ m1_subset_1(k4_xboole_0(X12,sK1),sK0)
      | ~ sP5(sK2,sK1,X12)
      | ~ m1_subset_1(k4_xboole_0(X11,sK1),sK0)
      | r2_hidden(sK2,sK1)
      | ~ r2_hidden(sK2,X11) ) ),
    inference(resolution,[],[f8750,f4400])).

fof(f16716,plain,
    ( spl8_598
    | ~ spl8_601
    | ~ spl8_576 ),
    inference(avatar_split_clause,[],[f16699,f16065,f16714,f16708])).

fof(f16708,plain,
    ( spl8_598
  <=> k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_598])])).

fof(f16714,plain,
    ( spl8_601
  <=> ~ r1_tarski(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_601])])).

fof(f16065,plain,
    ( spl8_576
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_576])])).

fof(f16699,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),k1_xboole_0)
    | k4_xboole_0(sK2,sK3) = k1_xboole_0
    | ~ spl8_576 ),
    inference(resolution,[],[f16066,f48])).

fof(f16066,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK3))
    | ~ spl8_576 ),
    inference(avatar_component_clause,[],[f16065])).

fof(f16683,plain,
    ( spl8_594
    | ~ spl8_597
    | ~ spl8_578 ),
    inference(avatar_split_clause,[],[f16669,f16073,f16681,f16675])).

fof(f16675,plain,
    ( spl8_594
  <=> k1_xboole_0 = sK7(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_594])])).

fof(f16681,plain,
    ( spl8_597
  <=> ~ r1_tarski(sK7(k1_zfmisc_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_597])])).

fof(f16073,plain,
    ( spl8_578
  <=> r1_tarski(k1_xboole_0,sK7(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_578])])).

fof(f16669,plain,
    ( ~ r1_tarski(sK7(k1_zfmisc_1(sK0)),k1_xboole_0)
    | k1_xboole_0 = sK7(k1_zfmisc_1(sK0))
    | ~ spl8_578 ),
    inference(resolution,[],[f16074,f48])).

fof(f16074,plain,
    ( r1_tarski(k1_xboole_0,sK7(k1_zfmisc_1(sK0)))
    | ~ spl8_578 ),
    inference(avatar_component_clause,[],[f16073])).

fof(f16657,plain,
    ( ~ spl8_591
    | spl8_592
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f16644,f6161,f16655,f16649])).

fof(f16649,plain,
    ( spl8_591
  <=> ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_591])])).

fof(f16644,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK1)),sK0)
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f16635,f6162])).

fof(f16635,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK1)),sK0)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f16612])).

fof(f16612,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k4_xboole_0(sK1,sK1)),sK0)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f6899,f3016])).

fof(f16592,plain,
    ( ~ spl8_589
    | spl8_582
    | ~ spl8_585
    | ~ spl8_587 ),
    inference(avatar_split_clause,[],[f16561,f16583,f16577,f16571,f16590])).

fof(f16590,plain,
    ( spl8_589
  <=> ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_589])])).

fof(f16577,plain,
    ( spl8_585
  <=> ~ r2_hidden(sK3,sK4(sK2,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_585])])).

fof(f16561,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k1_xboole_0))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f16550])).

fof(f16550,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK3,sK4(sK2,sK1,k1_xboole_0))
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f4669,f4199])).

fof(f4669,plain,(
    ! [X45] :
      ( ~ r2_hidden(sK4(X45,sK1,k1_xboole_0),sK2)
      | ~ m1_subset_1(sK4(X45,sK1,k1_xboole_0),sK0)
      | ~ r2_hidden(sK3,sK4(X45,sK1,k1_xboole_0))
      | k4_xboole_0(X45,sK1) = k1_xboole_0 ) ),
    inference(resolution,[],[f119,f2217])).

fof(f16585,plain,
    ( spl8_580
    | spl8_582
    | ~ spl8_585
    | ~ spl8_587 ),
    inference(avatar_split_clause,[],[f16563,f16583,f16577,f16571,f16565])).

fof(f16565,plain,
    ( spl8_580
  <=> ! [X0] : ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_580])])).

fof(f16563,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0)
      | ~ r2_hidden(sK3,sK4(sK2,sK1,k1_xboole_0))
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),X0) ) ),
    inference(duplicate_literal_removal,[],[f16548])).

fof(f16548,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK2,sK1,k1_xboole_0),sK0)
      | ~ r2_hidden(sK3,sK4(sK2,sK1,k1_xboole_0))
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | k4_xboole_0(sK2,sK1) = k1_xboole_0
      | ~ r2_hidden(sK4(sK2,sK1,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f4669,f419])).

fof(f16171,plain,
    ( spl8_192
    | ~ spl8_575
    | ~ spl8_570 ),
    inference(avatar_split_clause,[],[f16169,f15887,f15989,f5043])).

fof(f15989,plain,
    ( spl8_575
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_575])])).

fof(f15887,plain,
    ( spl8_570
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_570])])).

fof(f16169,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl8_570 ),
    inference(resolution,[],[f15888,f48])).

fof(f15888,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl8_570 ),
    inference(avatar_component_clause,[],[f15887])).

fof(f16075,plain,
    ( spl8_578
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(avatar_split_clause,[],[f16059,f6336,f6161,f16073])).

fof(f16059,plain,
    ( r1_tarski(k1_xboole_0,sK7(k1_zfmisc_1(sK0)))
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(resolution,[],[f15197,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',existence_m1_subset_1)).

fof(f16068,plain,
    ( spl8_570
    | ~ spl8_0
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(avatar_split_clause,[],[f16053,f6336,f6161,f67,f15887])).

fof(f67,plain,
    ( spl8_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f16053,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl8_0
    | ~ spl8_216
    | ~ spl8_234 ),
    inference(resolution,[],[f15197,f68])).

fof(f68,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f16067,plain,
    ( spl8_576
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_418 ),
    inference(avatar_split_clause,[],[f16051,f13080,f6336,f6161,f16065])).

fof(f13080,plain,
    ( spl8_418
  <=> m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_418])])).

fof(f16051,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK3))
    | ~ spl8_216
    | ~ spl8_234
    | ~ spl8_418 ),
    inference(resolution,[],[f15197,f13081])).

fof(f13081,plain,
    ( m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ spl8_418 ),
    inference(avatar_component_clause,[],[f13080])).

fof(f15994,plain,
    ( spl8_572
    | spl8_574
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15984,f6161,f15992,f15986])).

fof(f15986,plain,
    ( spl8_572
  <=> ! [X193] :
        ( ~ r2_hidden(sK2,sK6(X193,sK1,k1_xboole_0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X193)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_572])])).

fof(f15984,plain,
    ( ! [X193] :
        ( r1_tarski(sK1,k1_xboole_0)
        | ~ r2_hidden(sK2,sK6(X193,sK1,k1_xboole_0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X193)) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15696,f6162])).

fof(f15696,plain,
    ( ! [X193] :
        ( ~ r2_hidden(sK2,sK6(X193,sK1,k1_xboole_0))
        | r1_tarski(sK1,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X193)) )
    | ~ spl8_216 ),
    inference(superposition,[],[f3468,f6162])).

fof(f15889,plain,
    ( spl8_568
    | spl8_570
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15659,f6161,f15887,f15881])).

fof(f15881,plain,
    ( spl8_568
  <=> ! [X123] : ~ m1_subset_1(sK1,k1_zfmisc_1(X123)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_568])])).

fof(f15659,plain,
    ( ! [X123] :
        ( r1_tarski(k1_xboole_0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X123)) )
    | ~ spl8_216 ),
    inference(superposition,[],[f1946,f6162])).

fof(f1946,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k4_xboole_0(X4,X6),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f1935])).

fof(f1935,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r1_tarski(k4_xboole_0(X4,X6),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f1456,f245])).

fof(f1456,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k4_xboole_0(X3,X4),k1_zfmisc_1(X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | r1_tarski(k4_xboole_0(X3,X4),X3) ) ),
    inference(duplicate_literal_removal,[],[f1441])).

fof(f1441,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k4_xboole_0(X3,X4),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(k4_xboole_0(X3,X4),k1_zfmisc_1(X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(k4_xboole_0(X3,X4),k1_zfmisc_1(X5))
      | r1_tarski(k4_xboole_0(X3,X4),X3) ) ),
    inference(resolution,[],[f444,f56])).

fof(f15828,plain,
    ( spl8_566
    | spl8_76
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15824,f6161,f649,f15826])).

fof(f15826,plain,
    ( spl8_566
  <=> ! [X66] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X66,sK3),sK1)
        | sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1)
        | ~ m1_subset_1(sK4(k1_xboole_0,X66,sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_566])])).

fof(f15824,plain,
    ( ! [X66] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X66,sK3),sK1)
        | ~ m1_subset_1(sK4(k1_xboole_0,X66,sK3),sK0)
        | sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15823,f50])).

fof(f15823,plain,
    ( ! [X66] :
        ( k4_xboole_0(k1_xboole_0,X66) = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X66,sK3),sK1)
        | ~ m1_subset_1(sK4(k1_xboole_0,X66,sK3),sK0)
        | sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1) )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15822,f6162])).

fof(f15822,plain,
    ( ! [X66] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X66,sK3),sK1)
        | ~ m1_subset_1(sK4(k1_xboole_0,X66,sK3),sK0)
        | sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X66) = sK3 )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15821,f6162])).

fof(f15821,plain,
    ( ! [X66] :
        ( ~ m1_subset_1(sK4(k1_xboole_0,X66,sK3),sK0)
        | sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X66,sK3),sK1)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X66) = sK3 )
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15628,f6162])).

fof(f15628,plain,
    ( ! [X66] :
        ( sP5(sK4(k1_xboole_0,X66,sK3),sK2,sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X66,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X66,sK3),sK1)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X66) = sK3 )
    | ~ spl8_216 ),
    inference(superposition,[],[f634,f6162])).

fof(f634,plain,(
    ! [X8,X7,X9] :
      ( sP5(sK4(k4_xboole_0(X7,X8),X9,sK3),X8,X7)
      | ~ m1_subset_1(sK4(k4_xboole_0(X7,X8),X9,sK3),sK0)
      | ~ r2_hidden(sK4(k4_xboole_0(X7,X8),X9,sK3),sK1)
      | k4_xboole_0(k4_xboole_0(X7,X8),X9) = sK3 ) ),
    inference(resolution,[],[f421,f59])).

fof(f15785,plain,
    ( ~ spl8_563
    | spl8_564
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15772,f6161,f15783,f15777])).

fof(f15777,plain,
    ( spl8_563
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_563])])).

fof(f15783,plain,
    ( spl8_564
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_564])])).

fof(f15772,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_216 ),
    inference(forward_demodulation,[],[f15587,f6162])).

fof(f15587,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k4_xboole_0(sK1,sK2) = sK2
    | ~ spl8_216 ),
    inference(superposition,[],[f5818,f6162])).

fof(f5818,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k4_xboole_0(sK1,X0))
      | k4_xboole_0(sK1,X0) = sK2 ) ),
    inference(resolution,[],[f5769,f48])).

fof(f5769,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),sK2) ),
    inference(global_subsumption,[],[f36,f5762])).

fof(f5762,plain,(
    ! [X2] :
      ( r1_tarski(k4_xboole_0(sK1,X2),sK2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f5375,f245])).

fof(f5375,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(sK1,X0),sK2) ) ),
    inference(global_subsumption,[],[f35,f5374])).

fof(f5374,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK1,X0),sK2)
      | ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f5367])).

fof(f5367,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK1,X0),sK2)
      | ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(sK1,X0),sK2) ) ),
    inference(resolution,[],[f4710,f54])).

fof(f4710,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X2,k4_xboole_0(sK1,X1),sK2),sK0)
      | r1_tarski(k4_xboole_0(sK1,X1),sK2)
      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f4706])).

fof(f4706,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(sK1,X1),sK2)
      | ~ m1_subset_1(sK6(X2,k4_xboole_0(sK1,X1),sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(sK1,X1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f276,f444])).

fof(f276,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK6(X8,X9,sK2),sK1)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | r1_tarski(X9,sK2)
      | ~ m1_subset_1(sK6(X8,X9,sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f56,f30])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f15771,plain,
    ( spl8_560
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15586,f6161,f15769])).

fof(f15769,plain,
    ( spl8_560
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_560])])).

fof(f15586,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_216 ),
    inference(superposition,[],[f5769,f6162])).

fof(f15755,plain,
    ( ~ spl8_559
    | ~ spl8_178
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15581,f6161,f4580,f15753])).

fof(f15753,plain,
    ( spl8_559
  <=> ~ sP5(sK1,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_559])])).

fof(f4580,plain,
    ( spl8_178
  <=> ! [X103] : ~ sP5(sK1,k4_xboole_0(sK1,X103),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_178])])).

fof(f15581,plain,
    ( ~ sP5(sK1,k1_xboole_0,sK3)
    | ~ spl8_178
    | ~ spl8_216 ),
    inference(superposition,[],[f4581,f6162])).

fof(f4581,plain,
    ( ! [X103] : ~ sP5(sK1,k4_xboole_0(sK1,X103),sK3)
    | ~ spl8_178 ),
    inference(avatar_component_clause,[],[f4580])).

fof(f15746,plain,
    ( ~ spl8_557
    | ~ spl8_164
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15578,f6161,f4220,f15744])).

fof(f15744,plain,
    ( spl8_557
  <=> ~ sP5(sK3,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_557])])).

fof(f4220,plain,
    ( spl8_164
  <=> ! [X15] : ~ sP5(sK3,k4_xboole_0(sK1,X15),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_164])])).

fof(f15578,plain,
    ( ~ sP5(sK3,k1_xboole_0,sK3)
    | ~ spl8_164
    | ~ spl8_216 ),
    inference(superposition,[],[f4221,f6162])).

fof(f4221,plain,
    ( ! [X15] : ~ sP5(sK3,k4_xboole_0(sK1,X15),sK3)
    | ~ spl8_164 ),
    inference(avatar_component_clause,[],[f4220])).

fof(f15739,plain,
    ( ~ spl8_555
    | ~ spl8_160
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f15576,f6161,f3789,f15737])).

fof(f15737,plain,
    ( spl8_555
  <=> ~ sP5(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_555])])).

fof(f3789,plain,
    ( spl8_160
  <=> ! [X74] : ~ sP5(k1_xboole_0,k4_xboole_0(sK1,X74),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_160])])).

fof(f15576,plain,
    ( ~ sP5(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_160
    | ~ spl8_216 ),
    inference(superposition,[],[f3790,f6162])).

fof(f3790,plain,
    ( ! [X74] : ~ sP5(k1_xboole_0,k4_xboole_0(sK1,X74),sK3)
    | ~ spl8_160 ),
    inference(avatar_component_clause,[],[f3789])).

fof(f15378,plain,
    ( ~ spl8_553
    | ~ spl8_216
    | spl8_395 ),
    inference(avatar_split_clause,[],[f15233,f10006,f6161,f15376])).

fof(f15376,plain,
    ( spl8_553
  <=> ~ r2_hidden(sK2,sK4(sK1,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_553])])).

fof(f10006,plain,
    ( spl8_395
  <=> ~ r2_hidden(sK2,sK4(sK1,sK3,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_395])])).

fof(f15233,plain,
    ( ~ r2_hidden(sK2,sK4(sK1,sK3,k1_xboole_0))
    | ~ spl8_216
    | ~ spl8_395 ),
    inference(backward_demodulation,[],[f6162,f10007])).

fof(f10007,plain,
    ( ~ r2_hidden(sK2,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_395 ),
    inference(avatar_component_clause,[],[f10006])).

fof(f15369,plain,
    ( ~ spl8_551
    | ~ spl8_216
    | spl8_359 ),
    inference(avatar_split_clause,[],[f15226,f8525,f6161,f15367])).

fof(f15367,plain,
    ( spl8_551
  <=> ~ r2_hidden(sK3,sK4(sK1,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_551])])).

fof(f8525,plain,
    ( spl8_359
  <=> ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_359])])).

fof(f15226,plain,
    ( ~ r2_hidden(sK3,sK4(sK1,sK3,k1_xboole_0))
    | ~ spl8_216
    | ~ spl8_359 ),
    inference(backward_demodulation,[],[f6162,f8526])).

fof(f8526,plain,
    ( ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_359 ),
    inference(avatar_component_clause,[],[f8525])).

fof(f15362,plain,
    ( ~ spl8_549
    | ~ spl8_216
    | spl8_357 ),
    inference(avatar_split_clause,[],[f15225,f8431,f6161,f15360])).

fof(f15360,plain,
    ( spl8_549
  <=> ~ r2_hidden(k1_xboole_0,sK4(sK1,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_549])])).

fof(f8431,plain,
    ( spl8_357
  <=> ~ r2_hidden(k4_xboole_0(sK1,sK2),sK4(sK1,sK3,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_357])])).

fof(f15225,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(sK1,sK3,k1_xboole_0))
    | ~ spl8_216
    | ~ spl8_357 ),
    inference(backward_demodulation,[],[f6162,f8432])).

fof(f8432,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_357 ),
    inference(avatar_component_clause,[],[f8431])).

fof(f15355,plain,
    ( spl8_546
    | ~ spl8_216
    | ~ spl8_352 ),
    inference(avatar_split_clause,[],[f15224,f8271,f6161,f15353])).

fof(f8271,plain,
    ( spl8_352
  <=> r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_352])])).

fof(f15224,plain,
    ( r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK2)
    | ~ spl8_216
    | ~ spl8_352 ),
    inference(backward_demodulation,[],[f6162,f8272])).

fof(f8272,plain,
    ( r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_352 ),
    inference(avatar_component_clause,[],[f8271])).

fof(f15348,plain,
    ( ~ spl8_545
    | ~ spl8_216
    | spl8_351 ),
    inference(avatar_split_clause,[],[f15223,f8268,f6161,f15346])).

fof(f15346,plain,
    ( spl8_545
  <=> ~ m1_subset_1(sK4(sK1,sK3,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_545])])).

fof(f8268,plain,
    ( spl8_351
  <=> ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_351])])).

fof(f15223,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3,k1_xboole_0),sK0)
    | ~ spl8_216
    | ~ spl8_351 ),
    inference(backward_demodulation,[],[f6162,f8269])).

fof(f8269,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl8_351 ),
    inference(avatar_component_clause,[],[f8268])).

fof(f15341,plain,
    ( spl8_542
    | ~ spl8_216
    | ~ spl8_348 ),
    inference(avatar_split_clause,[],[f15222,f8262,f6161,f15339])).

fof(f8262,plain,
    ( spl8_348
  <=> r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_348])])).

fof(f15222,plain,
    ( r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK1)
    | ~ spl8_216
    | ~ spl8_348 ),
    inference(backward_demodulation,[],[f6162,f8263])).

fof(f8263,plain,
    ( r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_348 ),
    inference(avatar_component_clause,[],[f8262])).

fof(f15334,plain,
    ( ~ spl8_541
    | ~ spl8_216
    | spl8_347 ),
    inference(avatar_split_clause,[],[f15221,f8147,f6161,f15332])).

fof(f15332,plain,
    ( spl8_541
  <=> ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_541])])).

fof(f8147,plain,
    ( spl8_347
  <=> ~ sP5(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_347])])).

fof(f15221,plain,
    ( ~ sP5(sK4(sK1,sK3,k1_xboole_0),sK2,sK1)
    | ~ spl8_216
    | ~ spl8_347 ),
    inference(backward_demodulation,[],[f6162,f8148])).

fof(f8148,plain,
    ( ~ sP5(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl8_347 ),
    inference(avatar_component_clause,[],[f8147])).

fof(f15327,plain,
    ( ~ spl8_539
    | ~ spl8_216
    | spl8_345 ),
    inference(avatar_split_clause,[],[f15220,f8140,f6161,f15325])).

fof(f15325,plain,
    ( spl8_539
  <=> ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_539])])).

fof(f8140,plain,
    ( spl8_345
  <=> ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_345])])).

fof(f15220,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),sK3)
    | ~ spl8_216
    | ~ spl8_345 ),
    inference(backward_demodulation,[],[f6162,f8141])).

fof(f8141,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK3)
    | ~ spl8_345 ),
    inference(avatar_component_clause,[],[f8140])).

fof(f15320,plain,
    ( spl8_94
    | ~ spl8_216
    | ~ spl8_336 ),
    inference(avatar_split_clause,[],[f15218,f7481,f6161,f770])).

fof(f770,plain,
    ( spl8_94
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f7481,plain,
    ( spl8_336
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).

fof(f15218,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl8_216
    | ~ spl8_336 ),
    inference(backward_demodulation,[],[f6162,f7482])).

fof(f7482,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ spl8_336 ),
    inference(avatar_component_clause,[],[f7481])).

fof(f15319,plain,
    ( ~ spl8_97
    | ~ spl8_216
    | spl8_329 ),
    inference(avatar_split_clause,[],[f15214,f7437,f6161,f779])).

fof(f779,plain,
    ( spl8_97
  <=> ~ r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f7437,plain,
    ( spl8_329
  <=> ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_329])])).

fof(f15214,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_329 ),
    inference(backward_demodulation,[],[f6162,f7438])).

fof(f7438,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_329 ),
    inference(avatar_component_clause,[],[f7437])).

fof(f15313,plain,
    ( ~ spl8_537
    | ~ spl8_216
    | spl8_281 ),
    inference(avatar_split_clause,[],[f15207,f6681,f6161,f15311])).

fof(f15311,plain,
    ( spl8_537
  <=> ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_537])])).

fof(f6681,plain,
    ( spl8_281
  <=> ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_281])])).

fof(f15207,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_281 ),
    inference(backward_demodulation,[],[f6162,f6682])).

fof(f6682,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl8_281 ),
    inference(avatar_component_clause,[],[f6681])).

fof(f15306,plain,
    ( ~ spl8_535
    | ~ spl8_216
    | spl8_271 ),
    inference(avatar_split_clause,[],[f15206,f6658,f6161,f15304])).

fof(f15304,plain,
    ( spl8_535
  <=> ~ r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_535])])).

fof(f6658,plain,
    ( spl8_271
  <=> ~ r2_hidden(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_271])])).

fof(f15206,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl8_216
    | ~ spl8_271 ),
    inference(backward_demodulation,[],[f6162,f6659])).

fof(f6659,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl8_271 ),
    inference(avatar_component_clause,[],[f6658])).

fof(f15299,plain,
    ( spl8_58
    | ~ spl8_216
    | ~ spl8_258 ),
    inference(avatar_split_clause,[],[f15204,f6627,f6161,f331])).

fof(f331,plain,
    ( spl8_58
  <=> r2_hidden(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f6627,plain,
    ( spl8_258
  <=> r2_hidden(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_258])])).

fof(f15204,plain,
    ( r2_hidden(k1_xboole_0,sK2)
    | ~ spl8_216
    | ~ spl8_258 ),
    inference(backward_demodulation,[],[f6162,f6628])).

fof(f6628,plain,
    ( r2_hidden(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl8_258 ),
    inference(avatar_component_clause,[],[f6627])).

fof(f15298,plain,
    ( spl8_52
    | ~ spl8_216
    | ~ spl8_246 ),
    inference(avatar_split_clause,[],[f15201,f6596,f6161,f303])).

fof(f303,plain,
    ( spl8_52
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f6596,plain,
    ( spl8_246
  <=> r2_hidden(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_246])])).

fof(f15201,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_216
    | ~ spl8_246 ),
    inference(backward_demodulation,[],[f6162,f6597])).

fof(f6597,plain,
    ( r2_hidden(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl8_246 ),
    inference(avatar_component_clause,[],[f6596])).

fof(f15294,plain,
    ( spl8_82
    | ~ spl8_216
    | ~ spl8_232 ),
    inference(avatar_split_clause,[],[f15196,f6330,f6161,f701])).

fof(f701,plain,
    ( spl8_82
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f6330,plain,
    ( spl8_232
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_232])])).

fof(f15196,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_216
    | ~ spl8_232 ),
    inference(backward_demodulation,[],[f6162,f6331])).

fof(f6331,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_232 ),
    inference(avatar_component_clause,[],[f6330])).

fof(f15193,plain,
    ( spl8_216
    | spl8_526
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f15069,f13870,f14989,f6161])).

fof(f14989,plain,
    ( spl8_526
  <=> ! [X98,X99] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X98,k4_xboole_0(sK1,sK2)),X99)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X98,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_526])])).

fof(f15069,plain,
    ( ! [X45,X44] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X44,k4_xboole_0(sK1,sK2)),X45)
        | k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X44,k4_xboole_0(sK1,sK2))) )
    | ~ spl8_436 ),
    inference(resolution,[],[f14902,f1889])).

fof(f15192,plain,
    ( spl8_520
    | spl8_216
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f15191,f13870,f13399,f6161,f14961])).

fof(f14961,plain,
    ( spl8_520
  <=> ! [X65,X67,X66] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X66)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X67) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_520])])).

fof(f13399,plain,
    ( spl8_434
  <=> ! [X8] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_434])])).

fof(f15191,plain,
    ( ! [X24,X23,X22] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X22,k1_xboole_0),X23)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X22,k1_xboole_0),X24) )
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(forward_demodulation,[],[f15061,f13400])).

fof(f13400,plain,
    ( ! [X8] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X8)
    | ~ spl8_434 ),
    inference(avatar_component_clause,[],[f13399])).

fof(f15061,plain,
    ( ! [X24,X23,X22] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X22,k1_xboole_0),X23)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X22,k1_xboole_0),X24)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X22) = k1_xboole_0 )
    | ~ spl8_436 ),
    inference(resolution,[],[f14902,f2245])).

fof(f2245,plain,(
    ! [X28,X26,X27,X25] :
      ( sP5(sK4(k4_xboole_0(X25,X26),X27,k1_xboole_0),X26,X25)
      | ~ r2_hidden(sK4(k4_xboole_0(X25,X26),X27,k1_xboole_0),X28)
      | k4_xboole_0(k4_xboole_0(X25,X26),X27) = k1_xboole_0 ) ),
    inference(resolution,[],[f419,f59])).

fof(f15190,plain,
    ( spl8_480
    | spl8_216
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f15189,f13399,f6161,f14033])).

fof(f14033,plain,
    ( spl8_480
  <=> ! [X201,X199,X200] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X201)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_480])])).

fof(f15189,plain,
    ( ! [X202,X200,X201] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X202)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X200,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f15188,f13400])).

fof(f15188,plain,
    ( ! [X202,X200,X201] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X201) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X202)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X200,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14517,f13400])).

fof(f14517,plain,
    ( ! [X202,X200,X201] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X202)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X200,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X200),X201) = k1_xboole_0 )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14328,f13400])).

fof(f14328,plain,
    ( ! [X202,X200,X201] :
        ( sP5(sK4(k4_xboole_0(sK1,sK2),X201,k1_xboole_0),X200,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X200),X201,k1_xboole_0),X202)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X200),X201) = k1_xboole_0 )
    | ~ spl8_434 ),
    inference(superposition,[],[f2245,f13400])).

fof(f15187,plain,
    ( spl8_216
    | spl8_472
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14500,f13399,f13999,f6161])).

fof(f13999,plain,
    ( spl8_472
  <=> ! [X181,X182] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)),X181,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_472])])).

fof(f14500,plain,
    ( ! [X182,X183] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X183,k4_xboole_0(sK1,sK2)))
        | k4_xboole_0(sK1,sK2) = k1_xboole_0
        | sP5(sK4(k1_xboole_0,X183,k4_xboole_0(sK1,sK2)),X182,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14499,f13400])).

fof(f14499,plain,
    ( ! [X182,X183] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | sP5(sK4(k1_xboole_0,X183,k4_xboole_0(sK1,sK2)),X182,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X183,k4_xboole_0(k4_xboole_0(sK1,sK2),X182))) )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14319,f13400])).

fof(f14319,plain,
    ( ! [X182,X183] :
        ( sP5(sK4(k1_xboole_0,X183,k4_xboole_0(sK1,sK2)),X182,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X182) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X183,k4_xboole_0(k4_xboole_0(sK1,sK2),X182))) )
    | ~ spl8_434 ),
    inference(superposition,[],[f1889,f13400])).

fof(f15186,plain,
    ( ~ spl8_53
    | spl8_144
    | spl8_171 ),
    inference(avatar_split_clause,[],[f4625,f4522,f2227,f306])).

fof(f2227,plain,
    ( spl8_144
  <=> r2_hidden(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f4625,plain,
    ( r2_hidden(k1_xboole_0,sK3)
    | ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_171 ),
    inference(resolution,[],[f4523,f37])).

fof(f4523,plain,
    ( ~ sP5(k1_xboole_0,sK3,sK1)
    | ~ spl8_171 ),
    inference(avatar_component_clause,[],[f4522])).

fof(f15185,plain,
    ( ~ spl8_53
    | ~ spl8_106
    | spl8_171 ),
    inference(avatar_split_clause,[],[f4712,f4522,f1040,f306])).

fof(f4712,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_106
    | ~ spl8_171 ),
    inference(resolution,[],[f4435,f4523])).

fof(f15182,plain,
    ( ~ spl8_53
    | spl8_58
    | spl8_339 ),
    inference(avatar_split_clause,[],[f7599,f7568,f331,f306])).

fof(f7568,plain,
    ( spl8_339
  <=> ~ sP5(k1_xboole_0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_339])])).

fof(f7599,plain,
    ( r2_hidden(k1_xboole_0,sK2)
    | ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_339 ),
    inference(resolution,[],[f7569,f37])).

fof(f7569,plain,
    ( ~ sP5(k1_xboole_0,sK2,sK1)
    | ~ spl8_339 ),
    inference(avatar_component_clause,[],[f7568])).

fof(f15181,plain,
    ( ~ spl8_533
    | spl8_216
    | ~ spl8_524 ),
    inference(avatar_split_clause,[],[f15180,f14974,f6161,f15175])).

fof(f15175,plain,
    ( spl8_533
  <=> ~ r2_hidden(k1_xboole_0,sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_533])])).

fof(f14974,plain,
    ( spl8_524
  <=> ! [X82] : ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0),X82) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_524])])).

fof(f15180,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0))
    | ~ spl8_524 ),
    inference(forward_demodulation,[],[f15159,f51])).

fof(f15159,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0))
    | ~ spl8_524 ),
    inference(resolution,[],[f14975,f416])).

fof(f14975,plain,
    ( ! [X82] : ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0),X82)
    | ~ spl8_524 ),
    inference(avatar_component_clause,[],[f14974])).

fof(f15178,plain,
    ( spl8_216
    | ~ spl8_524 ),
    inference(avatar_split_clause,[],[f15148,f14974,f6161])).

fof(f15148,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl8_524 ),
    inference(resolution,[],[f14975,f4188])).

fof(f4188,plain,(
    ! [X5] :
      ( r2_hidden(sK4(X5,k1_xboole_0,k1_xboole_0),X5)
      | k1_xboole_0 = X5 ) ),
    inference(forward_demodulation,[],[f4040,f51])).

fof(f4040,plain,(
    ! [X5] :
      ( k4_xboole_0(X5,k1_xboole_0) = k1_xboole_0
      | r2_hidden(sK4(X5,k1_xboole_0,k1_xboole_0),X5) ) ),
    inference(duplicate_literal_removal,[],[f4026])).

fof(f4026,plain,(
    ! [X5] :
      ( k4_xboole_0(X5,k1_xboole_0) = k1_xboole_0
      | k4_xboole_0(X5,k1_xboole_0) = k1_xboole_0
      | r2_hidden(sK4(X5,k1_xboole_0,k1_xboole_0),X5) ) ),
    inference(resolution,[],[f2217,f282])).

fof(f15177,plain,
    ( ~ spl8_533
    | spl8_216
    | ~ spl8_524 ),
    inference(avatar_split_clause,[],[f15170,f14974,f6161,f15175])).

fof(f15170,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0))
    | ~ spl8_524 ),
    inference(forward_demodulation,[],[f15147,f51])).

fof(f15147,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0))
    | ~ spl8_524 ),
    inference(resolution,[],[f14975,f3106])).

fof(f3106,plain,(
    ! [X23,X21,X22,X20] :
      ( r2_hidden(sK4(k4_xboole_0(X21,X22),X23,X20),X21)
      | k4_xboole_0(k4_xboole_0(X21,X22),X23) = X20
      | ~ r2_hidden(X20,sK4(k4_xboole_0(X21,X22),X23,X20)) ) ),
    inference(resolution,[],[f1230,f38])).

fof(f1230,plain,(
    ! [X21,X19,X20,X18] :
      ( sP5(sK4(k4_xboole_0(X18,X19),X20,X21),X19,X18)
      | ~ r2_hidden(X21,sK4(k4_xboole_0(X18,X19),X20,X21))
      | k4_xboole_0(k4_xboole_0(X18,X19),X20) = X21 ) ),
    inference(resolution,[],[f416,f59])).

fof(f15001,plain,
    ( spl8_334
    | ~ spl8_529
    | spl8_530
    | ~ spl8_116
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f14938,f13870,f1211,f14999,f14996,f7477])).

fof(f7477,plain,
    ( spl8_334
  <=> k4_xboole_0(sK1,sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_334])])).

fof(f14996,plain,
    ( spl8_529
  <=> ~ r2_hidden(sK3,sK4(sK3,sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_529])])).

fof(f14999,plain,
    ( spl8_530
  <=> ! [X103] : ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK2)),X103) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_530])])).

fof(f14938,plain,
    ( ! [X103] :
        ( ~ r2_hidden(sK4(sK3,sK1,k4_xboole_0(sK1,sK2)),X103)
        | ~ r2_hidden(sK3,sK4(sK3,sK1,k4_xboole_0(sK1,sK2)))
        | k4_xboole_0(sK1,sK2) = sK3 )
    | ~ spl8_116
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f2620])).

fof(f14991,plain,
    ( spl8_216
    | spl8_526
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f14935,f13870,f14989,f6161])).

fof(f14935,plain,
    ( ! [X99,X98] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X98,k4_xboole_0(sK1,sK2)),X99)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X98,k4_xboole_0(sK1,sK2)))
        | k4_xboole_0(sK1,sK2) = k1_xboole_0 )
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f428])).

fof(f14976,plain,
    ( spl8_216
    | spl8_524
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f14929,f13870,f14974,f6161])).

fof(f14929,plain,
    ( ! [X82] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),k1_xboole_0,k1_xboole_0),X82)
        | k4_xboole_0(sK1,sK2) = k1_xboole_0 )
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f4188])).

fof(f14968,plain,
    ( spl8_522
    | spl8_334
    | ~ spl8_116
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f14964,f13870,f13399,f1211,f7477,f14966])).

fof(f14966,plain,
    ( spl8_522
  <=> ! [X71,X70] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),X71)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_522])])).

fof(f14964,plain,
    ( ! [X70,X71] :
        ( k4_xboole_0(sK1,sK2) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),X71)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),sK1) )
    | ~ spl8_116
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(forward_demodulation,[],[f14925,f13400])).

fof(f14925,plain,
    ( ! [X70,X71] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),X71)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X70) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X70,sK3),sK1) )
    | ~ spl8_116
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f2577])).

fof(f14963,plain,
    ( spl8_520
    | spl8_216
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(avatar_split_clause,[],[f14959,f13870,f13399,f6161,f14961])).

fof(f14959,plain,
    ( ! [X66,X67,X65] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X66)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X67) )
    | ~ spl8_434
    | ~ spl8_436 ),
    inference(forward_demodulation,[],[f14923,f13400])).

fof(f14923,plain,
    ( ! [X66,X67,X65] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X66)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X65) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X65,k1_xboole_0),X67) )
    | ~ spl8_436 ),
    inference(resolution,[],[f14713,f419])).

fof(f14851,plain,
    ( ~ spl8_519
    | spl8_517 ),
    inference(avatar_split_clause,[],[f14840,f14831,f14849])).

fof(f14849,plain,
    ( spl8_519
  <=> ~ sP5(k4_xboole_0(sK1,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_519])])).

fof(f14831,plain,
    ( spl8_517
  <=> ~ r2_hidden(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_517])])).

fof(f14840,plain,
    ( ~ sP5(k4_xboole_0(sK1,sK2),sK2,sK1)
    | ~ spl8_517 ),
    inference(resolution,[],[f14832,f60])).

fof(f14832,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl8_517 ),
    inference(avatar_component_clause,[],[f14831])).

fof(f14833,plain,
    ( spl8_320
    | ~ spl8_517
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14826,f13399,f14831,f7152])).

fof(f7152,plain,
    ( spl8_320
  <=> ! [X2] : r2_hidden(k4_xboole_0(sK1,sK2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_320])])).

fof(f14826,plain,
    ( ! [X10] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
        | r2_hidden(k4_xboole_0(sK1,sK2),X10) )
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14808,f13400])).

fof(f14808,plain,
    ( ! [X10] :
        ( r2_hidden(k4_xboole_0(sK1,sK2),X10)
        | ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X10),k4_xboole_0(sK1,sK2)) )
    | ~ spl8_434 ),
    inference(superposition,[],[f8789,f13400])).

fof(f14821,plain,
    ( spl8_42
    | spl8_514 ),
    inference(avatar_split_clause,[],[f14790,f14819,f217])).

fof(f14819,plain,
    ( spl8_514
  <=> ! [X9] :
        ( ~ r2_hidden(k4_xboole_0(X9,sK2),X9)
        | ~ r2_hidden(sK1,X9)
        | ~ sP5(sK3,sK2,X9)
        | ~ m1_subset_1(k4_xboole_0(X9,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_514])])).

fof(f14790,plain,(
    ! [X9] :
      ( ~ r2_hidden(k4_xboole_0(X9,sK2),X9)
      | ~ m1_subset_1(k4_xboole_0(X9,sK2),sK0)
      | ~ sP5(sK3,sK2,X9)
      | r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK1,X9) ) ),
    inference(resolution,[],[f8789,f4910])).

fof(f14817,plain,
    ( spl8_16
    | spl8_512 ),
    inference(avatar_split_clause,[],[f14788,f14815,f124])).

fof(f14815,plain,
    ( spl8_512
  <=> ! [X7] :
        ( ~ r2_hidden(k4_xboole_0(X7,sK1),X7)
        | ~ r2_hidden(sK2,X7)
        | ~ m1_subset_1(k4_xboole_0(X7,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_512])])).

fof(f14788,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_xboole_0(X7,sK1),X7)
      | ~ m1_subset_1(k4_xboole_0(X7,sK1),sK0)
      | r2_hidden(sK2,sK1)
      | ~ r2_hidden(sK2,X7) ) ),
    inference(resolution,[],[f8789,f4400])).

fof(f14200,plain,
    ( spl8_448
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14199,f13399,f6457,f6333,f13904])).

fof(f13904,plain,
    ( spl8_448
  <=> ! [X67,X66,X68] :
        ( k4_xboole_0(X67,k4_xboole_0(sK1,sK2)) = X68
        | sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X68)
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X67) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_448])])).

fof(f6333,plain,
    ( spl8_233
  <=> ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_233])])).

fof(f6457,plain,
    ( spl8_238
  <=> ! [X6] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X6),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_238])])).

fof(f14199,plain,
    ( ! [X23,X21,X20] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X21)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X23)
        | k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14198,f13400])).

fof(f14198,plain,
    ( ! [X23,X21,X20] :
        ( ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X21)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X23)
        | k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14197,f13400])).

fof(f14197,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(sK1,sK2),X22),X23),X21)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X23)
        | k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14196,f13400])).

fof(f14196,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r2_hidden(sK4(X21,k4_xboole_0(sK1,sK2),X23),X23)
        | k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14195,f13400])).

fof(f14195,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(sK1,sK2),X22),X23),X23)
        | k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14194,f13400])).

fof(f14194,plain,
    ( ! [X23,X21,X22,X20] :
        ( k4_xboole_0(X21,k4_xboole_0(sK1,sK2)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X23)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14193,f13400])).

fof(f14193,plain,
    ( ! [X23,X21,X22,X20] :
        ( k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(sK1,sK2),X22)) = X23
        | sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X23)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13827,f13400])).

fof(f13827,plain,
    ( ! [X23,X21,X22,X20] :
        ( sP5(sK4(X21,k4_xboole_0(sK1,sK2),X23),X20,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22)) = X23
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X23)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12707])).

fof(f12707,plain,
    ( ! [X23,X21,X22,X20] :
        ( sP5(sK4(X21,k4_xboole_0(k4_xboole_0(sK1,sK2),X22),X23),X20,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22)) = X23
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X23)
        | ~ r2_hidden(sK4(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),X22),X23),X21)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X20),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3575,f6458])).

fof(f6458,plain,
    ( ! [X6] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X6)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X6),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(avatar_component_clause,[],[f6457])).

fof(f3575,plain,(
    ! [X66,X64,X67,X65,X63] :
      ( sP5(sK4(X63,k4_xboole_0(k4_xboole_0(X64,X65),X66),X67),X65,X64)
      | k4_xboole_0(X63,k4_xboole_0(k4_xboole_0(X64,X65),X66)) = X67
      | ~ r2_hidden(sK4(X63,k4_xboole_0(k4_xboole_0(X64,X65),X66),X67),X67)
      | ~ r2_hidden(sK4(X63,k4_xboole_0(k4_xboole_0(X64,X65),X66),X67),X63) ) ),
    inference(resolution,[],[f1716,f59])).

fof(f14192,plain,
    ( spl8_510
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14188,f13399,f6457,f6333,f14190])).

fof(f14190,plain,
    ( spl8_510
  <=> ! [X338,X337] :
        ( ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X337)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X338)
        | k4_xboole_0(X338,k4_xboole_0(sK1,sK2)) = sK1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_510])])).

fof(f14188,plain,
    ( ! [X337,X338] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X337)
        | k4_xboole_0(X338,k4_xboole_0(sK1,sK2)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X338)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14187,f13400])).

fof(f14187,plain,
    ( ! [X337,X338] :
        ( ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X337)
        | k4_xboole_0(X338,k4_xboole_0(sK1,sK2)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X338)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14186,f13400])).

fof(f14186,plain,
    ( ! [X337,X338] :
        ( k4_xboole_0(X338,k4_xboole_0(sK1,sK2)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X338)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X337)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14185,f13400])).

fof(f14185,plain,
    ( ! [X337,X338] :
        ( ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),X338)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | k4_xboole_0(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X337)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14184,f13400])).

fof(f14184,plain,
    ( ! [X337,X338] :
        ( ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X338)
        | k4_xboole_0(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X337)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13825,f13400])).

fof(f13825,plain,
    ( ! [X337,X338] :
        ( ~ m1_subset_1(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK0)
        | ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1))
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X338)
        | k4_xboole_0(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X337)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12602])).

fof(f12602,plain,
    ( ! [X337,X338] :
        ( ~ r2_hidden(sK4(X338,k4_xboole_0(sK1,sK2),sK1),sK2)
        | ~ m1_subset_1(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),sK0)
        | ~ r2_hidden(sK3,sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1))
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X338)
        | k4_xboole_0(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337)) = sK1
        | ~ r2_hidden(sK4(X338,k4_xboole_0(k4_xboole_0(sK1,sK2),X337),sK1),X337)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X337),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4677,f6458])).

fof(f4677,plain,(
    ! [X61,X59,X60] :
      ( ~ r2_hidden(sK4(X59,k4_xboole_0(X60,X61),sK1),sK2)
      | ~ m1_subset_1(sK4(X59,k4_xboole_0(X60,X61),sK1),sK0)
      | ~ r2_hidden(sK3,sK4(X59,k4_xboole_0(X60,X61),sK1))
      | ~ r2_hidden(sK4(X59,k4_xboole_0(X60,X61),sK1),X59)
      | k4_xboole_0(X59,k4_xboole_0(X60,X61)) = sK1
      | ~ r2_hidden(sK4(X59,k4_xboole_0(X60,X61),sK1),X61) ) ),
    inference(resolution,[],[f119,f1715])).

fof(f1715,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(sK4(X16,k4_xboole_0(X17,X18),X19),X19)
      | ~ r2_hidden(sK4(X16,k4_xboole_0(X17,X18),X19),X16)
      | k4_xboole_0(X16,k4_xboole_0(X17,X18)) = X19
      | ~ r2_hidden(sK4(X16,k4_xboole_0(X17,X18),X19),X18) ) ),
    inference(resolution,[],[f431,f39])).

fof(f14183,plain,
    ( spl8_508
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14179,f13399,f6457,f6333,f14181])).

fof(f14181,plain,
    ( spl8_508
  <=> ! [X334,X333] :
        ( ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X333)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X334)
        | k4_xboole_0(X334,k4_xboole_0(sK1,sK2)) = sK3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_508])])).

fof(f14179,plain,
    ( ! [X333,X334] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X333)
        | k4_xboole_0(X334,k4_xboole_0(sK1,sK2)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X334)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14178,f13400])).

fof(f14178,plain,
    ( ! [X333,X334] :
        ( ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X333)
        | k4_xboole_0(X334,k4_xboole_0(sK1,sK2)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X334)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14177,f13400])).

fof(f14177,plain,
    ( ! [X333,X334] :
        ( k4_xboole_0(X334,k4_xboole_0(sK1,sK2)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X334)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X333)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14176,f13400])).

fof(f14176,plain,
    ( ! [X333,X334] :
        ( ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),X334)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | k4_xboole_0(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X333)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14175,f13400])).

fof(f14175,plain,
    ( ! [X333,X334] :
        ( ~ r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X334)
        | k4_xboole_0(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X333)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13824,f13400])).

fof(f13824,plain,
    ( ! [X333,X334] :
        ( ~ m1_subset_1(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK0)
        | r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),sK2)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X334)
        | k4_xboole_0(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X333)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12600])).

fof(f12600,plain,
    ( ! [X333,X334] :
        ( r2_hidden(sK4(X334,k4_xboole_0(sK1,sK2),sK3),sK1)
        | ~ m1_subset_1(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),sK0)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),sK2)
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X334)
        | k4_xboole_0(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333)) = sK3
        | ~ r2_hidden(sK4(X334,k4_xboole_0(k4_xboole_0(sK1,sK2),X333),sK3),X333)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X333),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4606,f6458])).

fof(f4606,plain,(
    ! [X33,X31,X32] :
      ( r2_hidden(sK4(X31,k4_xboole_0(X32,X33),sK3),sK1)
      | ~ m1_subset_1(sK4(X31,k4_xboole_0(X32,X33),sK3),sK0)
      | ~ r2_hidden(sK4(X31,k4_xboole_0(X32,X33),sK3),sK2)
      | ~ r2_hidden(sK4(X31,k4_xboole_0(X32,X33),sK3),X31)
      | k4_xboole_0(X31,k4_xboole_0(X32,X33)) = sK3
      | ~ r2_hidden(sK4(X31,k4_xboole_0(X32,X33),sK3),X33) ) ),
    inference(resolution,[],[f32,f1715])).

fof(f14174,plain,
    ( spl8_506
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14170,f13399,f6457,f6333,f14172])).

fof(f14172,plain,
    ( spl8_506
  <=> ! [X328,X329] :
        ( ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X328)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X329)
        | k4_xboole_0(X329,k4_xboole_0(sK1,sK2)) = sK2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_506])])).

fof(f14170,plain,
    ( ! [X329,X328] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X328)
        | k4_xboole_0(X329,k4_xboole_0(sK1,sK2)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X329)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14169,f13400])).

fof(f14169,plain,
    ( ! [X329,X328] :
        ( ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X328)
        | k4_xboole_0(X329,k4_xboole_0(sK1,sK2)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X329)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X328),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14168,f13400])).

fof(f14168,plain,
    ( ! [X329,X328] :
        ( k4_xboole_0(X329,k4_xboole_0(sK1,sK2)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X329)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X328)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X328),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14167,f13400])).

fof(f14167,plain,
    ( ! [X329,X328] :
        ( ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),X329)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | k4_xboole_0(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X328)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X328),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13823,f13400])).

fof(f13823,plain,
    ( ! [X329,X328] :
        ( ~ m1_subset_1(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X329)
        | k4_xboole_0(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X328)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X328),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12597])).

fof(f12597,plain,
    ( ! [X329,X328] :
        ( ~ r2_hidden(sK4(X329,k4_xboole_0(sK1,sK2),sK2),sK1)
        | ~ m1_subset_1(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),sK0)
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X329)
        | k4_xboole_0(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328)) = sK2
        | ~ r2_hidden(sK4(X329,k4_xboole_0(k4_xboole_0(sK1,sK2),X328),sK2),X328)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X328),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4414,f6458])).

fof(f4414,plain,(
    ! [X28,X29,X27] :
      ( ~ r2_hidden(sK4(X27,k4_xboole_0(X28,X29),sK2),sK1)
      | ~ m1_subset_1(sK4(X27,k4_xboole_0(X28,X29),sK2),sK0)
      | ~ r2_hidden(sK4(X27,k4_xboole_0(X28,X29),sK2),X27)
      | k4_xboole_0(X27,k4_xboole_0(X28,X29)) = sK2
      | ~ r2_hidden(sK4(X27,k4_xboole_0(X28,X29),sK2),X29) ) ),
    inference(resolution,[],[f30,f1715])).

fof(f14162,plain,
    ( spl8_504
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14158,f13399,f6457,f6333,f14160])).

fof(f14160,plain,
    ( spl8_504
  <=> ! [X317,X318,X316,X315] :
        ( ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X316))
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316))
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X318)
        | r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_504])])).

fof(f14158,plain,
    ( ! [X315,X316,X318,X317] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X316))
        | r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X318)
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14157,f13400])).

fof(f14157,plain,
    ( ! [X315,X316,X318,X317] :
        ( ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X316))
        | r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X318)
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X315),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14156,f13400])).

fof(f14156,plain,
    ( ! [X315,X316,X318,X317] :
        ( r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X318)
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316))
        | ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315)),k1_zfmisc_1(X316))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X315),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13820,f13400])).

fof(f13820,plain,
    ( ! [X315,X316,X318,X317] :
        ( ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X318)
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316))
        | r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315)))
        | ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315)),k1_zfmisc_1(X316))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X315),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12592])).

fof(f12592,plain,
    ( ! [X315,X316,X318,X317] :
        ( ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(sK1,sK2))),X315)
        | ~ m1_subset_1(X317,k1_zfmisc_1(X316))
        | ~ r2_hidden(sK6(X316,X317,k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315))),X318)
        | r1_tarski(X317,k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315)))
        | ~ m1_subset_1(k4_xboole_0(X318,k4_xboole_0(k4_xboole_0(sK1,sK2),X315)),k1_zfmisc_1(X316))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X315),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3831,f6458])).

fof(f3831,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ r2_hidden(sK6(X23,X24,k4_xboole_0(X20,k4_xboole_0(X21,X22))),X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ r2_hidden(sK6(X23,X24,k4_xboole_0(X20,k4_xboole_0(X21,X22))),X20)
      | r1_tarski(X24,k4_xboole_0(X20,k4_xboole_0(X21,X22)))
      | ~ m1_subset_1(k4_xboole_0(X20,k4_xboole_0(X21,X22)),k1_zfmisc_1(X23)) ) ),
    inference(resolution,[],[f1668,f39])).

fof(f1668,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( sP5(sK6(X22,X18,k4_xboole_0(X19,k4_xboole_0(X20,X21))),X21,X20)
      | ~ m1_subset_1(k4_xboole_0(X19,k4_xboole_0(X20,X21)),k1_zfmisc_1(X22))
      | ~ m1_subset_1(X18,k1_zfmisc_1(X22))
      | ~ r2_hidden(sK6(X22,X18,k4_xboole_0(X19,k4_xboole_0(X20,X21))),X19)
      | r1_tarski(X18,k4_xboole_0(X19,k4_xboole_0(X20,X21))) ) ),
    inference(resolution,[],[f466,f59])).

fof(f14150,plain,
    ( spl8_502
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14146,f13399,f6457,f6333,f14148])).

fof(f14148,plain,
    ( spl8_502
  <=> ! [X305,X306] :
        ( k4_xboole_0(X306,k4_xboole_0(sK1,sK2)) = X306
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X305)
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X306) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_502])])).

fof(f14146,plain,
    ( ! [X306,X305] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(X306,k4_xboole_0(sK1,sK2)) = X306
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X306)
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X305) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14145,f13400])).

fof(f14145,plain,
    ( ! [X306,X305] :
        ( k4_xboole_0(X306,k4_xboole_0(sK1,sK2)) = X306
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X306)
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X305)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X305),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13817,f13400])).

fof(f13817,plain,
    ( ! [X306,X305] :
        ( ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X306)
        | ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X305)
        | k4_xboole_0(X306,k4_xboole_0(k4_xboole_0(sK1,sK2),X305)) = X306
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X305),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12588])).

fof(f12588,plain,
    ( ! [X306,X305] :
        ( ~ r2_hidden(sK4(X306,k4_xboole_0(sK1,sK2),X306),X305)
        | k4_xboole_0(X306,k4_xboole_0(k4_xboole_0(sK1,sK2),X305)) = X306
        | ~ r2_hidden(sK4(X306,k4_xboole_0(k4_xboole_0(sK1,sK2),X305),X306),X306)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X305),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3524,f6458])).

fof(f3524,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,k4_xboole_0(X1,X2),X0),X2)
      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
      | ~ r2_hidden(sK4(X0,k4_xboole_0(X1,X2),X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f3487])).

fof(f3487,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,k4_xboole_0(X1,X2),X0),X0)
      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
      | ~ r2_hidden(sK4(X0,k4_xboole_0(X1,X2),X0),X2)
      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0 ) ),
    inference(resolution,[],[f1715,f422])).

fof(f14144,plain,
    ( spl8_500
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14140,f13399,f6457,f6333,f14142])).

fof(f14142,plain,
    ( spl8_500
  <=> ! [X303,X304,X302] :
        ( ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X303)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X302)
        | k4_xboole_0(X303,k4_xboole_0(sK1,sK2)) = X304 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_500])])).

fof(f14140,plain,
    ( ! [X302,X304,X303] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X303)
        | k4_xboole_0(X303,k4_xboole_0(sK1,sK2)) = X304
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X302)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14139,f13400])).

fof(f14139,plain,
    ( ! [X302,X304,X303] :
        ( ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X303)
        | k4_xboole_0(X303,k4_xboole_0(sK1,sK2)) = X304
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X302)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X302),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14138,f13400])).

fof(f14138,plain,
    ( ! [X302,X304,X303] :
        ( k4_xboole_0(X303,k4_xboole_0(sK1,sK2)) = X304
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X302)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302),X304),X303)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X302),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13816,f13400])).

fof(f13816,plain,
    ( ! [X302,X304,X303] :
        ( ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),X302)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302)) = X304
        | ~ r2_hidden(sK4(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302),X304),X303)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X302),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12587])).

fof(f12587,plain,
    ( ! [X302,X304,X303] :
        ( ~ r2_hidden(sK4(X303,k4_xboole_0(sK1,sK2),X304),k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302)) = X304
        | ~ r2_hidden(sK4(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302),X304),X302)
        | ~ r2_hidden(sK4(X303,k4_xboole_0(k4_xboole_0(sK1,sK2),X302),X304),X303)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X302),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3519,f6458])).

fof(f3519,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),k4_xboole_0(X20,X21))
      | k4_xboole_0(X19,k4_xboole_0(X20,X21)) = X22
      | ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),X21)
      | ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),X19) ) ),
    inference(duplicate_literal_removal,[],[f3492])).

fof(f3492,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),X19)
      | k4_xboole_0(X19,k4_xboole_0(X20,X21)) = X22
      | ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),X21)
      | k4_xboole_0(X19,k4_xboole_0(X20,X21)) = X22
      | ~ r2_hidden(sK4(X19,k4_xboole_0(X20,X21),X22),k4_xboole_0(X20,X21)) ) ),
    inference(resolution,[],[f1715,f281])).

fof(f14137,plain,
    ( spl8_498
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14133,f13399,f6457,f6333,f14135])).

fof(f14135,plain,
    ( spl8_498
  <=> ! [X299,X301,X298,X300] :
        ( ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X299)
        | ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X301)
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X299,k4_xboole_0(X300,X301)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_498])])).

fof(f14133,plain,
    ( ! [X300,X298,X301,X299] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X299)
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X299,k4_xboole_0(X300,X301))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X301)
        | ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14132,f13400])).

fof(f14132,plain,
    ( ! [X300,X298,X301,X299] :
        ( ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X299)
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X299,k4_xboole_0(X300,X301))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X301)
        | ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X298),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14131,f13400])).

fof(f14131,plain,
    ( ! [X300,X298,X301,X299] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X299,k4_xboole_0(X300,X301))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X301)
        | ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(k4_xboole_0(sK1,sK2),X298)),X299)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X298),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13815,f13400])).

fof(f13815,plain,
    ( ! [X300,X298,X301,X299] :
        ( ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X301)
        | ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X298) = k4_xboole_0(X299,k4_xboole_0(X300,X301))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(k4_xboole_0(sK1,sK2),X298)),X299)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X298),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12586])).

fof(f12586,plain,
    ( ! [X300,X298,X301,X299] :
        ( ~ sP5(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(sK1,sK2)),X298,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X298) = k4_xboole_0(X299,k4_xboole_0(X300,X301))
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(k4_xboole_0(sK1,sK2),X298)),X301)
        | ~ r2_hidden(sK4(X299,k4_xboole_0(X300,X301),k4_xboole_0(k4_xboole_0(sK1,sK2),X298)),X299)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X298),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3503,f6458])).

fof(f3503,plain,(
    ! [X54,X52,X56,X55,X53] :
      ( ~ sP5(sK4(X52,k4_xboole_0(X53,X54),k4_xboole_0(X55,X56)),X56,X55)
      | k4_xboole_0(X55,X56) = k4_xboole_0(X52,k4_xboole_0(X53,X54))
      | ~ r2_hidden(sK4(X52,k4_xboole_0(X53,X54),k4_xboole_0(X55,X56)),X54)
      | ~ r2_hidden(sK4(X52,k4_xboole_0(X53,X54),k4_xboole_0(X55,X56)),X52) ) ),
    inference(resolution,[],[f1715,f60])).

fof(f14130,plain,
    ( spl8_496
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14126,f13399,f6457,f6333,f14128])).

fof(f14128,plain,
    ( spl8_496
  <=> ! [X297,X295,X296,X294] :
        ( ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X295)
        | ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296)
        | ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X294)
        | k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_496])])).

fof(f14126,plain,
    ( ! [X294,X296,X295,X297] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X295)
        | k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X294)
        | ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14125,f13400])).

fof(f14125,plain,
    ( ! [X294,X296,X295,X297] :
        ( ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X295)
        | k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X294)
        | ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14124,f13400])).

fof(f14124,plain,
    ( ! [X294,X296,X295,X297] :
        ( k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X294)
        | ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296)
        | ~ r2_hidden(sK4(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k4_xboole_0(X296,X297)),X295)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13814,f13400])).

fof(f13814,plain,
    ( ! [X294,X296,X295,X297] :
        ( ~ r2_hidden(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X294)
        | ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296)
        | k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k4_xboole_0(X296,X297)),X295)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12585])).

fof(f12585,plain,
    ( ! [X294,X296,X295,X297] :
        ( ~ sP5(sK4(X295,k4_xboole_0(sK1,sK2),k4_xboole_0(X296,X297)),X297,X296)
        | k4_xboole_0(X296,X297) = k4_xboole_0(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294))
        | ~ r2_hidden(sK4(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k4_xboole_0(X296,X297)),X294)
        | ~ r2_hidden(sK4(X295,k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k4_xboole_0(X296,X297)),X295)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X294),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3503,f6458])).

fof(f14119,plain,
    ( spl8_494
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14115,f13399,f6457,f6333,f14117])).

fof(f14117,plain,
    ( spl8_494
  <=> ! [X284,X283,X285,X282] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X283))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_494])])).

fof(f14115,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X283))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(sK1,sK2)))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14114,f13400])).

fof(f14114,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X283))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(sK1,sK2)))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14113,f13400])).

fof(f14113,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X285),k1_zfmisc_1(X283))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(sK1,sK2)))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14112,f13400])).

fof(f14112,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(sK1,sK2)))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14111,f13400])).

fof(f14111,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(k4_xboole_0(sK1,sK2),X285)))
        | r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14110,f13400])).

fof(f14110,plain,
    ( ! [X282,X285,X283,X284] :
        ( r1_tarski(X284,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14109,f13400])).

fof(f14109,plain,
    ( ! [X282,X285,X283,X284] :
        ( r1_tarski(X284,k4_xboole_0(k4_xboole_0(sK1,sK2),X285))
        | ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13811,f13400])).

fof(f13811,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ sP5(sK6(X283,X284,k4_xboole_0(sK1,sK2)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | r1_tarski(X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12581])).

fof(f12581,plain,
    ( ! [X282,X285,X283,X284] :
        ( ~ sP5(sK6(X283,X284,k4_xboole_0(k4_xboole_0(sK1,sK2),X285)),X282,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X284,k1_zfmisc_1(X283))
        | r1_tarski(X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285))
        | ~ r2_hidden(X285,sK6(X283,X284,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),X285),k1_zfmisc_1(X283))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X282),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3457,f6458])).

fof(f3457,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ sP5(sK6(X17,X18,k4_xboole_0(k4_xboole_0(X14,X15),X16)),X15,X14)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | r1_tarski(X18,k4_xboole_0(k4_xboole_0(X14,X15),X16))
      | ~ r2_hidden(X16,sK6(X17,X18,k4_xboole_0(k4_xboole_0(X14,X15),X16)))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(X14,X15),X16),k1_zfmisc_1(X17)) ) ),
    inference(resolution,[],[f1666,f60])).

fof(f14095,plain,
    ( spl8_492
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14091,f13399,f6457,f6333,f14093])).

fof(f14093,plain,
    ( spl8_492
  <=> ! [X256,X254,X257,X255] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_492])])).

fof(f14091,plain,
    ( ! [X255,X257,X254,X256] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X255))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14090,f13400])).

fof(f14090,plain,
    ( ! [X255,X257,X254,X256] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X255))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14089,f13400])).

fof(f14089,plain,
    ( ! [X255,X257,X254,X256] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X257),k1_zfmisc_1(X255))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14088,f13400])).

fof(f14088,plain,
    ( ! [X255,X257,X254,X256] :
        ( r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14087,f13400])).

fof(f14087,plain,
    ( ! [X255,X257,X254,X256] :
        ( r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(k4_xboole_0(sK1,sK2),X257))
        | ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13804,f13400])).

fof(f13804,plain,
    ( ! [X255,X257,X254,X256] :
        ( ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(sK1,sK2)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12573])).

fof(f12573,plain,
    ( ! [X255,X257,X254,X256] :
        ( ~ sP5(sK6(X255,k4_xboole_0(X256,X257),k4_xboole_0(k4_xboole_0(sK1,sK2),X257)),X254,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X256,X257),k1_zfmisc_1(X255))
        | r1_tarski(k4_xboole_0(X256,X257),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),X257),k1_zfmisc_1(X255))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X254),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3302,f6458])).

fof(f3302,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ sP5(sK6(X16,k4_xboole_0(X17,X15),k4_xboole_0(k4_xboole_0(X13,X14),X15)),X14,X13)
      | ~ m1_subset_1(k4_xboole_0(X17,X15),k1_zfmisc_1(X16))
      | r1_tarski(k4_xboole_0(X17,X15),k4_xboole_0(k4_xboole_0(X13,X14),X15))
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(X13,X14),X15),k1_zfmisc_1(X16)) ) ),
    inference(resolution,[],[f1680,f60])).

fof(f14085,plain,
    ( spl8_490
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14081,f13399,f6457,f6333,f14083])).

fof(f14083,plain,
    ( spl8_490
  <=> ! [X248,X250,X249] :
        ( k4_xboole_0(sK1,sK2) = X250
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248)
        | ~ r2_hidden(X250,sK4(k4_xboole_0(sK1,sK2),X249,X250)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_490])])).

fof(f14081,plain,
    ( ! [X249,X250,X248] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = X250
        | ~ r2_hidden(X250,sK4(k4_xboole_0(sK1,sK2),X249,X250))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14080,f13400])).

fof(f14080,plain,
    ( ! [X249,X250,X248] :
        ( k4_xboole_0(sK1,sK2) = X250
        | ~ r2_hidden(X250,sK4(k4_xboole_0(sK1,sK2),X249,X250))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14079,f13400])).

fof(f14079,plain,
    ( ! [X249,X250,X248] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X249) = X250
        | ~ r2_hidden(X250,sK4(k4_xboole_0(sK1,sK2),X249,X250))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13802,f13400])).

fof(f13802,plain,
    ( ! [X249,X250,X248] :
        ( ~ r2_hidden(X250,sK4(k4_xboole_0(sK1,sK2),X249,X250))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),X249) = X250
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12571])).

fof(f12571,plain,
    ( ! [X249,X250,X248] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X249,X250),X248)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),X249) = X250
        | ~ r2_hidden(X250,sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),X249,X250))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X248),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3105,f6458])).

fof(f3105,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X17,X18),X19,X16),X18)
      | k4_xboole_0(k4_xboole_0(X17,X18),X19) = X16
      | ~ r2_hidden(X16,sK4(k4_xboole_0(X17,X18),X19,X16)) ) ),
    inference(resolution,[],[f1230,f39])).

fof(f14076,plain,
    ( spl8_446
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14075,f13399,f6457,f6333,f13897])).

fof(f13897,plain,
    ( spl8_446
  <=> ! [X63,X65,X64] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X64,X65)
        | sP5(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X63,k4_xboole_0(sK1,sK2))
        | r2_hidden(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X64) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_446])])).

fof(f14075,plain,
    ( ! [X241,X239,X240] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X240,X241)
        | r2_hidden(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X240)
        | sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14074,f13400])).

fof(f14074,plain,
    ( ! [X241,X239,X240] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X240,X241)
        | r2_hidden(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X240)
        | sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14073,f13400])).

fof(f14073,plain,
    ( ! [X241,X239,X242,X240] :
        ( k4_xboole_0(X240,X241) = k4_xboole_0(k4_xboole_0(sK1,sK2),X242)
        | r2_hidden(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X240)
        | sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14072,f13400])).

fof(f14072,plain,
    ( ! [X241,X239,X242,X240] :
        ( r2_hidden(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X240)
        | sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X240,X241) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14071,f13400])).

fof(f14071,plain,
    ( ! [X241,X239,X242,X240] :
        ( r2_hidden(sK4(X240,X241,k4_xboole_0(k4_xboole_0(sK1,sK2),X242)),X240)
        | sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X240,X241) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13799,f13400])).

fof(f13799,plain,
    ( ! [X241,X239,X242,X240] :
        ( sP5(sK4(X240,X241,k4_xboole_0(sK1,sK2)),X239,k4_xboole_0(sK1,sK2))
        | r2_hidden(sK4(X240,X241,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)),X240)
        | k4_xboole_0(X240,X241) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12568])).

fof(f12568,plain,
    ( ! [X241,X239,X242,X240] :
        ( sP5(sK4(X240,X241,k4_xboole_0(k4_xboole_0(sK1,sK2),X242)),X239,k4_xboole_0(sK1,sK2))
        | r2_hidden(sK4(X240,X241,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)),X240)
        | k4_xboole_0(X240,X241) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),X242)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X239),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f3009,f6458])).

fof(f3009,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( sP5(sK4(X31,X32,k4_xboole_0(k4_xboole_0(X33,X34),X35)),X34,X33)
      | r2_hidden(sK4(X31,X32,k4_xboole_0(k4_xboole_0(X33,X34),X35)),X31)
      | k4_xboole_0(X31,X32) = k4_xboole_0(k4_xboole_0(X33,X34),X35) ) ),
    inference(resolution,[],[f1514,f59])).

fof(f14069,plain,
    ( spl8_488
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14065,f13399,f6457,f6333,f14067])).

fof(f14067,plain,
    ( spl8_488
  <=> ! [X232,X230,X229,X231] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X231,X232)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X232) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_488])])).

fof(f14065,plain,
    ( ! [X231,X229,X230,X232] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X231,X232)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X232)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14064,f13400])).

fof(f14064,plain,
    ( ! [X231,X229,X230,X232] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X231,X232)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X232)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14063,f13400])).

fof(f14063,plain,
    ( ! [X231,X229,X230,X232] :
        ( k4_xboole_0(X231,X232) = k4_xboole_0(k4_xboole_0(sK1,sK2),X230)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X232)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13797,f13400])).

fof(f13797,plain,
    ( ! [X231,X229,X230,X232] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X232)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X231,X232) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),X230)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12565])).

fof(f12565,plain,
    ( ! [X231,X229,X230,X232] :
        ( sP5(sK4(k4_xboole_0(sK1,sK2),X230,k4_xboole_0(X231,X232)),X229,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),X230,k4_xboole_0(X231,X232)),X232)
        | k4_xboole_0(X231,X232) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),X230)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X229),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2964,f6458])).

fof(f14062,plain,
    ( spl8_486
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14058,f13399,f6457,f6333,f14060])).

fof(f14060,plain,
    ( spl8_486
  <=> ! [X226,X228,X225,X227] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(X226,X227),X228)
        | sP5(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X227,X226)
        | ~ r2_hidden(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X225) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_486])])).

fof(f14058,plain,
    ( ! [X227,X225,X228,X226] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(X226,X227),X228)
        | ~ r2_hidden(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X225)
        | sP5(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X227,X226) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14057,f13400])).

fof(f14057,plain,
    ( ! [X227,X225,X228,X226] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(X226,X227),X228)
        | ~ r2_hidden(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X225)
        | sP5(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X227,X226)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X225),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13796,f13400])).

fof(f13796,plain,
    ( ! [X227,X225,X228,X226] :
        ( ~ r2_hidden(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X225)
        | sP5(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X227,X226)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X225) = k4_xboole_0(k4_xboole_0(X226,X227),X228)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X225),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12564])).

fof(f12564,plain,
    ( ! [X227,X225,X228,X226] :
        ( sP5(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(sK1,sK2)),X227,X226)
        | ~ r2_hidden(sK4(k4_xboole_0(X226,X227),X228,k4_xboole_0(k4_xboole_0(sK1,sK2),X225)),X225)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X225) = k4_xboole_0(k4_xboole_0(X226,X227),X228)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X225),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2964,f6458])).

fof(f14056,plain,
    ( spl8_484
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14052,f13399,f6457,f6333,f14054])).

fof(f14054,plain,
    ( spl8_484
  <=> ! [X224,X223,X222] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X223,X224)
        | ~ r2_hidden(sK4(X223,X224,k4_xboole_0(sK1,sK2)),X222)
        | ~ r2_hidden(X223,sK4(X223,X224,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_484])])).

fof(f14052,plain,
    ( ! [X222,X223,X224] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X223,X224)
        | ~ r2_hidden(X223,sK4(X223,X224,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X223,X224,k4_xboole_0(sK1,sK2)),X222) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14051,f13400])).

fof(f14051,plain,
    ( ! [X222,X223,X224] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X223,X224)
        | ~ r2_hidden(X223,sK4(X223,X224,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X223,X224,k4_xboole_0(sK1,sK2)),X222)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X222),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13795,f13400])).

fof(f13795,plain,
    ( ! [X222,X223,X224] :
        ( ~ r2_hidden(X223,sK4(X223,X224,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X223,X224,k4_xboole_0(sK1,sK2)),X222)
        | k4_xboole_0(X223,X224) = k4_xboole_0(k4_xboole_0(sK1,sK2),X222)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X222),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12563])).

fof(f12563,plain,
    ( ! [X222,X223,X224] :
        ( ~ r2_hidden(sK4(X223,X224,k4_xboole_0(sK1,sK2)),X222)
        | k4_xboole_0(X223,X224) = k4_xboole_0(k4_xboole_0(sK1,sK2),X222)
        | ~ r2_hidden(X223,sK4(X223,X224,k4_xboole_0(k4_xboole_0(sK1,sK2),X222)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X222),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2962,f6458])).

fof(f14050,plain,
    ( spl8_444
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14049,f13399,f6457,f6333,f13891])).

fof(f13891,plain,
    ( spl8_444
  <=> ! [X60,X62,X61] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X61,X62)
        | sP5(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X60,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X62) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_444])])).

fof(f14049,plain,
    ( ! [X218,X220,X219] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X219,X220)
        | ~ r2_hidden(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X220)
        | sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14048,f13400])).

fof(f14048,plain,
    ( ! [X218,X220,X219] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X219,X220)
        | ~ r2_hidden(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X220)
        | sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14047,f13400])).

fof(f14047,plain,
    ( ! [X218,X220,X219,X221] :
        ( k4_xboole_0(X219,X220) = k4_xboole_0(k4_xboole_0(sK1,sK2),X221)
        | ~ r2_hidden(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X220)
        | sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14046,f13400])).

fof(f14046,plain,
    ( ! [X218,X220,X219,X221] :
        ( ~ r2_hidden(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X220)
        | sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X219,X220) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14045,f13400])).

fof(f14045,plain,
    ( ! [X218,X220,X219,X221] :
        ( ~ r2_hidden(sK4(X219,X220,k4_xboole_0(k4_xboole_0(sK1,sK2),X221)),X220)
        | sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X219,X220) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13794,f13400])).

fof(f13794,plain,
    ( ! [X218,X220,X219,X221] :
        ( sP5(sK4(X219,X220,k4_xboole_0(sK1,sK2)),X218,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X219,X220,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)),X220)
        | k4_xboole_0(X219,X220) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12562])).

fof(f12562,plain,
    ( ! [X218,X220,X219,X221] :
        ( sP5(sK4(X219,X220,k4_xboole_0(k4_xboole_0(sK1,sK2),X221)),X218,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X219,X220,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)),X220)
        | k4_xboole_0(X219,X220) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),X221)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X218),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2916,f6458])).

fof(f2916,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( sP5(sK4(X31,X32,k4_xboole_0(k4_xboole_0(X33,X34),X35)),X34,X33)
      | ~ r2_hidden(sK4(X31,X32,k4_xboole_0(k4_xboole_0(X33,X34),X35)),X32)
      | k4_xboole_0(X31,X32) = k4_xboole_0(k4_xboole_0(X33,X34),X35) ) ),
    inference(resolution,[],[f1480,f59])).

fof(f14043,plain,
    ( spl8_482
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14039,f13399,f6457,f6333,f14041])).

fof(f14041,plain,
    ( spl8_482
  <=> ! [X209,X211,X210,X212] :
        ( k4_xboole_0(X210,X211) = k4_xboole_0(X212,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X209,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X211) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_482])])).

fof(f14039,plain,
    ( ! [X212,X210,X211,X209] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(X210,X211) = k4_xboole_0(X212,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X211)
        | ~ sP5(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X209,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14038,f13400])).

fof(f14038,plain,
    ( ! [X212,X210,X211,X209] :
        ( k4_xboole_0(X210,X211) = k4_xboole_0(X212,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X211)
        | ~ sP5(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X209,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X209),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13792,f13400])).

fof(f13792,plain,
    ( ! [X212,X210,X211,X209] :
        ( ~ r2_hidden(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X211)
        | ~ sP5(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X209,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X210,X211) = k4_xboole_0(X212,k4_xboole_0(k4_xboole_0(sK1,sK2),X209))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X209),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12559])).

fof(f12559,plain,
    ( ! [X212,X210,X211,X209] :
        ( ~ sP5(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(sK1,sK2))),X209,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X210,X211,k4_xboole_0(X212,k4_xboole_0(k4_xboole_0(sK1,sK2),X209))),X211)
        | k4_xboole_0(X210,X211) = k4_xboole_0(X212,k4_xboole_0(k4_xboole_0(sK1,sK2),X209))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X209),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2857,f6458])).

fof(f2857,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ sP5(sK4(X13,X14,k4_xboole_0(X15,k4_xboole_0(X16,X17))),X17,X16)
      | ~ r2_hidden(sK4(X13,X14,k4_xboole_0(X15,k4_xboole_0(X16,X17))),X14)
      | k4_xboole_0(X13,X14) = k4_xboole_0(X15,k4_xboole_0(X16,X17)) ) ),
    inference(resolution,[],[f1479,f60])).

fof(f14035,plain,
    ( spl8_480
    | spl8_216
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14031,f13399,f6457,f6333,f6161,f14033])).

fof(f14031,plain,
    ( ! [X200,X199,X201] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X201)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14030,f13400])).

fof(f14030,plain,
    ( ! [X200,X199,X201] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X201)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14029,f13400])).

fof(f14029,plain,
    ( ! [X200,X199,X201] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X200) = k1_xboole_0
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X201)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13788,f13400])).

fof(f13788,plain,
    ( ! [X200,X199,X201] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X201)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),X200) = k1_xboole_0
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12554])).

fof(f12554,plain,
    ( ! [X200,X199,X201] :
        ( sP5(sK4(k4_xboole_0(sK1,sK2),X200,k1_xboole_0),X199,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),X200,k1_xboole_0),X201)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),X200) = k1_xboole_0
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X199),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2245,f6458])).

fof(f14026,plain,
    ( spl8_334
    | spl8_478
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14022,f13399,f6457,f6333,f14024,f7477])).

fof(f14024,plain,
    ( spl8_478
  <=> ! [X190,X189] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),X189)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_478])])).

fof(f14022,plain,
    ( ! [X189,X190] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),X189)
        | k4_xboole_0(sK1,sK2) = sK3
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14021,f13400])).

fof(f14021,plain,
    ( ! [X189,X190] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),X189)
        | k4_xboole_0(sK1,sK2) = sK3
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14020,f13400])).

fof(f14020,plain,
    ( ! [X189,X190] :
        ( k4_xboole_0(sK1,sK2) = sK3
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190,sK3),X189)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14019,f13400])).

fof(f14019,plain,
    ( ! [X189,X190] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X190) = sK3
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190,sK3),X189)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13785,f13400])).

fof(f13785,plain,
    ( ! [X189,X190] :
        ( ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190,sK3),X189)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12549])).

fof(f12549,plain,
    ( ! [X189,X190] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X190,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190,sK3),sK0)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),X190,sK3),X189)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X189),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2072,f6458])).

fof(f2072,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X12,X13),X14,sK3),sK1)
      | ~ m1_subset_1(sK4(k4_xboole_0(X12,X13),X14,sK3),sK0)
      | k4_xboole_0(k4_xboole_0(X12,X13),X14) = sK3
      | ~ r2_hidden(sK4(k4_xboole_0(X12,X13),X14,sK3),X13) ) ),
    inference(resolution,[],[f634,f39])).

fof(f14018,plain,
    ( spl8_328
    | spl8_476
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14014,f13399,f6457,f6333,f14016,f7440])).

fof(f7440,plain,
    ( spl8_328
  <=> r1_tarski(sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).

fof(f14016,plain,
    ( spl8_476
  <=> ! [X188,X187] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X188))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_476])])).

fof(f14014,plain,
    ( ! [X187,X188] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14013,f13400])).

fof(f14013,plain,
    ( ! [X187,X188] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14012,f13400])).

fof(f14012,plain,
    ( ! [X187,X188] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14011,f13400])).

fof(f14011,plain,
    ( ! [X187,X188] :
        ( r1_tarski(sK3,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14010,f13400])).

fof(f14010,plain,
    ( ! [X187,X188] :
        ( r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14009,f13400])).

fof(f14009,plain,
    ( ! [X187,X188] :
        ( ~ sP5(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14008,f13400])).

fof(f14008,plain,
    ( ! [X187,X188] :
        ( ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(sK1,sK2)),sK0)
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13784,f13400])).

fof(f13784,plain,
    ( ! [X187,X188] :
        ( ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ sP5(sK6(X188,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12548])).

fof(f12548,plain,
    ( ! [X187,X188] :
        ( ~ sP5(sK6(X188,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),X187,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X188))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1))
        | ~ m1_subset_1(sK6(X188,sK3,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),sK1),k1_zfmisc_1(X188))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X187),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2037,f6458])).

fof(f2037,plain,(
    ! [X6,X4,X5] :
      ( ~ sP5(sK6(X6,sK3,k4_xboole_0(k4_xboole_0(X4,X5),sK1)),X5,X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(X4,X5),sK1))
      | ~ m1_subset_1(sK6(X6,sK3,k4_xboole_0(k4_xboole_0(X4,X5),sK1)),sK0)
      | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(X4,X5),sK1),k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f1679,f60])).

fof(f1679,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK6(X5,sK3,k4_xboole_0(X4,sK1)),X4)
      | ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | r1_tarski(sK3,k4_xboole_0(X4,sK1))
      | ~ m1_subset_1(sK6(X5,sK3,k4_xboole_0(X4,sK1)),sK0) ) ),
    inference(duplicate_literal_removal,[],[f1664])).

fof(f1664,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK3,k4_xboole_0(X4,sK1))
      | ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ r2_hidden(sK6(X5,sK3,k4_xboole_0(X4,sK1)),X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | r1_tarski(sK3,k4_xboole_0(X4,sK1))
      | ~ m1_subset_1(sK6(X5,sK3,k4_xboole_0(X4,sK1)),sK0)
      | ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f466,f266])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X1,sK3,X0),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | r1_tarski(sK3,X0)
      | ~ m1_subset_1(sK6(X1,sK3,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f55,f31])).

fof(f14007,plain,
    ( spl8_474
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f14003,f13399,f6457,f6333,f14005])).

fof(f14005,plain,
    ( spl8_474
  <=> ! [X183,X184] :
        ( k4_xboole_0(sK1,sK2) = X184
        | sP5(sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)),X183,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X184,sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_474])])).

fof(f14003,plain,
    ( ! [X184,X183] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = X184
        | ~ r2_hidden(X184,sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)),X183,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f14002,f13400])).

fof(f14002,plain,
    ( ! [X184,X183] :
        ( k4_xboole_0(sK1,sK2) = X184
        | ~ r2_hidden(X184,sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)),X183,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X183),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13783,f13400])).

fof(f13783,plain,
    ( ! [X184,X183] :
        ( ~ r2_hidden(X184,sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)),X183,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X183) = X184
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X183),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12546])).

fof(f12546,plain,
    ( ! [X184,X183] :
        ( sP5(sK4(X184,k1_xboole_0,k4_xboole_0(sK1,sK2)),X183,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X183) = X184
        | ~ r2_hidden(X184,sK4(X184,k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK2),X183)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X183),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1906,f6458])).

fof(f1906,plain,(
    ! [X14,X15,X16] :
      ( sP5(sK4(X14,k1_xboole_0,k4_xboole_0(X15,X16)),X16,X15)
      | k4_xboole_0(X15,X16) = X14
      | ~ r2_hidden(X14,sK4(X14,k1_xboole_0,k4_xboole_0(X15,X16))) ) ),
    inference(resolution,[],[f441,f59])).

fof(f441,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,k1_xboole_0,X6),X6)
      | ~ r2_hidden(X5,sK4(X5,k1_xboole_0,X6))
      | X5 = X6 ) ),
    inference(forward_demodulation,[],[f439,f51])).

fof(f439,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK4(X5,k1_xboole_0,X6))
      | r2_hidden(sK4(X5,k1_xboole_0,X6),X6)
      | k4_xboole_0(X5,k1_xboole_0) = X6 ) ),
    inference(resolution,[],[f342,f42])).

fof(f342,plain,(
    ! [X2,X3] :
      ( ~ sP5(X3,k1_xboole_0,X2)
      | ~ r2_hidden(X2,X3) ) ),
    inference(superposition,[],[f230,f51])).

fof(f14001,plain,
    ( spl8_472
    | spl8_216
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13997,f13399,f6457,f6333,f6161,f13999])).

fof(f13997,plain,
    ( ! [X182,X181] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)),X181,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13996,f13400])).

fof(f13996,plain,
    ( ! [X182,X181] :
        ( k4_xboole_0(sK1,sK2) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)),X181,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X181),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13782,f13400])).

fof(f13782,plain,
    ( ! [X182,X181] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)))
        | sP5(sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)),X181,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X181) = k1_xboole_0
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X181),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12545])).

fof(f12545,plain,
    ( ! [X182,X181] :
        ( sP5(sK4(k1_xboole_0,X182,k4_xboole_0(sK1,sK2)),X181,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X181) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X182,k4_xboole_0(k4_xboole_0(sK1,sK2),X181)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X181),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1889,f6458])).

fof(f13993,plain,
    ( spl8_470
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13989,f13399,f6457,f6333,f13991])).

fof(f13991,plain,
    ( spl8_470
  <=> ! [X176,X175,X177] :
        ( ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X175)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X176)
        | k4_xboole_0(X176,k4_xboole_0(sK1,sK2)) = X177 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_470])])).

fof(f13989,plain,
    ( ! [X177,X175,X176] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X175)
        | k4_xboole_0(X176,k4_xboole_0(sK1,sK2)) = X177
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X176)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13988,f13400])).

fof(f13988,plain,
    ( ! [X177,X175,X176] :
        ( ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X175)
        | k4_xboole_0(X176,k4_xboole_0(sK1,sK2)) = X177
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X176)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X175),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13987,f13400])).

fof(f13987,plain,
    ( ! [X177,X175,X176] :
        ( k4_xboole_0(X176,k4_xboole_0(sK1,sK2)) = X177
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X176)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175),X177),X175)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X175),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13780,f13400])).

fof(f13780,plain,
    ( ! [X177,X175,X176] :
        ( ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X176)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177)
        | k4_xboole_0(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175)) = X177
        | ~ r2_hidden(sK4(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175),X177),X175)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X175),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12543])).

fof(f12543,plain,
    ( ! [X177,X175,X176] :
        ( ~ r2_hidden(sK4(X176,k4_xboole_0(sK1,sK2),X177),X177)
        | ~ r2_hidden(sK4(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175),X177),X176)
        | k4_xboole_0(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175)) = X177
        | ~ r2_hidden(sK4(X176,k4_xboole_0(k4_xboole_0(sK1,sK2),X175),X177),X175)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X175),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1715,f6458])).

fof(f13984,plain,
    ( spl8_468
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13980,f13399,f6457,f6333,f13982])).

fof(f13982,plain,
    ( spl8_468
  <=> ! [X168,X166,X165,X167] :
        ( r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166))
        | sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X168)
        | ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X166)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_468])])).

fof(f13980,plain,
    ( ! [X167,X165,X166,X168] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X166))
        | ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X168)
        | sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13979,f13400])).

fof(f13979,plain,
    ( ! [X167,X165,X166,X168] :
        ( r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X166))
        | ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X168)
        | sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13978,f13400])).

fof(f13978,plain,
    ( ! [X167,X165,X166,X168] :
        ( ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X166))
        | ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X168)
        | sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166))
        | r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13777,f13400])).

fof(f13777,plain,
    ( ! [X167,X165,X166,X168] :
        ( ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X168)
        | sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165)),k1_zfmisc_1(X166))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166))
        | r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12540])).

fof(f12540,plain,
    ( ! [X167,X165,X166,X168] :
        ( sP5(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(sK1,sK2))),X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165)),k1_zfmisc_1(X166))
        | ~ m1_subset_1(X167,k1_zfmisc_1(X166))
        | ~ r2_hidden(sK6(X166,X167,k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165))),X168)
        | r1_tarski(X167,k4_xboole_0(X168,k4_xboole_0(k4_xboole_0(sK1,sK2),X165)))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1668,f6458])).

fof(f13974,plain,
    ( spl8_466
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13970,f13399,f6457,f6333,f13972])).

fof(f13972,plain,
    ( spl8_466
  <=> ! [X157,X156,X158] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X157,X158)
        | r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X157)
        | ~ r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X156) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_466])])).

fof(f13970,plain,
    ( ! [X158,X156,X157] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X157,X158)
        | ~ r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X156)
        | r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X157) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13969,f13400])).

fof(f13969,plain,
    ( ! [X158,X156,X157] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X157,X158)
        | ~ r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X156)
        | r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X157)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X156),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13774,f13400])).

fof(f13774,plain,
    ( ! [X158,X156,X157] :
        ( ~ r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X156)
        | r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X157)
        | k4_xboole_0(X157,X158) = k4_xboole_0(k4_xboole_0(sK1,sK2),X156)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X156),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12537])).

fof(f12537,plain,
    ( ! [X158,X156,X157] :
        ( r2_hidden(sK4(X157,X158,k4_xboole_0(sK1,sK2)),X157)
        | k4_xboole_0(X157,X158) = k4_xboole_0(k4_xboole_0(sK1,sK2),X156)
        | ~ r2_hidden(sK4(X157,X158,k4_xboole_0(k4_xboole_0(sK1,sK2),X156)),X156)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X156),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1513,f6458])).

fof(f13967,plain,
    ( spl8_464
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13963,f13399,f6457,f6333,f13965])).

fof(f13965,plain,
    ( spl8_464
  <=> ! [X150,X151,X152] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X151,X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X150)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X152) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_464])])).

fof(f13963,plain,
    ( ! [X152,X151,X150] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X151,X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X150) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13962,f13400])).

fof(f13962,plain,
    ( ! [X152,X151,X150] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X151,X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X150)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X150),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13772,f13400])).

fof(f13772,plain,
    ( ! [X152,X151,X150] :
        ( ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X152)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X150)
        | k4_xboole_0(X151,X152) = k4_xboole_0(k4_xboole_0(sK1,sK2),X150)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X150),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12535])).

fof(f12535,plain,
    ( ! [X152,X151,X150] :
        ( ~ r2_hidden(sK4(X151,X152,k4_xboole_0(sK1,sK2)),X150)
        | k4_xboole_0(X151,X152) = k4_xboole_0(k4_xboole_0(sK1,sK2),X150)
        | ~ r2_hidden(sK4(X151,X152,k4_xboole_0(k4_xboole_0(sK1,sK2),X150)),X152)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X150),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1479,f6458])).

fof(f13956,plain,
    ( spl8_462
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13952,f13399,f6457,f6333,f13954])).

fof(f13954,plain,
    ( spl8_462
  <=> ! [X137,X139,X138,X140] :
        ( r1_tarski(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140)
        | ~ m1_subset_1(X140,k1_zfmisc_1(X138))
        | ~ sP5(sK6(X138,k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140),X137,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X138)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_462])])).

fof(f13952,plain,
    ( ! [X140,X138,X139,X137] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | r1_tarski(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140)
        | ~ m1_subset_1(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X138))
        | ~ sP5(sK6(X138,k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140),X137,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X140,k1_zfmisc_1(X138)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13951,f13400])).

fof(f13951,plain,
    ( ! [X140,X138,X139,X137] :
        ( r1_tarski(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140)
        | ~ m1_subset_1(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X138))
        | ~ sP5(sK6(X138,k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140),X137,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X140,k1_zfmisc_1(X138))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X137),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13769,f13400])).

fof(f13769,plain,
    ( ! [X140,X138,X139,X137] :
        ( ~ m1_subset_1(k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(X138))
        | ~ sP5(sK6(X138,k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140),X137,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X140,k1_zfmisc_1(X138))
        | r1_tarski(k4_xboole_0(X139,k4_xboole_0(k4_xboole_0(sK1,sK2),X137)),X140)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X137),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12531])).

fof(f12531,plain,
    ( ! [X140,X138,X139,X137] :
        ( ~ sP5(sK6(X138,k4_xboole_0(X139,k4_xboole_0(sK1,sK2)),X140),X137,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X140,k1_zfmisc_1(X138))
        | ~ m1_subset_1(k4_xboole_0(X139,k4_xboole_0(k4_xboole_0(sK1,sK2),X137)),k1_zfmisc_1(X138))
        | r1_tarski(k4_xboole_0(X139,k4_xboole_0(k4_xboole_0(sK1,sK2),X137)),X140)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X137),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1420,f6458])).

fof(f1420,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ sP5(sK6(X8,k4_xboole_0(X4,k4_xboole_0(X5,X6)),X7),X6,X5)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | ~ m1_subset_1(k4_xboole_0(X4,k4_xboole_0(X5,X6)),k1_zfmisc_1(X8))
      | r1_tarski(k4_xboole_0(X4,k4_xboole_0(X5,X6)),X7) ) ),
    inference(resolution,[],[f443,f60])).

fof(f13950,plain,
    ( spl8_460
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13946,f13399,f6457,f6333,f13948])).

fof(f13948,plain,
    ( spl8_460
  <=> ! [X135,X136,X134] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X135,X136)
        | ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X135)
        | ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_460])])).

fof(f13946,plain,
    ( ! [X134,X136,X135] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X135,X136)
        | ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X135)
        | ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13945,f13400])).

fof(f13945,plain,
    ( ! [X134,X136,X135] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X135,X136)
        | ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X135)
        | ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X134),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13944,f13400])).

fof(f13944,plain,
    ( ! [X134,X136,X135] :
        ( ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(sK1,sK2)))
        | ~ r2_hidden(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X135)
        | ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X135,X136) = k4_xboole_0(k4_xboole_0(sK1,sK2),X134)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X134),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13768,f13400])).

fof(f13768,plain,
    ( ! [X134,X136,X135] :
        ( ~ r2_hidden(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X135)
        | ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(k4_xboole_0(sK1,sK2),X134)))
        | k4_xboole_0(X135,X136) = k4_xboole_0(k4_xboole_0(sK1,sK2),X134)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X134),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12530])).

fof(f12530,plain,
    ( ! [X134,X136,X135] :
        ( ~ sP5(sK4(X135,X136,k4_xboole_0(sK1,sK2)),X134,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X135,X136,k4_xboole_0(k4_xboole_0(sK1,sK2),X134)),X135)
        | ~ r2_hidden(X136,sK4(X135,X136,k4_xboole_0(k4_xboole_0(sK1,sK2),X134)))
        | k4_xboole_0(X135,X136) = k4_xboole_0(k4_xboole_0(sK1,sK2),X134)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X134),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1381,f6458])).

fof(f1381,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ sP5(sK4(X22,X23,k4_xboole_0(X24,X25)),X25,X24)
      | ~ r2_hidden(sK4(X22,X23,k4_xboole_0(X24,X25)),X22)
      | ~ r2_hidden(X23,sK4(X22,X23,k4_xboole_0(X24,X25)))
      | k4_xboole_0(X22,X23) = k4_xboole_0(X24,X25) ) ),
    inference(resolution,[],[f429,f60])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(resolution,[],[f287,f57])).

fof(f13943,plain,
    ( spl8_458
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13939,f13399,f6457,f6333,f13941])).

fof(f13941,plain,
    ( spl8_458
  <=> ! [X131,X133,X132] :
        ( k4_xboole_0(sK1,sK2) = X133
        | sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X133,sK4(k4_xboole_0(sK1,sK2),X132,X133)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_458])])).

fof(f13939,plain,
    ( ! [X132,X133,X131] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = X133
        | ~ r2_hidden(X133,sK4(k4_xboole_0(sK1,sK2),X132,X133))
        | sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13938,f13400])).

fof(f13938,plain,
    ( ! [X132,X133,X131] :
        ( k4_xboole_0(sK1,sK2) = X133
        | ~ r2_hidden(X133,sK4(k4_xboole_0(sK1,sK2),X132,X133))
        | sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13937,f13400])).

fof(f13937,plain,
    ( ! [X132,X133,X131] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X132) = X133
        | ~ r2_hidden(X133,sK4(k4_xboole_0(sK1,sK2),X132,X133))
        | sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13767,f13400])).

fof(f13767,plain,
    ( ! [X132,X133,X131] :
        ( ~ r2_hidden(X133,sK4(k4_xboole_0(sK1,sK2),X132,X133))
        | sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),X132) = X133
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12529])).

fof(f12529,plain,
    ( ! [X132,X133,X131] :
        ( sP5(sK4(k4_xboole_0(sK1,sK2),X132,X133),X131,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X133,sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),X132,X133))
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),X132) = X133
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X131),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1230,f6458])).

fof(f13936,plain,
    ( spl8_456
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13932,f13399,f6457,f6333,f13934])).

fof(f13934,plain,
    ( spl8_456
  <=> ! [X129,X128,X130] :
        ( k4_xboole_0(X129,k4_xboole_0(sK1,sK2)) = X130
        | ~ sP5(sK4(X129,k4_xboole_0(sK1,sK2),X130),X128,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X130,sK4(X129,k4_xboole_0(sK1,sK2),X130)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_456])])).

fof(f13932,plain,
    ( ! [X130,X128,X129] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(X129,k4_xboole_0(sK1,sK2)) = X130
        | ~ r2_hidden(X130,sK4(X129,k4_xboole_0(sK1,sK2),X130))
        | ~ sP5(sK4(X129,k4_xboole_0(sK1,sK2),X130),X128,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13931,f13400])).

fof(f13931,plain,
    ( ! [X130,X128,X129] :
        ( k4_xboole_0(X129,k4_xboole_0(sK1,sK2)) = X130
        | ~ r2_hidden(X130,sK4(X129,k4_xboole_0(sK1,sK2),X130))
        | ~ sP5(sK4(X129,k4_xboole_0(sK1,sK2),X130),X128,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X128),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13766,f13400])).

fof(f13766,plain,
    ( ! [X130,X128,X129] :
        ( ~ r2_hidden(X130,sK4(X129,k4_xboole_0(sK1,sK2),X130))
        | ~ sP5(sK4(X129,k4_xboole_0(sK1,sK2),X130),X128,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X129,k4_xboole_0(k4_xboole_0(sK1,sK2),X128)) = X130
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X128),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12528])).

fof(f12528,plain,
    ( ! [X130,X128,X129] :
        ( ~ sP5(sK4(X129,k4_xboole_0(sK1,sK2),X130),X128,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(X130,sK4(X129,k4_xboole_0(k4_xboole_0(sK1,sK2),X128),X130))
        | k4_xboole_0(X129,k4_xboole_0(k4_xboole_0(sK1,sK2),X128)) = X130
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X128),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1189,f6458])).

fof(f1189,plain,(
    ! [X19,X17,X20,X18] :
      ( ~ sP5(sK4(X17,k4_xboole_0(X18,X19),X20),X19,X18)
      | ~ r2_hidden(X20,sK4(X17,k4_xboole_0(X18,X19),X20))
      | k4_xboole_0(X17,k4_xboole_0(X18,X19)) = X20 ) ),
    inference(resolution,[],[f407,f60])).

fof(f13930,plain,
    ( spl8_454
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13926,f13399,f6457,f6333,f13928])).

fof(f13928,plain,
    ( spl8_454
  <=> ! [X126,X127] :
        ( k4_xboole_0(sK1,sK2) = X127
        | ~ sP5(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X126,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X127) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_454])])).

fof(f13926,plain,
    ( ! [X127,X126] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = X127
        | ~ r2_hidden(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X127)
        | ~ sP5(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X126,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13925,f13400])).

fof(f13925,plain,
    ( ! [X127,X126] :
        ( k4_xboole_0(sK1,sK2) = X127
        | ~ r2_hidden(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X127)
        | ~ sP5(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X126,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X126),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13765,f13400])).

fof(f13765,plain,
    ( ! [X127,X126] :
        ( ~ r2_hidden(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X127)
        | ~ sP5(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X126,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X126) = X127
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X126),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12527])).

fof(f12527,plain,
    ( ! [X127,X126] :
        ( ~ sP5(sK4(X127,k1_xboole_0,k4_xboole_0(sK1,sK2)),X126,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X127,k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK2),X126)),X127)
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X126) = X127
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X126),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1120,f6458])).

fof(f1120,plain,(
    ! [X10,X11,X9] :
      ( ~ sP5(sK4(X9,k1_xboole_0,k4_xboole_0(X10,X11)),X11,X10)
      | ~ r2_hidden(sK4(X9,k1_xboole_0,k4_xboole_0(X10,X11)),X9)
      | k4_xboole_0(X10,X11) = X9 ) ),
    inference(resolution,[],[f291,f60])).

fof(f291,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(X8,k1_xboole_0,X9),X9)
      | X8 = X9
      | ~ r2_hidden(sK4(X8,k1_xboole_0,X9),X8) ) ),
    inference(forward_demodulation,[],[f289,f51])).

fof(f289,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(X8,k1_xboole_0,X9),X9)
      | k4_xboole_0(X8,k1_xboole_0) = X9
      | ~ r2_hidden(sK4(X8,k1_xboole_0,X9),X8) ) ),
    inference(resolution,[],[f43,f186])).

fof(f13924,plain,
    ( spl8_452
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13764,f13399,f6457,f6333,f13922])).

fof(f13922,plain,
    ( spl8_452
  <=> ! [X108,X107] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),k1_xboole_0,X108)
        | ~ sP5(X108,X107,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_452])])).

fof(f13764,plain,
    ( ! [X107,X108] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ sP5(k4_xboole_0(sK1,sK2),k1_xboole_0,X108)
        | ~ sP5(X108,X107,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12520])).

fof(f12520,plain,
    ( ! [X107,X108] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),k1_xboole_0,X108)
        | ~ sP5(X108,X107,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X107),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f922,f6458])).

fof(f922,plain,(
    ! [X4,X5,X3] :
      ( ~ sP5(k4_xboole_0(X5,X4),k1_xboole_0,X3)
      | ~ sP5(X3,X4,X5) ) ),
    inference(superposition,[],[f337,f51])).

fof(f13920,plain,
    ( spl8_450
    | spl8_334
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13916,f13399,f6457,f6333,f7477,f13918])).

fof(f13918,plain,
    ( spl8_450
  <=> ! [X98,X97] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK1)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_450])])).

fof(f13916,plain,
    ( ! [X97,X98] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13915,f13400])).

fof(f13915,plain,
    ( ! [X97,X98] :
        ( k4_xboole_0(sK1,sK2) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13914,f13400])).

fof(f13914,plain,
    ( ! [X97,X98] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X98) = sK3
        | ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13913,f13400])).

fof(f13913,plain,
    ( ! [X97,X98] :
        ( ~ r2_hidden(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK1)
        | ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98) = sK3
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13763,f13400])).

fof(f13763,plain,
    ( ! [X97,X98] :
        ( ~ m1_subset_1(sK4(k4_xboole_0(sK1,sK2),X98,sK3),sK0)
        | sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98,sK3),sK1)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98) = sK3
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12516])).

fof(f12516,plain,
    ( ! [X97,X98] :
        ( sP5(sK4(k4_xboole_0(sK1,sK2),X98,sK3),X97,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98,sK3),sK0)
        | ~ r2_hidden(sK4(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98,sK3),sK1)
        | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),X98) = sK3
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X97),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f634,f6458])).

fof(f13906,plain,
    ( spl8_448
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13902,f13399,f6457,f6333,f13904])).

fof(f13902,plain,
    ( ! [X68,X66,X67] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(X67,k4_xboole_0(sK1,sK2)) = X68
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X67)
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X68)
        | sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13901,f13400])).

fof(f13901,plain,
    ( ! [X68,X66,X67] :
        ( k4_xboole_0(X67,k4_xboole_0(sK1,sK2)) = X68
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X67)
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X68)
        | sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X66),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13900,f13400])).

fof(f13900,plain,
    ( ! [X68,X66,X67] :
        ( ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X67)
        | ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X68)
        | sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66)) = X68
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X66),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13758,f13400])).

fof(f13758,plain,
    ( ! [X68,X66,X67] :
        ( ~ r2_hidden(sK4(X67,k4_xboole_0(sK1,sK2),X68),X68)
        | sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66),X68),X67)
        | k4_xboole_0(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66)) = X68
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X66),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12504])).

fof(f12504,plain,
    ( ! [X68,X66,X67] :
        ( sP5(sK4(X67,k4_xboole_0(sK1,sK2),X68),X66,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66),X68),X68)
        | ~ r2_hidden(sK4(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66),X68),X67)
        | k4_xboole_0(X67,k4_xboole_0(k4_xboole_0(sK1,sK2),X66)) = X68
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X66),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f431,f6458])).

fof(f13899,plain,
    ( spl8_446
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13895,f13399,f6457,f6333,f13897])).

fof(f13895,plain,
    ( ! [X64,X65,X63] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X64,X65)
        | r2_hidden(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X64)
        | sP5(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X63,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13894,f13400])).

fof(f13894,plain,
    ( ! [X64,X65,X63] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X64,X65)
        | r2_hidden(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X64)
        | sP5(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X63,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X63),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13757,f13400])).

fof(f13757,plain,
    ( ! [X64,X65,X63] :
        ( r2_hidden(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X64)
        | sP5(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X63,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X64,X65) = k4_xboole_0(k4_xboole_0(sK1,sK2),X63)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X63),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12503])).

fof(f12503,plain,
    ( ! [X64,X65,X63] :
        ( sP5(sK4(X64,X65,k4_xboole_0(sK1,sK2)),X63,k4_xboole_0(sK1,sK2))
        | r2_hidden(sK4(X64,X65,k4_xboole_0(k4_xboole_0(sK1,sK2),X63)),X64)
        | k4_xboole_0(X64,X65) = k4_xboole_0(k4_xboole_0(sK1,sK2),X63)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X63),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f418,f6458])).

fof(f13893,plain,
    ( spl8_444
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13889,f13399,f6457,f6333,f13891])).

fof(f13889,plain,
    ( ! [X61,X62,X60] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(X61,X62)
        | ~ r2_hidden(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X62)
        | sP5(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X60,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13888,f13400])).

fof(f13888,plain,
    ( ! [X61,X62,X60] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(X61,X62)
        | ~ r2_hidden(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X62)
        | sP5(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X60,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X60),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13756,f13400])).

fof(f13756,plain,
    ( ! [X61,X62,X60] :
        ( ~ r2_hidden(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X62)
        | sP5(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X60,k4_xboole_0(sK1,sK2))
        | k4_xboole_0(X61,X62) = k4_xboole_0(k4_xboole_0(sK1,sK2),X60)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X60),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12502])).

fof(f12502,plain,
    ( ! [X61,X62,X60] :
        ( sP5(sK4(X61,X62,k4_xboole_0(sK1,sK2)),X60,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(X61,X62,k4_xboole_0(k4_xboole_0(sK1,sK2),X60)),X62)
        | k4_xboole_0(X61,X62) = k4_xboole_0(k4_xboole_0(sK1,sK2),X60)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X60),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f409,f6458])).

fof(f13887,plain,
    ( spl8_442
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13755,f13399,f6457,f6333,f13885])).

fof(f13885,plain,
    ( spl8_442
  <=> ! [X53,X52,X54] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),X53,X54)
        | ~ sP5(k4_xboole_0(X54,X53),X52,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_442])])).

fof(f13755,plain,
    ( ! [X54,X52,X53] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ sP5(k4_xboole_0(sK1,sK2),X53,X54)
        | ~ sP5(k4_xboole_0(X54,X53),X52,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12498])).

fof(f12498,plain,
    ( ! [X54,X52,X53] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),X53,X54)
        | ~ sP5(k4_xboole_0(X54,X53),X52,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X52),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f337,f6458])).

fof(f13883,plain,
    ( spl8_440
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13879,f13399,f6457,f6333,f13881])).

fof(f13881,plain,
    ( spl8_440
  <=> ! [X49,X48,X47] :
        ( r1_tarski(X49,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X48))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X48))
        | ~ sP5(sK6(X48,X49,k4_xboole_0(sK1,sK2)),X47,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_440])])).

fof(f13879,plain,
    ( ! [X47,X48,X49] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | r1_tarski(X49,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X48))
        | ~ sP5(sK6(X48,X49,k4_xboole_0(sK1,sK2)),X47,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X48)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13878,f13400])).

fof(f13878,plain,
    ( ! [X47,X48,X49] :
        ( r1_tarski(X49,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X48))
        | ~ sP5(sK6(X48,X49,k4_xboole_0(sK1,sK2)),X47,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X48))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X47),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(forward_demodulation,[],[f13754,f13400])).

fof(f13754,plain,
    ( ! [X47,X48,X49] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X48))
        | ~ sP5(sK6(X48,X49,k4_xboole_0(sK1,sK2)),X47,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X48))
        | r1_tarski(X49,k4_xboole_0(k4_xboole_0(sK1,sK2),X47))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X47),k1_zfmisc_1(sK0)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12496])).

fof(f12496,plain,
    ( ! [X47,X48,X49] :
        ( ~ sP5(sK6(X48,X49,k4_xboole_0(sK1,sK2)),X47,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X48))
        | r1_tarski(X49,k4_xboole_0(k4_xboole_0(sK1,sK2),X47))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X47),k1_zfmisc_1(X48))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X47),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f274,f6458])).

fof(f13876,plain,
    ( spl8_438
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13752,f13399,f6457,f6333,f13874])).

fof(f13874,plain,
    ( spl8_438
  <=> ! [X38,X39] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),X39)
        | ~ sP5(X39,X38,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_438])])).

fof(f13752,plain,
    ( ! [X39,X38] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(k4_xboole_0(sK1,sK2),X39)
        | ~ sP5(X39,X38,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12491])).

fof(f12491,plain,
    ( ! [X39,X38] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),X39)
        | ~ sP5(X39,X38,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X38),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f230,f6458])).

fof(f13872,plain,
    ( spl8_436
    | ~ spl8_233
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(avatar_split_clause,[],[f13751,f13399,f6457,f6333,f13870])).

fof(f13751,plain,
    ( ! [X33,X32] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
        | ~ r2_hidden(X33,k4_xboole_0(sK1,sK2))
        | sP5(X33,X32,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_238
    | ~ spl8_434 ),
    inference(backward_demodulation,[],[f13400,f12489])).

fof(f12489,plain,
    ( ! [X33,X32] :
        ( ~ r2_hidden(X33,k4_xboole_0(sK1,sK2))
        | sP5(X33,X32,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X32),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f59,f6458])).

fof(f13401,plain,
    ( ~ spl8_241
    | spl8_434
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f13231,f6457,f13399,f6586])).

fof(f6586,plain,
    ( spl8_241
  <=> ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).

fof(f13231,plain,
    ( ! [X8] :
        ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X8)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f8192,f6458])).

fof(f13226,plain,
    ( ~ spl8_431
    | ~ spl8_429
    | ~ spl8_433
    | spl8_427 ),
    inference(avatar_split_clause,[],[f13211,f13201,f13224,f13208,f13218])).

fof(f13218,plain,
    ( spl8_431
  <=> ~ r2_hidden(sK3,sK4(sK3,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_431])])).

fof(f13208,plain,
    ( spl8_429
  <=> ~ m1_subset_1(sK4(sK3,k1_xboole_0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_429])])).

fof(f13224,plain,
    ( spl8_433
  <=> ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_433])])).

fof(f13211,plain,
    ( ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK2)
    | ~ m1_subset_1(sK4(sK3,k1_xboole_0,k1_xboole_0),sK0)
    | ~ r2_hidden(sK3,sK4(sK3,k1_xboole_0,k1_xboole_0))
    | ~ spl8_427 ),
    inference(resolution,[],[f13202,f119])).

fof(f13210,plain,
    ( ~ spl8_427
    | ~ spl8_429
    | spl8_76 ),
    inference(avatar_split_clause,[],[f13191,f649,f13208,f13201])).

fof(f13191,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4(sK3,k1_xboole_0,k1_xboole_0),sK0)
    | ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK1) ),
    inference(resolution,[],[f4188,f31])).

fof(f13203,plain,
    ( ~ spl8_427
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f13190,f1211,f649,f13201])).

fof(f13190,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK4(sK3,k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl8_116 ),
    inference(resolution,[],[f4188,f2541])).

fof(f13162,plain,
    ( spl8_420
    | ~ spl8_423
    | ~ spl8_425
    | spl8_417 ),
    inference(avatar_split_clause,[],[f13141,f13071,f13160,f13154,f13148])).

fof(f13148,plain,
    ( spl8_420
  <=> r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_420])])).

fof(f13154,plain,
    ( spl8_423
  <=> ~ m1_subset_1(sK4(sK1,k1_xboole_0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_423])])).

fof(f13160,plain,
    ( spl8_425
  <=> ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_425])])).

fof(f13071,plain,
    ( spl8_417
  <=> ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_417])])).

fof(f13141,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK2)
    | ~ m1_subset_1(sK4(sK1,k1_xboole_0,k1_xboole_0),sK0)
    | r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl8_417 ),
    inference(resolution,[],[f13072,f32])).

fof(f13072,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK3)
    | ~ spl8_417 ),
    inference(avatar_component_clause,[],[f13071])).

fof(f13091,plain,
    ( ~ spl8_3
    | spl8_419 ),
    inference(avatar_split_clause,[],[f13087,f13083,f71])).

fof(f13087,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_419 ),
    inference(resolution,[],[f13084,f245])).

fof(f13084,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ spl8_419 ),
    inference(avatar_component_clause,[],[f13083])).

fof(f13085,plain,
    ( spl8_46
    | ~ spl8_1
    | ~ spl8_419
    | ~ spl8_322 ),
    inference(avatar_split_clause,[],[f13078,f7237,f13083,f64,f247])).

fof(f247,plain,
    ( spl8_46
  <=> r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f7237,plain,
    ( spl8_322
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK3),sK1),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_322])])).

fof(f13078,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_322 ),
    inference(duplicate_literal_removal,[],[f13074])).

fof(f13074,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_322 ),
    inference(resolution,[],[f7238,f54])).

fof(f7238,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK3),sK1),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl8_322 ),
    inference(avatar_component_clause,[],[f7237])).

fof(f13073,plain,
    ( ~ spl8_417
    | spl8_192
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f13066,f1211,f5043,f13071])).

fof(f13066,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK3)
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f13059,f51])).

fof(f13059,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK3)
    | k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f12997])).

fof(f12997,plain,
    ( ~ r2_hidden(sK4(sK1,k1_xboole_0,k1_xboole_0),sK3)
    | k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0
    | ~ spl8_116 ),
    inference(resolution,[],[f4003,f2217])).

fof(f4003,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK4(sK1,X7,X8),X8)
        | ~ r2_hidden(sK4(sK1,X7,X8),sK3)
        | k4_xboole_0(sK1,X7) = X8 )
    | ~ spl8_116 ),
    inference(resolution,[],[f3967,f42])).

fof(f12855,plain,
    ( ~ spl8_7
    | ~ spl8_234
    | spl8_337 ),
    inference(avatar_split_clause,[],[f12850,f7484,f6336,f85])).

fof(f85,plain,
    ( spl8_7
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f7484,plain,
    ( spl8_337
  <=> ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_337])])).

fof(f12850,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_234
    | ~ spl8_337 ),
    inference(resolution,[],[f7485,f6337])).

fof(f7485,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ spl8_337 ),
    inference(avatar_component_clause,[],[f7484])).

fof(f12675,plain,
    ( ~ spl8_285
    | spl8_294
    | spl8_414
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12483,f6457,f12673,f6716,f6692])).

fof(f6692,plain,
    ( spl8_285
  <=> ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_285])])).

fof(f6716,plain,
    ( spl8_294
  <=> r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_294])])).

fof(f12673,plain,
    ( spl8_414
  <=> ! [X25] :
        ( ~ sP5(sK6(X25,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X25))
        | ~ m1_subset_1(sK6(X25,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_414])])).

fof(f12483,plain,
    ( ! [X25] :
        ( ~ sP5(sK6(X25,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X25))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK6(X25,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X25))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2037,f6458])).

fof(f12671,plain,
    ( ~ spl8_285
    | spl8_294
    | spl8_296
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12613,f6457,f6719,f6716,f6692])).

fof(f6719,plain,
    ( spl8_296
  <=> ! [X183] :
        ( ~ r2_hidden(sK6(X183,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X183,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X183))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X183)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_296])])).

fof(f12613,plain,
    ( ! [X369] :
        ( ~ r2_hidden(sK6(X369,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X369))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X369))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK6(X369,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1679,f6458])).

fof(f12670,plain,
    ( ~ spl8_303
    | spl8_412
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12627,f6457,f12668,f6736])).

fof(f6736,plain,
    ( spl8_303
  <=> ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_303])])).

fof(f12668,plain,
    ( spl8_412
  <=> ! [X396,X395] :
        ( ~ r2_hidden(sK6(X395,k4_xboole_0(sK1,X396),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | r1_tarski(k4_xboole_0(sK1,X396),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))
        | ~ m1_subset_1(sK6(X395,k4_xboole_0(sK1,X396),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X395))
        | ~ m1_subset_1(k4_xboole_0(sK1,X396),k1_zfmisc_1(X395)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_412])])).

fof(f12627,plain,
    ( ! [X395,X396] :
        ( ~ r2_hidden(sK6(X395,k4_xboole_0(sK1,X396),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,X396),k1_zfmisc_1(X395))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X395))
        | ~ m1_subset_1(sK6(X395,k4_xboole_0(sK1,X396),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),sK0)
        | r1_tarski(k4_xboole_0(sK1,X396),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2738,f6458])).

fof(f2738,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK6(X3,k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3)),X2)
      | ~ m1_subset_1(k4_xboole_0(sK1,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(X2,sK3),k1_zfmisc_1(X3))
      | ~ m1_subset_1(sK6(X3,k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3)),sK0)
      | r1_tarski(k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f2731])).

fof(f2731,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(k4_xboole_0(X2,sK3),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(sK1,X4),k1_zfmisc_1(X3))
      | ~ r2_hidden(sK6(X3,k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3)),X2)
      | ~ m1_subset_1(sK6(X3,k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3)),sK0)
      | r1_tarski(k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3))
      | r1_tarski(k4_xboole_0(sK1,X4),k4_xboole_0(X2,sK3))
      | ~ m1_subset_1(k4_xboole_0(X2,sK3),k1_zfmisc_1(X3))
      | ~ m1_subset_1(k4_xboole_0(sK1,X4),k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f1672,f444])).

fof(f1672,plain,(
    ! [X35,X33,X34] :
      ( ~ r2_hidden(sK6(X35,X33,k4_xboole_0(X34,sK3)),sK1)
      | ~ m1_subset_1(k4_xboole_0(X34,sK3),k1_zfmisc_1(X35))
      | ~ m1_subset_1(X33,k1_zfmisc_1(X35))
      | ~ r2_hidden(sK6(X35,X33,k4_xboole_0(X34,sK3)),X34)
      | ~ m1_subset_1(sK6(X35,X33,k4_xboole_0(X34,sK3)),sK0)
      | r1_tarski(X33,k4_xboole_0(X34,sK3)) ) ),
    inference(resolution,[],[f466,f31])).

fof(f12666,plain,
    ( ~ spl8_299
    | spl8_410
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12624,f6457,f12664,f6726])).

fof(f6726,plain,
    ( spl8_299
  <=> ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_299])])).

fof(f12664,plain,
    ( spl8_410
  <=> ! [X390,X389] :
        ( ~ r2_hidden(sK4(X389,X390,k4_xboole_0(sK1,sK2)),sK1)
        | ~ r2_hidden(sK4(X389,X390,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),X390)
        | k4_xboole_0(X389,X390) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)
        | ~ m1_subset_1(sK4(X389,X390,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_410])])).

fof(f12624,plain,
    ( ! [X389,X390] :
        ( ~ r2_hidden(sK4(X389,X390,k4_xboole_0(sK1,sK2)),sK1)
        | ~ m1_subset_1(sK4(X389,X390,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK0)
        | k4_xboole_0(X389,X390) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)
        | ~ r2_hidden(sK4(X389,X390,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),X390)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4413,f6458])).

fof(f4413,plain,(
    ! [X26,X24,X25] :
      ( ~ r2_hidden(sK4(X24,X25,k4_xboole_0(X26,sK2)),sK1)
      | ~ m1_subset_1(sK4(X24,X25,k4_xboole_0(X26,sK2)),sK0)
      | k4_xboole_0(X26,sK2) = k4_xboole_0(X24,X25)
      | ~ r2_hidden(sK4(X24,X25,k4_xboole_0(X26,sK2)),X25) ) ),
    inference(resolution,[],[f30,f1479])).

fof(f12662,plain,
    ( ~ spl8_299
    | spl8_408
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12622,f6457,f12660,f6726])).

fof(f12660,plain,
    ( spl8_408
  <=> ! [X386,X385] :
        ( ~ r2_hidden(sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK0)
        | ~ m1_subset_1(k4_xboole_0(X386,sK1),k1_zfmisc_1(X385))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(X385))
        | r1_tarski(k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2))
        | ~ r2_hidden(sK3,sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_408])])).

fof(f12622,plain,
    ( ! [X385,X386] :
        ( ~ r2_hidden(sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK3,sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)))
        | r1_tarski(k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(X385))
        | ~ m1_subset_1(k4_xboole_0(X386,sK1),k1_zfmisc_1(X385))
        | ~ m1_subset_1(sK6(X385,k4_xboole_0(X386,sK1),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f5977,f6458])).

fof(f5977,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)),X4)
      | ~ r2_hidden(sK3,sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)))
      | r1_tarski(k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2))
      | ~ m1_subset_1(k4_xboole_0(X4,sK2),k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X3,sK1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)),sK0) ) ),
    inference(duplicate_literal_removal,[],[f5968])).

fof(f5968,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)),sK0)
      | ~ r2_hidden(sK3,sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)))
      | r1_tarski(k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2))
      | ~ m1_subset_1(k4_xboole_0(X4,sK2),k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X3,sK1),k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2))
      | ~ m1_subset_1(k4_xboole_0(X4,sK2),k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(X3,sK1),k1_zfmisc_1(X2))
      | ~ r2_hidden(sK6(X2,k4_xboole_0(X3,sK1),k4_xboole_0(X4,sK2)),X4) ) ),
    inference(resolution,[],[f4686,f466])).

fof(f4686,plain,(
    ! [X83,X81,X82] :
      ( ~ r2_hidden(sK6(X81,k4_xboole_0(X82,sK1),X83),sK2)
      | ~ m1_subset_1(sK6(X81,k4_xboole_0(X82,sK1),X83),sK0)
      | ~ r2_hidden(sK3,sK6(X81,k4_xboole_0(X82,sK1),X83))
      | r1_tarski(k4_xboole_0(X82,sK1),X83)
      | ~ m1_subset_1(X83,k1_zfmisc_1(X81))
      | ~ m1_subset_1(k4_xboole_0(X82,sK1),k1_zfmisc_1(X81)) ) ),
    inference(resolution,[],[f119,f443])).

fof(f12658,plain,
    ( ~ spl8_285
    | spl8_406
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12620,f6457,f12656,f6692])).

fof(f12656,plain,
    ( spl8_406
  <=> ! [X381,X382] :
        ( ~ r2_hidden(sK6(X381,k4_xboole_0(X382,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X381,k4_xboole_0(X382,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(X382,sK2),k1_zfmisc_1(X381))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X381))
        | r1_tarski(k4_xboole_0(X382,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_406])])).

fof(f12620,plain,
    ( ! [X382,X381] :
        ( ~ r2_hidden(sK6(X381,k4_xboole_0(X382,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | r1_tarski(k4_xboole_0(X382,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X381))
        | ~ m1_subset_1(k4_xboole_0(X382,sK2),k1_zfmisc_1(X381))
        | ~ m1_subset_1(sK6(X381,k4_xboole_0(X382,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f5755,f6458])).

fof(f5755,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK6(X4,k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1)),X6)
      | r1_tarski(k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1))
      | ~ m1_subset_1(k4_xboole_0(X6,sK1),k1_zfmisc_1(X4))
      | ~ m1_subset_1(k4_xboole_0(X5,sK2),k1_zfmisc_1(X4))
      | ~ m1_subset_1(sK6(X4,k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1)),sK0) ) ),
    inference(duplicate_literal_removal,[],[f5747])).

fof(f5747,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK6(X4,k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1)),sK0)
      | r1_tarski(k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1))
      | ~ m1_subset_1(k4_xboole_0(X6,sK1),k1_zfmisc_1(X4))
      | ~ m1_subset_1(k4_xboole_0(X5,sK2),k1_zfmisc_1(X4))
      | r1_tarski(k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1))
      | ~ m1_subset_1(k4_xboole_0(X6,sK1),k1_zfmisc_1(X4))
      | ~ m1_subset_1(k4_xboole_0(X5,sK2),k1_zfmisc_1(X4))
      | ~ r2_hidden(sK6(X4,k4_xboole_0(X5,sK2),k4_xboole_0(X6,sK1)),X6) ) ),
    inference(resolution,[],[f4419,f466])).

fof(f4419,plain,(
    ! [X39,X41,X40] :
      ( ~ r2_hidden(sK6(X39,k4_xboole_0(X40,sK2),X41),sK1)
      | ~ m1_subset_1(sK6(X39,k4_xboole_0(X40,sK2),X41),sK0)
      | r1_tarski(k4_xboole_0(X40,sK2),X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
      | ~ m1_subset_1(k4_xboole_0(X40,sK2),k1_zfmisc_1(X39)) ) ),
    inference(resolution,[],[f30,f443])).

fof(f12654,plain,
    ( ~ spl8_285
    | spl8_404
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12617,f6457,f12652,f6692])).

fof(f12652,plain,
    ( spl8_404
  <=> ! [X376,X377] :
        ( ~ r2_hidden(sK4(X376,X377,k4_xboole_0(sK1,sK2)),sK2)
        | ~ r2_hidden(sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),X377)
        | k4_xboole_0(X376,X377) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)
        | ~ r2_hidden(sK3,sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)))
        | ~ m1_subset_1(sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_404])])).

fof(f12617,plain,
    ( ! [X377,X376] :
        ( ~ r2_hidden(sK4(X376,X377,k4_xboole_0(sK1,sK2)),sK2)
        | ~ m1_subset_1(sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ r2_hidden(sK3,sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)))
        | k4_xboole_0(X376,X377) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)
        | ~ r2_hidden(sK4(X376,X377,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),X377)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4676,f6458])).

fof(f12650,plain,
    ( ~ spl8_285
    | spl8_402
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12616,f6457,f1040,f12648,f6692])).

fof(f12648,plain,
    ( spl8_402
  <=> ! [X375,X374] :
        ( sP5(sK6(X374,X375,k4_xboole_0(sK1,sK2)),sK3,sK1)
        | ~ m1_subset_1(X375,k1_zfmisc_1(X374))
        | r1_tarski(X375,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X374))
        | ~ r2_hidden(sK6(X374,X375,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_402])])).

fof(f12616,plain,
    ( ! [X374,X375] :
        ( sP5(sK6(X374,X375,k4_xboole_0(sK1,sK2)),sK3,sK1)
        | ~ r2_hidden(sK6(X374,X375,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X374))
        | r1_tarski(X375,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(X375,k1_zfmisc_1(X374))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(superposition,[],[f4555,f6458])).

fof(f4555,plain,
    ( ! [X92,X90,X91] :
        ( sP5(sK6(X90,X91,k4_xboole_0(X92,sK1)),sK3,sK1)
        | ~ r2_hidden(sK6(X90,X91,k4_xboole_0(X92,sK1)),X92)
        | ~ m1_subset_1(k4_xboole_0(X92,sK1),k1_zfmisc_1(X90))
        | r1_tarski(X91,k4_xboole_0(X92,sK1))
        | ~ m1_subset_1(X91,k1_zfmisc_1(X90)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4554,f1041])).

fof(f4554,plain,
    ( ! [X92,X90,X91] :
        ( ~ r2_hidden(sK6(X90,X91,k4_xboole_0(X92,sK1)),X92)
        | ~ m1_subset_1(k4_xboole_0(X92,sK1),k1_zfmisc_1(X90))
        | sP5(sK6(X90,X91,k4_xboole_0(X92,sK1)),sK3,sK1)
        | ~ m1_subset_1(X91,k1_zfmisc_1(X90))
        | r1_tarski(X91,k4_xboole_0(X92,k4_xboole_0(sK1,sK3))) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4553,f1041])).

fof(f4553,plain,
    ( ! [X92,X90,X91] :
        ( ~ m1_subset_1(k4_xboole_0(X92,sK1),k1_zfmisc_1(X90))
        | sP5(sK6(X90,X91,k4_xboole_0(X92,sK1)),sK3,sK1)
        | ~ m1_subset_1(X91,k1_zfmisc_1(X90))
        | ~ r2_hidden(sK6(X90,X91,k4_xboole_0(X92,k4_xboole_0(sK1,sK3))),X92)
        | r1_tarski(X91,k4_xboole_0(X92,k4_xboole_0(sK1,sK3))) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4481,f1041])).

fof(f4481,plain,
    ( ! [X92,X90,X91] :
        ( sP5(sK6(X90,X91,k4_xboole_0(X92,sK1)),sK3,sK1)
        | ~ m1_subset_1(k4_xboole_0(X92,k4_xboole_0(sK1,sK3)),k1_zfmisc_1(X90))
        | ~ m1_subset_1(X91,k1_zfmisc_1(X90))
        | ~ r2_hidden(sK6(X90,X91,k4_xboole_0(X92,k4_xboole_0(sK1,sK3))),X92)
        | r1_tarski(X91,k4_xboole_0(X92,k4_xboole_0(sK1,sK3))) )
    | ~ spl8_106 ),
    inference(superposition,[],[f1668,f1041])).

fof(f12646,plain,
    ( ~ spl8_285
    | spl8_400
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12614,f6457,f12644,f6692])).

fof(f12644,plain,
    ( spl8_400
  <=> ! [X371,X370] :
        ( ~ r2_hidden(sK6(X370,k4_xboole_0(sK3,X371),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X370))
        | r1_tarski(k4_xboole_0(sK3,X371),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK6(X370,k4_xboole_0(sK3,X371),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3,X371),k1_zfmisc_1(X370)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_400])])).

fof(f12614,plain,
    ( ! [X370,X371] :
        ( ~ r2_hidden(sK6(X370,k4_xboole_0(sK3,X371),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK3,X371),k1_zfmisc_1(X370))
        | ~ m1_subset_1(sK6(X370,k4_xboole_0(sK3,X371),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | r1_tarski(k4_xboole_0(sK3,X371),k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X370))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2024,f6458])).

fof(f2024,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X1,k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1)),X0)
      | ~ m1_subset_1(k4_xboole_0(sK3,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK6(X1,k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1)),sK0)
      | r1_tarski(k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1))
      | ~ m1_subset_1(k4_xboole_0(X0,sK1),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f2017])).

fof(f2017,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_xboole_0(X0,sK1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(k4_xboole_0(sK3,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK6(X1,k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1)),sK0)
      | r1_tarski(k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1))
      | r1_tarski(k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1))
      | ~ m1_subset_1(k4_xboole_0(X0,sK1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(k4_xboole_0(sK3,X2),k1_zfmisc_1(X1))
      | ~ r2_hidden(sK6(X1,k4_xboole_0(sK3,X2),k4_xboole_0(X0,sK1)),X0) ) ),
    inference(resolution,[],[f1449,f466])).

fof(f1449,plain,(
    ! [X35,X33,X34] :
      ( ~ r2_hidden(sK6(X35,k4_xboole_0(sK3,X33),X34),sK1)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | ~ m1_subset_1(k4_xboole_0(sK3,X33),k1_zfmisc_1(X35))
      | ~ m1_subset_1(sK6(X35,k4_xboole_0(sK3,X33),X34),sK0)
      | r1_tarski(k4_xboole_0(sK3,X33),X34) ) ),
    inference(resolution,[],[f444,f31])).

fof(f12642,plain,
    ( ~ spl8_241
    | spl8_398
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f12486,f6457,f12640,f6586])).

fof(f12640,plain,
    ( spl8_398
  <=> ! [X27,X26] :
        ( ~ r2_hidden(sK4(X26,X27,k4_xboole_0(sK1,sK2)),X27)
        | k4_xboole_0(X26,X27) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_398])])).

fof(f12486,plain,
    ( ! [X26,X27] :
        ( ~ r2_hidden(sK4(X26,X27,k4_xboole_0(sK1,sK2)),X27)
        | k4_xboole_0(X26,X27) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f2933,f6458])).

fof(f12638,plain,
    ( ~ spl8_285
    | ~ spl8_337
    | ~ spl8_238
    | spl8_291 ),
    inference(avatar_split_clause,[],[f12482,f6703,f6457,f7484,f6692])).

fof(f6703,plain,
    ( spl8_291
  <=> ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_291])])).

fof(f12482,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0))
    | ~ spl8_238
    | ~ spl8_291 ),
    inference(superposition,[],[f6704,f6458])).

fof(f6704,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3)
    | ~ spl8_291 ),
    inference(avatar_component_clause,[],[f6703])).

fof(f12637,plain,
    ( ~ spl8_285
    | spl8_328
    | ~ spl8_238
    | ~ spl8_294 ),
    inference(avatar_split_clause,[],[f12481,f6716,f6457,f7440,f6692])).

fof(f12481,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0))
    | ~ spl8_238
    | ~ spl8_294 ),
    inference(superposition,[],[f6717,f6458])).

fof(f6717,plain,
    ( r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
    | ~ spl8_294 ),
    inference(avatar_component_clause,[],[f6716])).

fof(f12636,plain,
    ( ~ spl8_285
    | ~ spl8_335
    | ~ spl8_238
    | spl8_325 ),
    inference(avatar_split_clause,[],[f12480,f7252,f6457,f7474,f6692])).

fof(f7474,plain,
    ( spl8_335
  <=> k4_xboole_0(sK1,sK2) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_335])])).

fof(f7252,plain,
    ( spl8_325
  <=> k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_325])])).

fof(f12480,plain,
    ( k4_xboole_0(sK1,sK2) != sK3
    | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0))
    | ~ spl8_238
    | ~ spl8_325 ),
    inference(superposition,[],[f7253,f6458])).

fof(f7253,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) != sK3
    | ~ spl8_325 ),
    inference(avatar_component_clause,[],[f7252])).

fof(f10826,plain,
    ( ~ spl8_247
    | spl8_259 ),
    inference(avatar_split_clause,[],[f10821,f6630,f6599])).

fof(f6599,plain,
    ( spl8_247
  <=> ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_247])])).

fof(f6630,plain,
    ( spl8_259
  <=> ~ r2_hidden(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_259])])).

fof(f10821,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl8_259 ),
    inference(duplicate_literal_removal,[],[f10813])).

fof(f10813,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1)
    | ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl8_259 ),
    inference(resolution,[],[f8752,f6631])).

fof(f6631,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl8_259 ),
    inference(avatar_component_clause,[],[f6630])).

fof(f8752,plain,
    ( ! [X24] :
        ( r2_hidden(k4_xboole_0(X24,sK2),sK2)
        | ~ r2_hidden(k4_xboole_0(X24,sK2),sK1)
        | ~ r2_hidden(k4_xboole_0(sK1,sK2),X24) )
    | ~ spl8_259 ),
    inference(resolution,[],[f2107,f6631])).

fof(f10825,plain,
    ( spl8_20
    | spl8_396
    | spl8_259 ),
    inference(avatar_split_clause,[],[f10811,f6630,f10823,f137])).

fof(f10823,plain,
    ( spl8_396
  <=> ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(X1,sK2),sK1)
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(k4_xboole_0(sK1,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_396])])).

fof(f10811,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_xboole_0(X1,sK2),sK1)
        | ~ r2_hidden(k4_xboole_0(sK1,sK2),X1)
        | r2_hidden(sK2,sK2)
        | ~ r2_hidden(sK2,X1) )
    | ~ spl8_259 ),
    inference(resolution,[],[f8752,f2119])).

fof(f10008,plain,
    ( ~ spl8_395
    | ~ spl8_352 ),
    inference(avatar_split_clause,[],[f9997,f8271,f10006])).

fof(f9997,plain,
    ( ~ r2_hidden(sK2,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_352 ),
    inference(resolution,[],[f8272,f57])).

fof(f9913,plain,
    ( spl8_340
    | ~ spl8_106
    | ~ spl8_280 ),
    inference(avatar_split_clause,[],[f9897,f6678,f1040,f8126])).

fof(f8126,plain,
    ( spl8_340
  <=> k4_xboole_0(sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_340])])).

fof(f6678,plain,
    ( spl8_280
  <=> r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_280])])).

fof(f9897,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ spl8_106
    | ~ spl8_280 ),
    inference(resolution,[],[f6966,f6679])).

fof(f6679,plain,
    ( r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl8_280 ),
    inference(avatar_component_clause,[],[f6678])).

fof(f9774,plain,
    ( ~ spl8_393
    | ~ spl8_233
    | ~ spl8_274 ),
    inference(avatar_split_clause,[],[f9739,f6665,f6333,f9772])).

fof(f9772,plain,
    ( spl8_393
  <=> ~ sP5(sK1,k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_393])])).

fof(f6665,plain,
    ( spl8_274
  <=> ! [X165] :
        ( ~ sP5(sK1,X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_274])])).

fof(f9739,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ sP5(sK1,k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl8_274 ),
    inference(superposition,[],[f6666,f51])).

fof(f6666,plain,
    ( ! [X165] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0))
        | ~ sP5(sK1,X165,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_274 ),
    inference(avatar_component_clause,[],[f6665])).

fof(f9767,plain,
    ( ~ spl8_233
    | spl8_390
    | ~ spl8_274 ),
    inference(avatar_split_clause,[],[f9735,f6665,f9765,f6333])).

fof(f9765,plain,
    ( spl8_390
  <=> ! [X2] : ~ sP5(sK1,X2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_390])])).

fof(f9735,plain,
    ( ! [X2] :
        ( ~ sP5(sK1,X2,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) )
    | ~ spl8_274 ),
    inference(resolution,[],[f6666,f245])).

fof(f9763,plain,
    ( ~ spl8_389
    | ~ spl8_274
    | ~ spl8_302 ),
    inference(avatar_split_clause,[],[f9733,f6733,f6665,f9761])).

fof(f9761,plain,
    ( spl8_389
  <=> ~ sP5(sK1,sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_389])])).

fof(f6733,plain,
    ( spl8_302
  <=> m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_302])])).

fof(f9733,plain,
    ( ~ sP5(sK1,sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_274
    | ~ spl8_302 ),
    inference(resolution,[],[f6666,f6734])).

fof(f6734,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0))
    | ~ spl8_302 ),
    inference(avatar_component_clause,[],[f6733])).

fof(f9756,plain,
    ( ~ spl8_387
    | ~ spl8_274
    | ~ spl8_298 ),
    inference(avatar_split_clause,[],[f9732,f6723,f6665,f9754])).

fof(f9754,plain,
    ( spl8_387
  <=> ~ sP5(sK1,sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_387])])).

fof(f6723,plain,
    ( spl8_298
  <=> m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_298])])).

fof(f9732,plain,
    ( ~ sP5(sK1,sK2,k4_xboole_0(sK1,sK2))
    | ~ spl8_274
    | ~ spl8_298 ),
    inference(resolution,[],[f6666,f6724])).

fof(f6724,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0))
    | ~ spl8_298 ),
    inference(avatar_component_clause,[],[f6723])).

fof(f9749,plain,
    ( ~ spl8_385
    | ~ spl8_240
    | ~ spl8_274 ),
    inference(avatar_split_clause,[],[f9730,f6665,f6583,f9747])).

fof(f9747,plain,
    ( spl8_385
  <=> ~ sP5(sK1,k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_385])])).

fof(f6583,plain,
    ( spl8_240
  <=> m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_240])])).

fof(f9730,plain,
    ( ~ sP5(sK1,k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl8_240
    | ~ spl8_274 ),
    inference(resolution,[],[f6666,f6584])).

fof(f6584,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl8_240 ),
    inference(avatar_component_clause,[],[f6583])).

fof(f9037,plain,
    ( spl8_76
    | spl8_382
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f9033,f1211,f9035,f649])).

fof(f9035,plain,
    ( spl8_382
  <=> ! [X18,X19] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,sK3))
        | sP5(sK4(k1_xboole_0,X19,sK3),k4_xboole_0(sK1,X18),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_382])])).

fof(f9033,plain,
    ( ! [X19,X18] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,sK3))
        | k1_xboole_0 = sK3
        | sP5(sK4(k1_xboole_0,X19,sK3),k4_xboole_0(sK1,X18),sK3) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f9032,f3648])).

fof(f9032,plain,
    ( ! [X19,X18] :
        ( k1_xboole_0 = sK3
        | sP5(sK4(k1_xboole_0,X19,sK3),k4_xboole_0(sK1,X18),sK3)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,k4_xboole_0(sK3,k4_xboole_0(sK1,X18)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8975,f3648])).

fof(f8975,plain,
    ( ! [X19,X18] :
        ( sP5(sK4(k1_xboole_0,X19,sK3),k4_xboole_0(sK1,X18),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X18)) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,k4_xboole_0(sK3,k4_xboole_0(sK1,X18)))) )
    | ~ spl8_116 ),
    inference(superposition,[],[f1889,f3648])).

fof(f9031,plain,
    ( spl8_76
    | spl8_380
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f9027,f1211,f9029,f649])).

fof(f9029,plain,
    ( spl8_380
  <=> ! [X17] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X17,sK3))
        | sP5(sK4(k1_xboole_0,X17,sK3),sK1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_380])])).

fof(f9027,plain,
    ( ! [X17] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X17,sK3))
        | k1_xboole_0 = sK3
        | sP5(sK4(k1_xboole_0,X17,sK3),sK1,sK3) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f9026,f1212])).

fof(f9026,plain,
    ( ! [X17] :
        ( k1_xboole_0 = sK3
        | sP5(sK4(k1_xboole_0,X17,sK3),sK1,sK3)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X17,k4_xboole_0(sK3,sK1))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8974,f1212])).

fof(f8974,plain,
    ( ! [X17] :
        ( sP5(sK4(k1_xboole_0,X17,sK3),sK1,sK3)
        | k4_xboole_0(sK3,sK1) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X17,k4_xboole_0(sK3,sK1))) )
    | ~ spl8_116 ),
    inference(superposition,[],[f1889,f1212])).

fof(f9025,plain,
    ( spl8_192
    | spl8_378
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f9021,f1211,f9023,f5043])).

fof(f9023,plain,
    ( spl8_378
  <=> ! [X16,X15] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X16,sK1))
        | sP5(sK4(k1_xboole_0,X16,sK1),k4_xboole_0(sK3,X15),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_378])])).

fof(f9021,plain,
    ( ! [X15,X16] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X16,sK1))
        | k1_xboole_0 = sK1
        | sP5(sK4(k1_xboole_0,X16,sK1),k4_xboole_0(sK3,X15),sK1) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f9020,f5148])).

fof(f9020,plain,
    ( ! [X15,X16] :
        ( k1_xboole_0 = sK1
        | sP5(sK4(k1_xboole_0,X16,sK1),k4_xboole_0(sK3,X15),sK1)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X16,k4_xboole_0(sK1,k4_xboole_0(sK3,X15)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8973,f5148])).

fof(f8973,plain,
    ( ! [X15,X16] :
        ( sP5(sK4(k1_xboole_0,X16,sK1),k4_xboole_0(sK3,X15),sK1)
        | k4_xboole_0(sK1,k4_xboole_0(sK3,X15)) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X16,k4_xboole_0(sK1,k4_xboole_0(sK3,X15)))) )
    | ~ spl8_116 ),
    inference(superposition,[],[f1889,f5148])).

fof(f9019,plain,
    ( spl8_192
    | spl8_376
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f9015,f1040,f9017,f5043])).

fof(f9017,plain,
    ( spl8_376
  <=> ! [X14] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X14,sK1))
        | sP5(sK4(k1_xboole_0,X14,sK1),sK3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_376])])).

fof(f9015,plain,
    ( ! [X14] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X14,sK1))
        | k1_xboole_0 = sK1
        | sP5(sK4(k1_xboole_0,X14,sK1),sK3,sK1) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f9014,f1041])).

fof(f9014,plain,
    ( ! [X14] :
        ( k1_xboole_0 = sK1
        | sP5(sK4(k1_xboole_0,X14,sK1),sK3,sK1)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X14,k4_xboole_0(sK1,sK3))) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f8972,f1041])).

fof(f8972,plain,
    ( ! [X14] :
        ( sP5(sK4(k1_xboole_0,X14,sK1),sK3,sK1)
        | k4_xboole_0(sK1,sK3) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X14,k4_xboole_0(sK1,sK3))) )
    | ~ spl8_106 ),
    inference(superposition,[],[f1889,f1041])).

fof(f8996,plain,
    ( spl8_192
    | spl8_374
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f8992,f1211,f8994,f5043])).

fof(f8994,plain,
    ( spl8_374
  <=> ! [X40] :
        ( ~ sP5(sK1,k1_xboole_0,sK4(k1_xboole_0,X40,sK1))
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X40,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_374])])).

fof(f8992,plain,
    ( ! [X40] :
        ( ~ sP5(sK1,k1_xboole_0,sK4(k1_xboole_0,X40,sK1))
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X40,sK1))
        | k1_xboole_0 = sK1 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8991,f5148])).

fof(f8991,plain,
    ( ! [X39,X40] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X40,sK1))
        | k1_xboole_0 = sK1
        | ~ sP5(sK1,k1_xboole_0,sK4(k1_xboole_0,X40,k4_xboole_0(sK1,k4_xboole_0(sK3,X39)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8990,f5148])).

fof(f8990,plain,
    ( ! [X39,X40] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X40,k4_xboole_0(sK1,k4_xboole_0(sK3,X39))))
        | ~ sP5(sK1,k1_xboole_0,sK4(k1_xboole_0,X40,k4_xboole_0(sK1,k4_xboole_0(sK3,X39)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8958,f5148])).

fof(f8958,plain,
    ( ! [X39,X40] :
        ( k4_xboole_0(sK1,k4_xboole_0(sK3,X39)) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X40,k4_xboole_0(sK1,k4_xboole_0(sK3,X39))))
        | ~ sP5(sK1,k1_xboole_0,sK4(k1_xboole_0,X40,k4_xboole_0(sK1,k4_xboole_0(sK3,X39)))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f1889,f5206])).

fof(f5206,plain,
    ( ! [X99,X100] :
        ( ~ sP5(X100,k4_xboole_0(sK3,X99),sK1)
        | ~ sP5(sK1,k1_xboole_0,X100) )
    | ~ spl8_116 ),
    inference(superposition,[],[f922,f5148])).

fof(f8986,plain,
    ( spl8_76
    | spl8_372
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f8982,f1211,f8984,f649])).

fof(f8984,plain,
    ( spl8_372
  <=> ! [X36] :
        ( ~ sP5(sK3,k1_xboole_0,sK4(k1_xboole_0,X36,sK3))
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X36,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_372])])).

fof(f8982,plain,
    ( ! [X36] :
        ( ~ sP5(sK3,k1_xboole_0,sK4(k1_xboole_0,X36,sK3))
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X36,sK3))
        | k1_xboole_0 = sK3 )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8981,f3648])).

fof(f8981,plain,
    ( ! [X35,X36] :
        ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X36,sK3))
        | k1_xboole_0 = sK3
        | ~ sP5(sK3,k1_xboole_0,sK4(k1_xboole_0,X36,k4_xboole_0(sK3,k4_xboole_0(sK1,X35)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8980,f3648])).

fof(f8980,plain,
    ( ! [X35,X36] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X36,k4_xboole_0(sK3,k4_xboole_0(sK1,X35))))
        | ~ sP5(sK3,k1_xboole_0,sK4(k1_xboole_0,X36,k4_xboole_0(sK3,k4_xboole_0(sK1,X35)))) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f8956,f3648])).

fof(f8956,plain,
    ( ! [X35,X36] :
        ( k4_xboole_0(sK3,k4_xboole_0(sK1,X35)) = k1_xboole_0
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X36,k4_xboole_0(sK3,k4_xboole_0(sK1,X35))))
        | ~ sP5(sK3,k1_xboole_0,sK4(k1_xboole_0,X36,k4_xboole_0(sK3,k4_xboole_0(sK1,X35)))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f1889,f3732])).

fof(f3732,plain,
    ( ! [X76,X77] :
        ( ~ sP5(X77,k4_xboole_0(sK1,X76),sK3)
        | ~ sP5(sK3,k1_xboole_0,X77) )
    | ~ spl8_116 ),
    inference(superposition,[],[f922,f3648])).

fof(f8851,plain,
    ( ~ spl8_371
    | ~ spl8_233
    | ~ spl8_264 ),
    inference(avatar_split_clause,[],[f8809,f6641,f6333,f8849])).

fof(f8849,plain,
    ( spl8_371
  <=> ~ sP5(sK3,k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_371])])).

fof(f6641,plain,
    ( spl8_264
  <=> ! [X161] :
        ( ~ sP5(sK3,X161,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X161),k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_264])])).

fof(f8809,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ sP5(sK3,k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl8_264 ),
    inference(superposition,[],[f6642,f51])).

fof(f6642,plain,
    ( ! [X161] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X161),k1_zfmisc_1(sK0))
        | ~ sP5(sK3,X161,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_264 ),
    inference(avatar_component_clause,[],[f6641])).

fof(f8844,plain,
    ( ~ spl8_233
    | spl8_368
    | ~ spl8_264 ),
    inference(avatar_split_clause,[],[f8805,f6641,f8842,f6333])).

fof(f8842,plain,
    ( spl8_368
  <=> ! [X2] : ~ sP5(sK3,X2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_368])])).

fof(f8805,plain,
    ( ! [X2] :
        ( ~ sP5(sK3,X2,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) )
    | ~ spl8_264 ),
    inference(resolution,[],[f6642,f245])).

fof(f8840,plain,
    ( ~ spl8_367
    | ~ spl8_264
    | ~ spl8_302 ),
    inference(avatar_split_clause,[],[f8803,f6733,f6641,f8838])).

fof(f8838,plain,
    ( spl8_367
  <=> ~ sP5(sK3,sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_367])])).

fof(f8803,plain,
    ( ~ sP5(sK3,sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_264
    | ~ spl8_302 ),
    inference(resolution,[],[f6642,f6734])).

fof(f8833,plain,
    ( ~ spl8_365
    | ~ spl8_264
    | ~ spl8_298 ),
    inference(avatar_split_clause,[],[f8802,f6723,f6641,f8831])).

fof(f8831,plain,
    ( spl8_365
  <=> ~ sP5(sK3,sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_365])])).

fof(f8802,plain,
    ( ~ sP5(sK3,sK2,k4_xboole_0(sK1,sK2))
    | ~ spl8_264
    | ~ spl8_298 ),
    inference(resolution,[],[f6642,f6724])).

fof(f8826,plain,
    ( ~ spl8_363
    | ~ spl8_264
    | ~ spl8_284 ),
    inference(avatar_split_clause,[],[f8801,f6689,f6641,f8824])).

fof(f8824,plain,
    ( spl8_363
  <=> ~ sP5(sK3,sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_363])])).

fof(f6689,plain,
    ( spl8_284
  <=> m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_284])])).

fof(f8801,plain,
    ( ~ sP5(sK3,sK1,k4_xboole_0(sK1,sK2))
    | ~ spl8_264
    | ~ spl8_284 ),
    inference(resolution,[],[f6642,f6690])).

fof(f6690,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0))
    | ~ spl8_284 ),
    inference(avatar_component_clause,[],[f6689])).

fof(f8819,plain,
    ( ~ spl8_361
    | ~ spl8_240
    | ~ spl8_264 ),
    inference(avatar_split_clause,[],[f8800,f6641,f6583,f8817])).

fof(f8817,plain,
    ( spl8_361
  <=> ~ sP5(sK3,k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_361])])).

fof(f8800,plain,
    ( ~ sP5(sK3,k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl8_240
    | ~ spl8_264 ),
    inference(resolution,[],[f6642,f6584])).

fof(f8649,plain,
    ( ~ spl8_357
    | ~ spl8_280 ),
    inference(avatar_split_clause,[],[f8644,f6678,f8431])).

fof(f8644,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_280 ),
    inference(resolution,[],[f6679,f57])).

fof(f8527,plain,
    ( ~ spl8_359
    | ~ spl8_349
    | spl8_340
    | ~ spl8_106
    | ~ spl8_346 ),
    inference(avatar_split_clause,[],[f8520,f8144,f1040,f8126,f8259,f8525])).

fof(f8259,plain,
    ( spl8_349
  <=> ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_349])])).

fof(f8144,plain,
    ( spl8_346
  <=> sP5(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_346])])).

fof(f8520,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_106
    | ~ spl8_346 ),
    inference(forward_demodulation,[],[f8515,f1041])).

fof(f8515,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK3,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ spl8_346 ),
    inference(resolution,[],[f8145,f1381])).

fof(f8145,plain,
    ( sP5(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl8_346 ),
    inference(avatar_component_clause,[],[f8144])).

fof(f8519,plain,
    ( ~ spl8_353
    | ~ spl8_346 ),
    inference(avatar_split_clause,[],[f8513,f8144,f8274])).

fof(f8274,plain,
    ( spl8_353
  <=> ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_353])])).

fof(f8513,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_346 ),
    inference(resolution,[],[f8145,f39])).

fof(f8433,plain,
    ( ~ spl8_357
    | spl8_340
    | ~ spl8_106
    | spl8_349 ),
    inference(avatar_split_clause,[],[f8426,f8259,f1040,f8126,f8431])).

fof(f8426,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ r2_hidden(k4_xboole_0(sK1,sK2),sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_106
    | ~ spl8_349 ),
    inference(forward_demodulation,[],[f8407,f1041])).

fof(f8407,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ r2_hidden(k4_xboole_0(sK1,sK2),sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | ~ spl8_349 ),
    inference(resolution,[],[f8260,f416])).

fof(f8260,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_349 ),
    inference(avatar_component_clause,[],[f8259])).

fof(f8425,plain,
    ( ~ spl8_355
    | spl8_340
    | ~ spl8_106
    | spl8_349 ),
    inference(avatar_split_clause,[],[f8418,f8259,f1040,f8126,f8423])).

fof(f8423,plain,
    ( spl8_355
  <=> ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_355])])).

fof(f8418,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl8_106
    | ~ spl8_349 ),
    inference(forward_demodulation,[],[f8406,f1041])).

fof(f8406,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl8_349 ),
    inference(resolution,[],[f8260,f4199])).

fof(f8417,plain,
    ( spl8_340
    | ~ spl8_106
    | spl8_349 ),
    inference(avatar_split_clause,[],[f8416,f8259,f1040,f8126])).

fof(f8416,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ spl8_106
    | ~ spl8_349 ),
    inference(forward_demodulation,[],[f8404,f1041])).

fof(f8404,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ spl8_349 ),
    inference(resolution,[],[f8260,f3016])).

fof(f8415,plain,
    ( ~ spl8_353
    | spl8_340
    | ~ spl8_106
    | spl8_349 ),
    inference(avatar_split_clause,[],[f8414,f8259,f1040,f8126,f8274])).

fof(f8414,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_106
    | ~ spl8_349 ),
    inference(forward_demodulation,[],[f8403,f1041])).

fof(f8403,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_349 ),
    inference(resolution,[],[f8260,f1513])).

fof(f8357,plain,
    ( ~ spl8_349
    | spl8_352
    | spl8_347 ),
    inference(avatar_split_clause,[],[f8351,f8147,f8271,f8259])).

fof(f8351,plain,
    ( r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_347 ),
    inference(resolution,[],[f8148,f37])).

fof(f8276,plain,
    ( spl8_348
    | ~ spl8_351
    | ~ spl8_353
    | spl8_345 ),
    inference(avatar_split_clause,[],[f8253,f8140,f8274,f8268,f8262])).

fof(f8253,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK0)
    | r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_345 ),
    inference(resolution,[],[f8141,f32])).

fof(f8149,plain,
    ( ~ spl8_347
    | spl8_281 ),
    inference(avatar_split_clause,[],[f8117,f6681,f8147])).

fof(f8117,plain,
    ( ~ sP5(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl8_281 ),
    inference(resolution,[],[f6682,f60])).

fof(f8142,plain,
    ( ~ spl8_345
    | spl8_340
    | ~ spl8_106
    | spl8_281 ),
    inference(avatar_split_clause,[],[f8135,f6681,f1040,f8126,f8140])).

fof(f8135,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK3)
    | ~ spl8_106
    | ~ spl8_281 ),
    inference(forward_demodulation,[],[f8116,f1041])).

fof(f8116,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),sK3)
    | ~ spl8_281 ),
    inference(resolution,[],[f6682,f281])).

fof(f8134,plain,
    ( spl8_340
    | ~ spl8_343
    | ~ spl8_106
    | spl8_281 ),
    inference(avatar_split_clause,[],[f8111,f6681,f1040,f8132,f8126])).

fof(f8132,plain,
    ( spl8_343
  <=> ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_343])])).

fof(f8111,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK1,sK2)))
    | k4_xboole_0(sK1,sK2) = sK1
    | ~ spl8_106
    | ~ spl8_281 ),
    inference(resolution,[],[f6682,f4788])).

fof(f8020,plain,
    ( ~ spl8_233
    | spl8_241 ),
    inference(avatar_split_clause,[],[f8013,f6586,f6333])).

fof(f8013,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_241 ),
    inference(resolution,[],[f6587,f245])).

fof(f6587,plain,
    ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl8_241 ),
    inference(avatar_component_clause,[],[f6586])).

fof(f7923,plain,
    ( ~ spl8_233
    | spl8_303 ),
    inference(avatar_split_clause,[],[f7916,f6736,f6333])).

fof(f7916,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_303 ),
    inference(resolution,[],[f6737,f245])).

fof(f6737,plain,
    ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0))
    | ~ spl8_303 ),
    inference(avatar_component_clause,[],[f6736])).

fof(f7865,plain,
    ( ~ spl8_233
    | spl8_299 ),
    inference(avatar_split_clause,[],[f7858,f6726,f6333])).

fof(f7858,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_299 ),
    inference(resolution,[],[f6727,f245])).

fof(f6727,plain,
    ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0))
    | ~ spl8_299 ),
    inference(avatar_component_clause,[],[f6726])).

fof(f7570,plain,
    ( ~ spl8_339
    | spl8_331 ),
    inference(avatar_split_clause,[],[f7558,f7451,f7568])).

fof(f7451,plain,
    ( spl8_331
  <=> ~ r2_hidden(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_331])])).

fof(f7558,plain,
    ( ~ sP5(k1_xboole_0,sK2,sK1)
    | ~ spl8_331 ),
    inference(resolution,[],[f7452,f60])).

fof(f7452,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl8_331 ),
    inference(avatar_component_clause,[],[f7451])).

fof(f7538,plain,
    ( ~ spl8_331
    | spl8_52
    | spl8_327 ),
    inference(avatar_split_clause,[],[f7533,f7394,f303,f7451])).

fof(f7394,plain,
    ( spl8_327
  <=> ~ sP5(k1_xboole_0,sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_327])])).

fof(f7533,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ r2_hidden(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl8_327 ),
    inference(resolution,[],[f7395,f37])).

fof(f7395,plain,
    ( ~ sP5(k1_xboole_0,sK1,k4_xboole_0(sK1,sK2))
    | ~ spl8_327 ),
    inference(avatar_component_clause,[],[f7394])).

fof(f7486,plain,
    ( spl8_334
    | ~ spl8_337
    | ~ spl8_328 ),
    inference(avatar_split_clause,[],[f7469,f7440,f7484,f7477])).

fof(f7469,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | k4_xboole_0(sK1,sK2) = sK3
    | ~ spl8_328 ),
    inference(resolution,[],[f7441,f48])).

fof(f7441,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_328 ),
    inference(avatar_component_clause,[],[f7440])).

fof(f7479,plain,
    ( spl8_334
    | ~ spl8_7
    | ~ spl8_234
    | ~ spl8_328 ),
    inference(avatar_split_clause,[],[f7468,f7440,f6336,f85,f7477])).

fof(f7468,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | k4_xboole_0(sK1,sK2) = sK3
    | ~ spl8_234
    | ~ spl8_328 ),
    inference(resolution,[],[f7441,f6400])).

fof(f7465,plain,
    ( ~ spl8_333
    | spl8_198
    | ~ spl8_116
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f7352,f7255,f1211,f5310,f7463])).

fof(f7463,plain,
    ( spl8_333
  <=> ~ sP5(sK1,sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_333])])).

fof(f5310,plain,
    ( spl8_198
  <=> ! [X178] : ~ sP5(sK3,k4_xboole_0(sK3,X178),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_198])])).

fof(f7255,plain,
    ( spl8_324
  <=> k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_324])])).

fof(f7352,plain,
    ( ! [X105] :
        ( ~ sP5(sK3,k4_xboole_0(sK3,X105),sK1)
        | ~ sP5(sK1,sK1,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_116
    | ~ spl8_324 ),
    inference(superposition,[],[f5184,f7256])).

fof(f7256,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = sK3
    | ~ spl8_324 ),
    inference(avatar_component_clause,[],[f7255])).

fof(f7453,plain,
    ( ~ spl8_331
    | spl8_52
    | ~ spl8_57
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f7343,f7255,f328,f303,f7451])).

fof(f328,plain,
    ( spl8_57
  <=> ~ r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f7343,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | r2_hidden(k1_xboole_0,sK1)
    | ~ r2_hidden(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl8_324 ),
    inference(superposition,[],[f2117,f7256])).

fof(f2117,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(k4_xboole_0(X18,X17),k1_xboole_0)
      | r2_hidden(k1_xboole_0,X17)
      | ~ r2_hidden(k1_xboole_0,X18) ) ),
    inference(forward_demodulation,[],[f2116,f50])).

fof(f2116,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(k1_xboole_0,X17)
      | ~ r2_hidden(k4_xboole_0(k1_xboole_0,X16),X18)
      | ~ r2_hidden(k4_xboole_0(X18,X17),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f2108,f50])).

fof(f2108,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(k4_xboole_0(k1_xboole_0,X16),X17)
      | ~ r2_hidden(k4_xboole_0(k1_xboole_0,X16),X18)
      | ~ r2_hidden(k4_xboole_0(X18,X17),k1_xboole_0) ) ),
    inference(resolution,[],[f918,f185])).

fof(f7442,plain,
    ( spl8_236
    | spl8_328
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f7340,f7255,f7440,f6454])).

fof(f6454,plain,
    ( spl8_236
  <=> ! [X7] : ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_236])])).

fof(f7340,plain,
    ( ! [X99] :
        ( r1_tarski(sK3,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X99)) )
    | ~ spl8_324 ),
    inference(superposition,[],[f1946,f7256])).

fof(f7396,plain,
    ( ~ spl8_327
    | spl8_142
    | ~ spl8_324 ),
    inference(avatar_split_clause,[],[f7314,f7255,f2199,f7394])).

fof(f2199,plain,
    ( spl8_142
  <=> ! [X35] : ~ sP5(sK3,X35,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f7314,plain,
    ( ! [X49] :
        ( ~ sP5(sK3,X49,k1_xboole_0)
        | ~ sP5(k1_xboole_0,sK1,k4_xboole_0(sK1,sK2)) )
    | ~ spl8_324 ),
    inference(superposition,[],[f921,f7256])).

fof(f921,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(k4_xboole_0(X2,X1),X0,k1_xboole_0)
      | ~ sP5(k1_xboole_0,X1,X2) ) ),
    inference(superposition,[],[f337,f50])).

fof(f7257,plain,
    ( spl8_324
    | ~ spl8_295
    | ~ spl8_290 ),
    inference(avatar_split_clause,[],[f7244,f6706,f6713,f7255])).

fof(f6713,plain,
    ( spl8_295
  <=> ~ r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_295])])).

fof(f6706,plain,
    ( spl8_290
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_290])])).

fof(f7244,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
    | k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = sK3
    | ~ spl8_290 ),
    inference(resolution,[],[f6707,f48])).

fof(f6707,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3)
    | ~ spl8_290 ),
    inference(avatar_component_clause,[],[f6706])).

fof(f7239,plain,
    ( spl8_46
    | spl8_322 ),
    inference(avatar_split_clause,[],[f7235,f7237,f247])).

fof(f7235,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK3),sK1),sK0)
      | r1_tarski(k4_xboole_0(sK2,sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f7226])).

fof(f7226,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK3),sK1),sK0)
      | r1_tarski(k4_xboole_0(sK2,sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
      | r1_tarski(k4_xboole_0(sK2,sK3),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f5940,f444])).

fof(f7225,plain,
    ( ~ spl8_233
    | spl8_285 ),
    inference(avatar_split_clause,[],[f7218,f6692,f6333])).

fof(f7218,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_285 ),
    inference(resolution,[],[f6693,f245])).

fof(f6693,plain,
    ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0))
    | ~ spl8_285 ),
    inference(avatar_component_clause,[],[f6692])).

fof(f7155,plain,
    ( ~ spl8_319
    | ~ spl8_262 ),
    inference(avatar_split_clause,[],[f7139,f6637,f7148])).

fof(f7148,plain,
    ( spl8_319
  <=> ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_319])])).

fof(f6637,plain,
    ( spl8_262
  <=> ! [X81] : ~ sP5(k4_xboole_0(sK1,sK2),X81,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_262])])).

fof(f7139,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl8_262 ),
    inference(resolution,[],[f6638,f186])).

fof(f6638,plain,
    ( ! [X81] : ~ sP5(k4_xboole_0(sK1,sK2),X81,k1_xboole_0)
    | ~ spl8_262 ),
    inference(avatar_component_clause,[],[f6637])).

fof(f7154,plain,
    ( ~ spl8_319
    | spl8_320
    | ~ spl8_262 ),
    inference(avatar_split_clause,[],[f7138,f6637,f7152,f7148])).

fof(f7138,plain,
    ( ! [X2] :
        ( r2_hidden(k4_xboole_0(sK1,sK2),X2)
        | ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_xboole_0) )
    | ~ spl8_262 ),
    inference(resolution,[],[f6638,f37])).

fof(f7150,plain,
    ( ~ spl8_319
    | ~ spl8_262 ),
    inference(avatar_split_clause,[],[f7134,f6637,f7148])).

fof(f7134,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl8_262 ),
    inference(resolution,[],[f6638,f185])).

fof(f7055,plain,
    ( ~ spl8_17
    | spl8_20
    | spl8_313 ),
    inference(avatar_split_clause,[],[f7054,f6826,f137,f127])).

fof(f127,plain,
    ( spl8_17
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f6826,plain,
    ( spl8_313
  <=> ~ sP5(sK2,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_313])])).

fof(f7054,plain,
    ( r2_hidden(sK2,sK2)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl8_313 ),
    inference(resolution,[],[f6827,f37])).

fof(f6827,plain,
    ( ~ sP5(sK2,sK2,sK1)
    | ~ spl8_313 ),
    inference(avatar_component_clause,[],[f6826])).

fof(f7011,plain,
    ( ~ spl8_313
    | spl8_271 ),
    inference(avatar_split_clause,[],[f7006,f6658,f6826])).

fof(f7006,plain,
    ( ~ sP5(sK2,sK2,sK1)
    | ~ spl8_271 ),
    inference(resolution,[],[f6659,f60])).

fof(f6882,plain,
    ( ~ spl8_317
    | spl8_255 ),
    inference(avatar_split_clause,[],[f6871,f6619,f6880])).

fof(f6880,plain,
    ( spl8_317
  <=> ~ sP5(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_317])])).

fof(f6619,plain,
    ( spl8_255
  <=> ~ r2_hidden(sK3,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_255])])).

fof(f6871,plain,
    ( ~ sP5(sK3,sK2,sK1)
    | ~ spl8_255 ),
    inference(resolution,[],[f6620,f60])).

fof(f6620,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK1,sK2))
    | ~ spl8_255 ),
    inference(avatar_component_clause,[],[f6619])).

fof(f6835,plain,
    ( ~ spl8_315
    | ~ spl8_246 ),
    inference(avatar_split_clause,[],[f6807,f6596,f6833])).

fof(f6833,plain,
    ( spl8_315
  <=> ~ sP5(sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_315])])).

fof(f6807,plain,
    ( ~ sP5(sK1,sK2,sK1)
    | ~ spl8_246 ),
    inference(resolution,[],[f6597,f230])).

fof(f6828,plain,
    ( ~ spl8_313
    | ~ spl8_311
    | ~ spl8_246 ),
    inference(avatar_split_clause,[],[f6805,f6596,f6819,f6826])).

fof(f6819,plain,
    ( spl8_311
  <=> ~ m1_subset_1(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_311])])).

fof(f6805,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),sK0)
    | ~ sP5(sK2,sK2,sK1)
    | ~ spl8_246 ),
    inference(resolution,[],[f6597,f232])).

fof(f6821,plain,
    ( ~ spl8_17
    | spl8_20
    | ~ spl8_311
    | ~ spl8_246 ),
    inference(avatar_split_clause,[],[f6804,f6596,f6819,f137,f127])).

fof(f6804,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK2,sK2)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl8_246 ),
    inference(resolution,[],[f6597,f4400])).

fof(f6767,plain,
    ( ~ spl8_232
    | ~ spl8_236 ),
    inference(avatar_contradiction_clause,[],[f6763])).

fof(f6763,plain,
    ( $false
    | ~ spl8_232
    | ~ spl8_236 ),
    inference(resolution,[],[f6455,f6331])).

fof(f6455,plain,
    ( ! [X7] : ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X7))
    | ~ spl8_236 ),
    inference(avatar_component_clause,[],[f6454])).

fof(f6751,plain,
    ( ~ spl8_303
    | spl8_308
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6580,f6457,f6749,f6736])).

fof(f6749,plain,
    ( spl8_308
  <=> ! [X190,X189] :
        ( ~ r2_hidden(sK6(X189,X190,k4_xboole_0(sK1,sK2)),sK1)
        | r1_tarski(X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))
        | ~ m1_subset_1(sK6(X189,X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),sK0)
        | ~ r2_hidden(sK6(X189,X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X190,k1_zfmisc_1(X189))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X189)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_308])])).

fof(f6580,plain,
    ( ! [X189,X190] :
        ( ~ r2_hidden(sK6(X189,X190,k4_xboole_0(sK1,sK2)),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X189))
        | ~ m1_subset_1(X190,k1_zfmisc_1(X189))
        | ~ r2_hidden(sK6(X189,X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK6(X189,X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),sK0)
        | r1_tarski(X190,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1672,f6458])).

fof(f6747,plain,
    ( ~ spl8_303
    | spl8_304
    | spl8_306
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6578,f6457,f1040,f6745,f6742,f6736])).

fof(f6742,plain,
    ( spl8_304
  <=> r1_tarski(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_304])])).

fof(f6745,plain,
    ( spl8_306
  <=> ! [X186] :
        ( ~ r2_hidden(sK6(X186,sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X186))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X186)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_306])])).

fof(f6578,plain,
    ( ! [X186] :
        ( ~ r2_hidden(sK6(X186,sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X186))
        | r1_tarski(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(X186))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK3),k1_zfmisc_1(sK0)) )
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(superposition,[],[f4557,f6458])).

fof(f6731,plain,
    ( ~ spl8_299
    | spl8_300
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6577,f6457,f6729,f6726])).

fof(f6729,plain,
    ( spl8_300
  <=> ! [X184,X185] :
        ( ~ r2_hidden(sK6(X184,k4_xboole_0(sK1,sK2),X185),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(X184))
        | ~ m1_subset_1(X185,k1_zfmisc_1(X184))
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),X185)
        | ~ m1_subset_1(sK6(X184,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),X185),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_300])])).

fof(f6577,plain,
    ( ! [X185,X184] :
        ( ~ r2_hidden(sK6(X184,k4_xboole_0(sK1,sK2),X185),sK1)
        | ~ m1_subset_1(sK6(X184,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),X185),sK0)
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),X185)
        | ~ m1_subset_1(X185,k1_zfmisc_1(X184))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(X184))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4419,f6458])).

fof(f6721,plain,
    ( ~ spl8_285
    | spl8_294
    | spl8_296
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6576,f6457,f6719,f6716,f6692])).

fof(f6576,plain,
    ( ! [X183] :
        ( ~ r2_hidden(sK6(X183,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X183))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X183))
        | r1_tarski(sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1))
        | ~ m1_subset_1(sK6(X183,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1679,f6458])).

fof(f6711,plain,
    ( ~ spl8_285
    | spl8_290
    | spl8_292
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6575,f6457,f6709,f6706,f6692])).

fof(f6709,plain,
    ( spl8_292
  <=> ! [X182] :
        ( ~ r2_hidden(sK6(X182,k4_xboole_0(sK1,sK2),sK3),sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X182))
        | ~ m1_subset_1(sK6(X182,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X182)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_292])])).

fof(f6575,plain,
    ( ! [X182] :
        ( ~ r2_hidden(sK6(X182,k4_xboole_0(sK1,sK2),sK3),sK2)
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X182))
        | ~ m1_subset_1(sK6(X182,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),sK3),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X182))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4766,f6458])).

fof(f4766,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK6(X5,k4_xboole_0(X4,sK1),sK3),sK2)
      | r1_tarski(k4_xboole_0(X4,sK1),sK3)
      | ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK6(X5,k4_xboole_0(X4,sK1),sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f4759])).

fof(f4759,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5))
      | r1_tarski(k4_xboole_0(X4,sK1),sK3)
      | ~ r2_hidden(sK6(X5,k4_xboole_0(X4,sK1),sK3),sK2)
      | ~ m1_subset_1(sK6(X5,k4_xboole_0(X4,sK1),sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | r1_tarski(k4_xboole_0(X4,sK1),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(k4_xboole_0(X4,sK1),k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f277,f443])).

fof(f277,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK6(X10,X11,sK3),sK1)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | r1_tarski(X11,sK3)
      | ~ r2_hidden(sK6(X10,X11,sK3),sK2)
      | ~ m1_subset_1(sK6(X10,X11,sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X10)) ) ),
    inference(resolution,[],[f56,f32])).

fof(f6701,plain,
    ( ~ spl8_285
    | spl8_288
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6574,f6457,f6699,f6692])).

fof(f6699,plain,
    ( spl8_288
  <=> ! [X181,X180] :
        ( ~ r2_hidden(sK6(X180,k4_xboole_0(sK1,sK2),X181),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X180))
        | ~ m1_subset_1(X181,k1_zfmisc_1(X180))
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181)
        | ~ r2_hidden(sK3,sK6(X180,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181))
        | ~ m1_subset_1(sK6(X180,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_288])])).

fof(f6574,plain,
    ( ! [X180,X181] :
        ( ~ r2_hidden(sK6(X180,k4_xboole_0(sK1,sK2),X181),sK2)
        | ~ m1_subset_1(sK6(X180,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181),sK0)
        | ~ r2_hidden(sK3,sK6(X180,k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181))
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X181)
        | ~ m1_subset_1(X181,k1_zfmisc_1(X180))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X180))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4686,f6458])).

fof(f6697,plain,
    ( ~ spl8_285
    | spl8_286
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6573,f6457,f1040,f6695,f6692])).

fof(f6695,plain,
    ( spl8_286
  <=> ! [X179,X178] :
        ( ~ sP5(sK6(X178,k4_xboole_0(sK1,sK2),X179),sK3,sK1)
        | ~ m1_subset_1(X179,k1_zfmisc_1(X178))
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X179)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X178)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_286])])).

fof(f6573,plain,
    ( ! [X178,X179] :
        ( ~ sP5(sK6(X178,k4_xboole_0(sK1,sK2),X179),sK3,sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(X178))
        | r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),X179)
        | ~ m1_subset_1(X179,k1_zfmisc_1(X178))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k1_zfmisc_1(sK0)) )
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(superposition,[],[f4538,f6458])).

fof(f4538,plain,
    ( ! [X72,X71,X73] :
        ( ~ sP5(sK6(X71,k4_xboole_0(X72,sK1),X73),sK3,sK1)
        | ~ m1_subset_1(k4_xboole_0(X72,sK1),k1_zfmisc_1(X71))
        | r1_tarski(k4_xboole_0(X72,sK1),X73)
        | ~ m1_subset_1(X73,k1_zfmisc_1(X71)) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4537,f1041])).

fof(f4537,plain,
    ( ! [X72,X71,X73] :
        ( ~ m1_subset_1(k4_xboole_0(X72,sK1),k1_zfmisc_1(X71))
        | ~ sP5(sK6(X71,k4_xboole_0(X72,sK1),X73),sK3,sK1)
        | ~ m1_subset_1(X73,k1_zfmisc_1(X71))
        | r1_tarski(k4_xboole_0(X72,k4_xboole_0(sK1,sK3)),X73) )
    | ~ spl8_106 ),
    inference(forward_demodulation,[],[f4472,f1041])).

fof(f4472,plain,
    ( ! [X72,X71,X73] :
        ( ~ sP5(sK6(X71,k4_xboole_0(X72,sK1),X73),sK3,sK1)
        | ~ m1_subset_1(X73,k1_zfmisc_1(X71))
        | ~ m1_subset_1(k4_xboole_0(X72,k4_xboole_0(sK1,sK3)),k1_zfmisc_1(X71))
        | r1_tarski(k4_xboole_0(X72,k4_xboole_0(sK1,sK3)),X73) )
    | ~ spl8_106 ),
    inference(superposition,[],[f1420,f1041])).

fof(f6687,plain,
    ( spl8_274
    | spl8_282
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6570,f6457,f1211,f6685,f6665])).

fof(f6685,plain,
    ( spl8_282
  <=> ! [X169] : ~ sP5(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X169),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_282])])).

fof(f6570,plain,
    ( ! [X169,X168] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X169),sK1)
        | ~ sP5(sK1,X168,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X168),k1_zfmisc_1(sK0)) )
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(superposition,[],[f5184,f6458])).

fof(f6683,plain,
    ( spl8_278
    | ~ spl8_281
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6568,f6457,f1040,f6681,f6675])).

fof(f6675,plain,
    ( spl8_278
  <=> ! [X166] :
        ( k4_xboole_0(k4_xboole_0(sK1,sK2),X166) = sK1
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X166),k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),X166)),X166) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_278])])).

fof(f6568,plain,
    ( ! [X166] :
        ( ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
        | k4_xboole_0(k4_xboole_0(sK1,sK2),X166) = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k4_xboole_0(k4_xboole_0(sK1,sK2),X166)),X166)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X166),k1_zfmisc_1(sK0)) )
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(superposition,[],[f5014,f6458])).

fof(f6673,plain,
    ( spl8_274
    | ~ spl8_277
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6567,f6457,f1040,f6671,f6665])).

fof(f6671,plain,
    ( spl8_277
  <=> ~ sP5(k4_xboole_0(sK1,sK2),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_277])])).

fof(f6567,plain,
    ( ! [X165] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),sK3,sK1)
        | ~ sP5(sK1,X165,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X165),k1_zfmisc_1(sK0)) )
    | ~ spl8_106
    | ~ spl8_238 ),
    inference(superposition,[],[f4442,f6458])).

fof(f6663,plain,
    ( ~ spl8_271
    | spl8_272
    | ~ spl8_247
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6566,f6457,f6599,f6661,f6658])).

fof(f6661,plain,
    ( spl8_272
  <=> ! [X164] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X164),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X164),k1_zfmisc_1(sK0))
        | r2_hidden(sK2,X164) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_272])])).

fof(f6566,plain,
    ( ! [X164] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X164),sK0)
        | r2_hidden(sK2,X164)
        | ~ r2_hidden(sK2,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X164),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f4400,f6458])).

fof(f6653,plain,
    ( spl8_264
    | spl8_268
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6565,f6457,f1211,f6651,f6641])).

fof(f6651,plain,
    ( spl8_268
  <=> ! [X163] : ~ sP5(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X163),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_268])])).

fof(f6565,plain,
    ( ! [X163,X162] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X163),sK3)
        | ~ sP5(sK3,X162,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X162),k1_zfmisc_1(sK0)) )
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(superposition,[],[f3713,f6458])).

fof(f3713,plain,
    ( ! [X26,X24,X25] :
        ( ~ sP5(k4_xboole_0(X26,X25),k4_xboole_0(sK1,X24),sK3)
        | ~ sP5(sK3,X25,X26) )
    | ~ spl8_116 ),
    inference(superposition,[],[f337,f3648])).

fof(f6649,plain,
    ( spl8_264
    | ~ spl8_267
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6564,f6457,f1211,f6647,f6641])).

fof(f6647,plain,
    ( spl8_267
  <=> ~ sP5(k4_xboole_0(sK1,sK2),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_267])])).

fof(f6564,plain,
    ( ! [X161] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),sK1,sK3)
        | ~ sP5(sK3,X161,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X161),k1_zfmisc_1(sK0)) )
    | ~ spl8_116
    | ~ spl8_238 ),
    inference(superposition,[],[f2452,f6458])).

fof(f2452,plain,
    ( ! [X12,X13] :
        ( ~ sP5(k4_xboole_0(X13,X12),sK1,sK3)
        | ~ sP5(sK3,X12,X13) )
    | ~ spl8_116 ),
    inference(superposition,[],[f337,f1212])).

fof(f6639,plain,
    ( spl8_260
    | spl8_262
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6535,f6457,f6637,f6634])).

fof(f6634,plain,
    ( spl8_260
  <=> ! [X80] :
        ( ~ sP5(k1_xboole_0,X80,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X80),k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_260])])).

fof(f6535,plain,
    ( ! [X80,X81] :
        ( ~ sP5(k4_xboole_0(sK1,sK2),X81,k1_xboole_0)
        | ~ sP5(k1_xboole_0,X80,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X80),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f921,f6458])).

fof(f6632,plain,
    ( spl8_256
    | ~ spl8_259
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6530,f6457,f6630,f6624])).

fof(f6624,plain,
    ( spl8_256
  <=> ! [X69] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_zfmisc_1(sK0))
        | ~ sP5(sK3,X69,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK1,X69,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).

fof(f6530,plain,
    ( ! [X69] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),sK0)
        | ~ sP5(sK1,X69,k4_xboole_0(sK1,sK2))
        | ~ sP5(sK3,X69,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f565,f6458])).

fof(f6622,plain,
    ( spl8_248
    | spl8_246
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6516,f6457,f6596,f6603])).

fof(f6603,plain,
    ( spl8_248
  <=> ! [X16] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),k1_zfmisc_1(sK0))
        | ~ sP5(sK3,X16,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_248])])).

fof(f6516,plain,
    ( ! [X31] :
        ( r2_hidden(k4_xboole_0(sK1,sK2),sK1)
        | ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X31),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X31),sK0)
        | ~ sP5(sK3,X31,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X31),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f340,f6458])).

fof(f6621,plain,
    ( spl8_252
    | ~ spl8_255
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6515,f6457,f6619,f6613])).

fof(f6613,plain,
    ( spl8_252
  <=> ! [X30] :
        ( ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),k1_zfmisc_1(sK0))
        | ~ sP5(sK1,X30,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_252])])).

fof(f6515,plain,
    ( ! [X30] :
        ( ~ r2_hidden(sK3,k4_xboole_0(sK1,sK2))
        | ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),sK2)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),sK0)
        | ~ sP5(sK1,X30,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X30),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f338,f6458])).

fof(f6611,plain,
    ( spl8_248
    | ~ spl8_251
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6509,f6457,f6609,f6603])).

fof(f6609,plain,
    ( spl8_251
  <=> ~ r2_hidden(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).

fof(f6509,plain,
    ( ! [X16] :
        ( ~ r2_hidden(sK1,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),sK0)
        | ~ r2_hidden(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),sK2)
        | ~ sP5(sK3,X16,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X16),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f233,f6458])).

fof(f233,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(sK1,k4_xboole_0(X12,X11))
      | ~ m1_subset_1(k4_xboole_0(X12,X11),sK0)
      | ~ r2_hidden(k4_xboole_0(X12,X11),sK2)
      | ~ sP5(sK3,X11,X12) ) ),
    inference(resolution,[],[f60,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f119,f57])).

fof(f6601,plain,
    ( spl8_244
    | ~ spl8_247
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6508,f6457,f6599,f6593])).

fof(f6593,plain,
    ( spl8_244
  <=> ! [X15] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X15),sK0)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X15),k1_zfmisc_1(sK0))
        | ~ sP5(sK2,X15,k4_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_244])])).

fof(f6508,plain,
    ( ! [X15] :
        ( ~ r2_hidden(k4_xboole_0(sK1,sK2),sK1)
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X15),sK0)
        | ~ sP5(sK2,X15,k4_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X15),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f232,f6458])).

fof(f6591,plain,
    ( ~ spl8_241
    | spl8_242
    | ~ spl8_238 ),
    inference(avatar_split_clause,[],[f6503,f6457,f6589,f6586])).

fof(f6589,plain,
    ( spl8_242
  <=> ! [X3,X4] :
        ( r1_tarski(k4_xboole_0(sK1,sK2),X3)
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).

fof(f6503,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k4_xboole_0(sK1,sK2),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X4))
        | ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) )
    | ~ spl8_238 ),
    inference(superposition,[],[f1957,f6458])).

fof(f6459,plain,
    ( spl8_236
    | spl8_238
    | ~ spl8_234 ),
    inference(avatar_split_clause,[],[f6445,f6336,f6457,f6454])).

fof(f6445,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k4_xboole_0(k4_xboole_0(sK1,sK2),X6),k1_zfmisc_1(sK0))
        | k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X6)
        | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X7)) )
    | ~ spl8_234 ),
    inference(resolution,[],[f6400,f1946])).

fof(f6344,plain,
    ( ~ spl8_1
    | spl8_233 ),
    inference(avatar_split_clause,[],[f6340,f6333,f64])).

fof(f6340,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_233 ),
    inference(resolution,[],[f6334,f245])).

fof(f6334,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl8_233 ),
    inference(avatar_component_clause,[],[f6333])).

fof(f6338,plain,
    ( ~ spl8_233
    | spl8_234 ),
    inference(avatar_split_clause,[],[f6328,f6336,f6333])).

fof(f6328,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f6324])).

fof(f6324,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(sK1,sK2),X0) ) ),
    inference(resolution,[],[f5756,f54])).

fof(f5756,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK6(X2,k4_xboole_0(sK1,sK2),X3),sK0)
      | r1_tarski(k4_xboole_0(sK1,sK2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f5746])).

fof(f5746,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK6(X2,k4_xboole_0(sK1,sK2),X3),sK0)
      | r1_tarski(k4_xboole_0(sK1,sK2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X2))
      | r1_tarski(k4_xboole_0(sK1,sK2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f4419,f444])).

fof(f6274,plain,
    ( spl8_166
    | spl8_230
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f6261,f1040,f6272,f4339])).

fof(f6261,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X8))
        | r1_tarski(sK1,k4_xboole_0(sK2,sK3))
        | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(X8))
        | ~ m1_subset_1(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK0)
        | ~ r2_hidden(sK6(X8,sK1,k4_xboole_0(sK2,sK3)),sK1) )
    | ~ spl8_106 ),
    inference(resolution,[],[f4557,f30])).

fof(f6254,plain,
    ( spl8_228
    | spl8_220
    | ~ spl8_223
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f6250,f1211,f1040,f6215,f6209,f6252])).

fof(f6252,plain,
    ( spl8_228
  <=> ! [X10] : sP5(sK4(sK1,sK3,sK3),k4_xboole_0(sK1,X10),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_228])])).

fof(f6209,plain,
    ( spl8_220
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_220])])).

fof(f6215,plain,
    ( spl8_223
  <=> ~ r2_hidden(sK1,sK4(sK1,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_223])])).

fof(f6250,plain,
    ( ! [X10] :
        ( ~ r2_hidden(sK1,sK4(sK1,sK3,sK3))
        | sK1 = sK3
        | sP5(sK4(sK1,sK3,sK3),k4_xboole_0(sK1,X10),sK3) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6249,f3648])).

fof(f6249,plain,
    ( ! [X10] :
        ( sK1 = sK3
        | sP5(sK4(sK1,sK3,sK3),k4_xboole_0(sK1,X10),sK3)
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X10)))) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6197,f3648])).

fof(f6197,plain,
    ( ! [X10] :
        ( sP5(sK4(sK1,sK3,sK3),k4_xboole_0(sK1,X10),sK3)
        | k4_xboole_0(sK3,k4_xboole_0(sK1,X10)) = sK1
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X10)))) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(superposition,[],[f5027,f3648])).

fof(f6248,plain,
    ( spl8_226
    | spl8_220
    | ~ spl8_223
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f6241,f1211,f1040,f6215,f6209,f6246])).

fof(f6246,plain,
    ( spl8_226
  <=> sP5(sK4(sK1,sK3,sK3),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_226])])).

fof(f6241,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,sK3,sK3))
    | sK1 = sK3
    | sP5(sK4(sK1,sK3,sK3),sK1,sK3)
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6240,f1212])).

fof(f6240,plain,
    ( sK1 = sK3
    | sP5(sK4(sK1,sK3,sK3),sK1,sK3)
    | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,sK1)))
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6196,f1212])).

fof(f6196,plain,
    ( sP5(sK4(sK1,sK3,sK3),sK1,sK3)
    | k4_xboole_0(sK3,sK1) = sK1
    | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,sK1)))
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(superposition,[],[f5027,f1212])).

fof(f6223,plain,
    ( spl8_220
    | ~ spl8_223
    | ~ spl8_225
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f6204,f1211,f1040,f6221,f6215,f6209])).

fof(f6221,plain,
    ( spl8_225
  <=> ~ sP5(sK3,k1_xboole_0,sK4(sK1,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_225])])).

fof(f6204,plain,
    ( ~ sP5(sK3,k1_xboole_0,sK4(sK1,sK3,sK3))
    | ~ r2_hidden(sK1,sK4(sK1,sK3,sK3))
    | sK1 = sK3
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6203,f3648])).

fof(f6203,plain,
    ( ! [X17] :
        ( ~ r2_hidden(sK1,sK4(sK1,sK3,sK3))
        | sK1 = sK3
        | ~ sP5(sK3,k1_xboole_0,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X17)))) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6202,f3648])).

fof(f6202,plain,
    ( ! [X17] :
        ( sK1 = sK3
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X17))))
        | ~ sP5(sK3,k1_xboole_0,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X17)))) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f6181,f3648])).

fof(f6181,plain,
    ( ! [X17] :
        ( k4_xboole_0(sK3,k4_xboole_0(sK1,X17)) = sK1
        | ~ r2_hidden(sK1,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X17))))
        | ~ sP5(sK3,k1_xboole_0,sK4(sK1,sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X17)))) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(resolution,[],[f5027,f3732])).

fof(f6169,plain,
    ( spl8_214
    | spl8_216
    | ~ spl8_219 ),
    inference(avatar_split_clause,[],[f6153,f6167,f6161,f6155])).

fof(f6155,plain,
    ( spl8_214
  <=> ! [X0] : ~ r2_hidden(sK4(sK1,sK2,k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_214])])).

fof(f6167,plain,
    ( spl8_219
  <=> ~ m1_subset_1(sK4(sK1,sK2,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_219])])).

fof(f6153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK2,k1_xboole_0),sK0)
      | k4_xboole_0(sK1,sK2) = k1_xboole_0
      | ~ r2_hidden(sK4(sK1,sK2,k1_xboole_0),X0) ) ),
    inference(duplicate_literal_removal,[],[f6144])).

fof(f6144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK2,k1_xboole_0),sK0)
      | k4_xboole_0(sK1,sK2) = k1_xboole_0
      | k4_xboole_0(sK1,sK2) = k1_xboole_0
      | ~ r2_hidden(sK4(sK1,sK2,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f4406,f419])).

fof(f4406,plain,(
    ! [X13] :
      ( ~ r2_hidden(sK4(X13,sK2,k1_xboole_0),sK1)
      | ~ m1_subset_1(sK4(X13,sK2,k1_xboole_0),sK0)
      | k4_xboole_0(X13,sK2) = k1_xboole_0 ) ),
    inference(resolution,[],[f30,f2217])).

fof(f5920,plain,
    ( spl8_212
    | spl8_212
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f5908,f1211,f5918,f5918])).

fof(f5918,plain,
    ( spl8_212
  <=> ! [X15] : ~ sP5(sK1,k4_xboole_0(sK3,X15),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).

fof(f5908,plain,
    ( ! [X15,X16] :
        ( ~ sP5(sK1,k4_xboole_0(sK3,X16),sK1)
        | ~ sP5(sK1,k4_xboole_0(sK3,X15),sK1) )
    | ~ spl8_116 ),
    inference(superposition,[],[f5184,f5148])).

fof(f5809,plain,
    ( spl8_208
    | ~ spl8_211
    | ~ spl8_206 ),
    inference(avatar_split_clause,[],[f5793,f5787,f5807,f5801])).

fof(f5801,plain,
    ( spl8_208
  <=> k4_xboole_0(sK2,sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_208])])).

fof(f5807,plain,
    ( spl8_211
  <=> ~ r1_tarski(sK3,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_211])])).

fof(f5787,plain,
    ( spl8_206
  <=> r1_tarski(k4_xboole_0(sK2,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_206])])).

fof(f5793,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK2,sK1))
    | k4_xboole_0(sK2,sK1) = sK3
    | ~ spl8_206 ),
    inference(resolution,[],[f5788,f48])).

fof(f5788,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK3)
    | ~ spl8_206 ),
    inference(avatar_component_clause,[],[f5787])).

fof(f5789,plain,
    ( spl8_204
    | spl8_206 ),
    inference(avatar_split_clause,[],[f5779,f5787,f5781])).

fof(f5781,plain,
    ( spl8_204
  <=> ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK2,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK1),sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).

fof(f5779,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3)
      | ~ m1_subset_1(k4_xboole_0(sK2,sK1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK1),sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f5770])).

fof(f5770,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3)
      | ~ m1_subset_1(k4_xboole_0(sK2,sK1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,k4_xboole_0(sK2,sK1),sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | r1_tarski(k4_xboole_0(sK2,sK1),sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k4_xboole_0(sK2,sK1),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f4766,f444])).

fof(f5399,plain,
    ( ~ spl8_35
    | spl8_40
    | spl8_177 ),
    inference(avatar_split_clause,[],[f5397,f4576,f211,f195])).

fof(f195,plain,
    ( spl8_35
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f4576,plain,
    ( spl8_177
  <=> ~ sP5(sK1,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).

fof(f5397,plain,
    ( r2_hidden(sK1,sK1)
    | ~ r2_hidden(sK1,sK3)
    | ~ spl8_177 ),
    inference(resolution,[],[f4577,f37])).

fof(f4577,plain,
    ( ~ sP5(sK1,sK1,sK3)
    | ~ spl8_177 ),
    inference(avatar_component_clause,[],[f4576])).

fof(f5398,plain,
    ( ~ spl8_35
    | ~ spl8_116
    | spl8_177 ),
    inference(avatar_split_clause,[],[f5393,f4576,f1211,f195])).

fof(f5393,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl8_116
    | ~ spl8_177 ),
    inference(resolution,[],[f4577,f2445])).

fof(f5366,plain,
    ( ~ spl8_201
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f5353,f4525,f5359])).

fof(f5359,plain,
    ( spl8_201
  <=> ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_201])])).

fof(f4525,plain,
    ( spl8_172
  <=> ! [X51] : ~ sP5(sK1,X51,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_172])])).

fof(f5353,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_172 ),
    inference(resolution,[],[f4526,f186])).

fof(f4526,plain,
    ( ! [X51] : ~ sP5(sK1,X51,k1_xboole_0)
    | ~ spl8_172 ),
    inference(avatar_component_clause,[],[f4525])).

fof(f5365,plain,
    ( ~ spl8_201
    | spl8_202
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f5352,f4525,f5363,f5359])).

fof(f5363,plain,
    ( spl8_202
  <=> ! [X2] : r2_hidden(sK1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_202])])).

fof(f5352,plain,
    ( ! [X2] :
        ( r2_hidden(sK1,X2)
        | ~ r2_hidden(sK1,k1_xboole_0) )
    | ~ spl8_172 ),
    inference(resolution,[],[f4526,f37])).

fof(f5361,plain,
    ( ~ spl8_201
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f5348,f4525,f5359])).

fof(f5348,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_172 ),
    inference(resolution,[],[f4526,f185])).

fof(f5313,plain,
    ( spl8_198
    | spl8_178
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f5235,f1211,f4580,f5310])).

fof(f5235,plain,
    ( ! [X180,X179] :
        ( ~ sP5(sK1,k4_xboole_0(sK1,X180),sK3)
        | ~ sP5(sK3,k4_xboole_0(sK3,X179),sK1) )
    | ~ spl8_116 ),
    inference(superposition,[],[f3713,f5148])).

fof(f5312,plain,
    ( spl8_198
    | ~ spl8_177
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f5234,f1211,f4576,f5310])).

fof(f5234,plain,
    ( ! [X178] :
        ( ~ sP5(sK1,sK1,sK3)
        | ~ sP5(sK3,k4_xboole_0(sK3,X178),sK1) )
    | ~ spl8_116 ),
    inference(superposition,[],[f2452,f5148])).

fof(f5270,plain,
    ( spl8_196
    | spl8_172
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f5205,f1211,f4525,f5268])).

fof(f5205,plain,
    ( ! [X97,X98] :
        ( ~ sP5(sK1,X98,k1_xboole_0)
        | ~ sP5(k1_xboole_0,k4_xboole_0(sK3,X97),sK1) )
    | ~ spl8_116 ),
    inference(superposition,[],[f921,f5148])).

fof(f5051,plain,
    ( spl8_190
    | spl8_192
    | ~ spl8_195
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f5030,f1040,f5049,f5043,f5037])).

fof(f5037,plain,
    ( spl8_190
  <=> ! [X8] : ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).

fof(f5049,plain,
    ( spl8_195
  <=> ~ r2_hidden(sK1,sK4(sK1,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_195])])).

fof(f5030,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK1,sK4(sK1,sK3,k1_xboole_0))
        | k1_xboole_0 = sK1
        | ~ r2_hidden(sK4(sK1,sK3,k1_xboole_0),X8) )
    | ~ spl8_106 ),
    inference(resolution,[],[f4788,f270])).

fof(f4988,plain,
    ( spl8_186
    | ~ spl8_189
    | ~ spl8_184 ),
    inference(avatar_split_clause,[],[f4975,f4971,f4986,f4980])).

fof(f4980,plain,
    ( spl8_186
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_186])])).

fof(f4986,plain,
    ( spl8_189
  <=> ~ r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_189])])).

fof(f4971,plain,
    ( spl8_184
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_184])])).

fof(f4975,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3
    | ~ spl8_184 ),
    inference(resolution,[],[f4972,f48])).

fof(f4972,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl8_184 ),
    inference(avatar_component_clause,[],[f4971])).

fof(f4973,plain,
    ( spl8_182
    | spl8_184 ),
    inference(avatar_split_clause,[],[f4963,f4971,f4965])).

fof(f4965,plain,
    ( spl8_182
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ r2_hidden(sK1,sK6(X0,sK2,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK2,sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).

fof(f4963,plain,(
    ! [X0] :
      ( r1_tarski(sK2,sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,sK2,sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK1,sK6(X0,sK2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f4957])).

fof(f4957,plain,(
    ! [X0] :
      ( r1_tarski(sK2,sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,sK2,sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK1,sK6(X0,sK2,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,sK3) ) ),
    inference(resolution,[],[f400,f55])).

fof(f400,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK6(X4,X3,sK3),sK2)
      | r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | ~ m1_subset_1(sK6(X4,X3,sK3),sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
      | ~ r2_hidden(sK1,sK6(X4,X3,sK3)) ) ),
    inference(resolution,[],[f277,f57])).

fof(f4892,plain,
    ( ~ spl8_41
    | spl8_34
    | spl8_181 ),
    inference(avatar_split_clause,[],[f4890,f4867,f192,f214])).

fof(f214,plain,
    ( spl8_41
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f4867,plain,
    ( spl8_181
  <=> ~ sP5(sK1,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_181])])).

fof(f4890,plain,
    ( r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK1)
    | ~ spl8_181 ),
    inference(resolution,[],[f4868,f37])).

fof(f4868,plain,
    ( ~ sP5(sK1,sK3,sK1)
    | ~ spl8_181 ),
    inference(avatar_component_clause,[],[f4867])).

fof(f4891,plain,
    ( ~ spl8_41
    | ~ spl8_106
    | spl8_181 ),
    inference(avatar_split_clause,[],[f4886,f4867,f1040,f214])).

fof(f4886,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl8_106
    | ~ spl8_181 ),
    inference(resolution,[],[f4868,f4435])).

fof(f4869,plain,
    ( ~ spl8_181
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f4862,f1040,f4867])).

fof(f4862,plain,
    ( ~ sP5(sK1,sK3,sK1)
    | ~ spl8_106 ),
    inference(duplicate_literal_removal,[],[f4859])).

fof(f4859,plain,
    ( ~ sP5(sK1,sK3,sK1)
    | ~ sP5(sK1,sK3,sK1)
    | ~ spl8_106 ),
    inference(superposition,[],[f4442,f1041])).

fof(f4636,plain,
    ( ~ spl8_23
    | spl8_38
    | spl8_175 ),
    inference(avatar_split_clause,[],[f4635,f4570,f205,f146])).

fof(f146,plain,
    ( spl8_23
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f205,plain,
    ( spl8_38
  <=> r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f4570,plain,
    ( spl8_175
  <=> ~ sP5(sK3,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_175])])).

fof(f4635,plain,
    ( r2_hidden(sK3,sK3)
    | ~ r2_hidden(sK3,sK1)
    | ~ spl8_175 ),
    inference(resolution,[],[f4571,f37])).

fof(f4571,plain,
    ( ~ sP5(sK3,sK3,sK1)
    | ~ spl8_175 ),
    inference(avatar_component_clause,[],[f4570])).

fof(f4582,plain,
    ( ~ spl8_175
    | spl8_178
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f4490,f1211,f1040,f4580,f4570])).

fof(f4490,plain,
    ( ! [X103] :
        ( ~ sP5(sK1,k4_xboole_0(sK1,X103),sK3)
        | ~ sP5(sK3,sK3,sK1) )
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(superposition,[],[f3713,f1041])).

fof(f4578,plain,
    ( ~ spl8_175
    | ~ spl8_177
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f4489,f1211,f1040,f4576,f4570])).

fof(f4489,plain,
    ( ~ sP5(sK1,sK1,sK3)
    | ~ sP5(sK3,sK3,sK1)
    | ~ spl8_106
    | ~ spl8_116 ),
    inference(superposition,[],[f2452,f1041])).

fof(f4527,plain,
    ( ~ spl8_171
    | spl8_172
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f4460,f1040,f4525,f4522])).

fof(f4460,plain,
    ( ! [X51] :
        ( ~ sP5(sK1,X51,k1_xboole_0)
        | ~ sP5(k1_xboole_0,sK3,sK1) )
    | ~ spl8_106 ),
    inference(superposition,[],[f921,f1041])).

fof(f4381,plain,
    ( spl8_168
    | spl8_76 ),
    inference(avatar_split_clause,[],[f4377,f649,f4379])).

fof(f4379,plain,
    ( spl8_168
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X1,sK3),sK1)
        | sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0)
        | ~ m1_subset_1(sK4(k1_xboole_0,X1,sK3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f4377,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK3
      | ~ r2_hidden(sK4(k1_xboole_0,X1,sK3),sK1)
      | ~ m1_subset_1(sK4(k1_xboole_0,X1,sK3),sK0)
      | sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f4376,f50])).

fof(f4376,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_xboole_0,X1) = sK3
      | ~ r2_hidden(sK4(k1_xboole_0,X1,sK3),sK1)
      | ~ m1_subset_1(sK4(k1_xboole_0,X1,sK3),sK0)
      | sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f2094,f50])).

fof(f2094,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X1,sK3),sK1)
      | ~ m1_subset_1(sK4(k1_xboole_0,X1,sK3),sK0)
      | sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0)
      | k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = sK3 ) ),
    inference(forward_demodulation,[],[f2093,f50])).

fof(f2093,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X1,sK3),sK0)
      | sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0)
      | ~ r2_hidden(sK4(k4_xboole_0(k1_xboole_0,X0),X1,sK3),sK1)
      | k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = sK3 ) ),
    inference(forward_demodulation,[],[f2077,f50])).

fof(f2077,plain,(
    ! [X0,X1] :
      ( sP5(sK4(k1_xboole_0,X1,sK3),X0,k1_xboole_0)
      | ~ m1_subset_1(sK4(k4_xboole_0(k1_xboole_0,X0),X1,sK3),sK0)
      | ~ r2_hidden(sK4(k4_xboole_0(k1_xboole_0,X0),X1,sK3),sK1)
      | k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = sK3 ) ),
    inference(superposition,[],[f634,f50])).

fof(f4375,plain,
    ( ~ spl8_3
    | ~ spl8_167
    | spl8_33 ),
    inference(avatar_split_clause,[],[f4374,f181,f4342,f71])).

fof(f4342,plain,
    ( spl8_167
  <=> ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f181,plain,
    ( spl8_33
  <=> ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f4374,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_33 ),
    inference(superposition,[],[f182,f44])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f181])).

fof(f4367,plain,
    ( ~ spl8_3
    | spl8_46
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f4366,f172,f247,f71])).

fof(f172,plain,
    ( spl8_30
  <=> r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f4366,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_30 ),
    inference(superposition,[],[f173,f44])).

fof(f173,plain,
    ( r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f172])).

fof(f4355,plain,
    ( spl8_100
    | ~ spl8_131
    | ~ spl8_102 ),
    inference(avatar_split_clause,[],[f2014,f1026,f1973,f1018])).

fof(f1018,plain,
    ( spl8_100
  <=> k7_subset_1(sK0,sK1,sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f1973,plain,
    ( spl8_131
  <=> ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f1026,plain,
    ( spl8_102
  <=> r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f2014,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | k7_subset_1(sK0,sK1,sK3) = sK1
    | ~ spl8_102 ),
    inference(resolution,[],[f1027,f48])).

fof(f1027,plain,
    ( r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f1026])).

fof(f4352,plain,
    ( spl8_106
    | ~ spl8_133
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f2010,f1033,f1985,f1040])).

fof(f1985,plain,
    ( spl8_133
  <=> ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f1033,plain,
    ( spl8_104
  <=> r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f2010,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | k4_xboole_0(sK1,sK3) = sK1
    | ~ spl8_104 ),
    inference(resolution,[],[f1034,f48])).

fof(f1034,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f4351,plain,
    ( ~ spl8_1
    | ~ spl8_133
    | spl8_131 ),
    inference(avatar_split_clause,[],[f2016,f1973,f1985,f64])).

fof(f2016,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_131 ),
    inference(superposition,[],[f1974,f44])).

fof(f1974,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ spl8_131 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f4350,plain,
    ( ~ spl8_1
    | ~ spl8_107
    | spl8_101 ),
    inference(avatar_split_clause,[],[f1054,f1021,f1043,f64])).

fof(f1043,plain,
    ( spl8_107
  <=> k4_xboole_0(sK1,sK3) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f1021,plain,
    ( spl8_101
  <=> k7_subset_1(sK0,sK1,sK3) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f1054,plain,
    ( k4_xboole_0(sK1,sK3) != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl8_101 ),
    inference(superposition,[],[f1022,f44])).

fof(f1022,plain,
    ( k7_subset_1(sK0,sK1,sK3) != sK1
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f4347,plain,
    ( ~ spl8_167
    | ~ spl8_47
    | spl8_49 ),
    inference(avatar_split_clause,[],[f788,f257,f250,f4342])).

fof(f250,plain,
    ( spl8_47
  <=> ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f257,plain,
    ( spl8_49
  <=> k4_xboole_0(sK2,sK3) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f788,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_49 ),
    inference(extensionality_resolution,[],[f48,f258])).

fof(f258,plain,
    ( k4_xboole_0(sK2,sK3) != sK1
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f257])).

fof(f4346,plain,
    ( ~ spl8_47
    | ~ spl8_167
    | spl8_49 ),
    inference(avatar_split_clause,[],[f787,f257,f4342,f250])).

fof(f787,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_49 ),
    inference(extensionality_resolution,[],[f48,f258])).

fof(f4345,plain,
    ( ~ spl8_167
    | ~ spl8_47
    | spl8_49 ),
    inference(avatar_split_clause,[],[f263,f257,f250,f4342])).

fof(f263,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_49 ),
    inference(extensionality_resolution,[],[f48,f258])).

fof(f4344,plain,
    ( ~ spl8_47
    | ~ spl8_167
    | spl8_49 ),
    inference(avatar_split_clause,[],[f262,f257,f4342,f250])).

fof(f262,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_49 ),
    inference(extensionality_resolution,[],[f48,f258])).

fof(f4337,plain,
    ( spl8_106
    | spl8_113 ),
    inference(avatar_split_clause,[],[f4328,f1110,f1040])).

fof(f4328,plain,
    ( k4_xboole_0(sK1,sK3) = sK1
    | ~ spl8_113 ),
    inference(resolution,[],[f1111,f422])).

fof(f4326,plain,
    ( ~ spl8_113
    | spl8_106
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f4325,f1211,f1040,f1110])).

fof(f4325,plain,
    ( k4_xboole_0(sK1,sK3) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f4321])).

fof(f4321,plain,
    ( k4_xboole_0(sK1,sK3) = sK1
    | k4_xboole_0(sK1,sK3) = sK1
    | ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ spl8_116 ),
    inference(resolution,[],[f4314,f287])).

fof(f4222,plain,
    ( spl8_164
    | spl8_164
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f4214,f1211,f4220,f4220])).

fof(f4214,plain,
    ( ! [X15,X16] :
        ( ~ sP5(sK3,k4_xboole_0(sK1,X16),sK3)
        | ~ sP5(sK3,k4_xboole_0(sK1,X15),sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f3713,f3648])).

fof(f4183,plain,
    ( spl8_162
    | spl8_76
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f4175,f513,f649,f4181])).

fof(f4181,plain,
    ( spl8_162
  <=> ! [X13] :
        ( ~ r2_hidden(sK4(X13,X13,sK3),sK1)
        | ~ m1_subset_1(sK4(X13,X13,sK3),sK0)
        | ~ r2_hidden(sK3,sK4(X13,X13,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f513,plain,
    ( spl8_72
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f4175,plain,
    ( ! [X13] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(X13,X13,sK3),sK1)
        | ~ r2_hidden(sK3,sK4(X13,X13,sK3))
        | ~ m1_subset_1(sK4(X13,X13,sK3),sK0) )
    | ~ spl8_72 ),
    inference(backward_demodulation,[],[f4170,f1190])).

fof(f1190,plain,(
    ! [X13] :
      ( ~ r2_hidden(sK4(X13,X13,sK3),sK1)
      | ~ r2_hidden(sK3,sK4(X13,X13,sK3))
      | ~ m1_subset_1(sK4(X13,X13,sK3),sK0)
      | k4_xboole_0(X13,X13) = sK3 ) ),
    inference(duplicate_literal_removal,[],[f1187])).

fof(f1187,plain,(
    ! [X13] :
      ( k4_xboole_0(X13,X13) = sK3
      | ~ r2_hidden(sK3,sK4(X13,X13,sK3))
      | k4_xboole_0(X13,X13) = sK3
      | ~ m1_subset_1(sK4(X13,X13,sK3),sK0)
      | ~ r2_hidden(sK4(X13,X13,sK3),sK1) ) ),
    inference(resolution,[],[f407,f421])).

fof(f4170,plain,
    ( ! [X1] : k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ spl8_72 ),
    inference(duplicate_literal_removal,[],[f4138])).

fof(f4138,plain,
    ( ! [X1] :
        ( k4_xboole_0(X1,X1) = k1_xboole_0
        | k4_xboole_0(X1,X1) = k1_xboole_0 )
    | ~ spl8_72 ),
    inference(resolution,[],[f2421,f2217])).

fof(f2421,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK4(X4,X5,k1_xboole_0),X4)
        | k4_xboole_0(X4,X5) = k1_xboole_0 )
    | ~ spl8_72 ),
    inference(resolution,[],[f514,f282])).

fof(f514,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f513])).

fof(f3791,plain,
    ( spl8_160
    | spl8_142
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f3731,f1211,f2199,f3789])).

fof(f3731,plain,
    ( ! [X74,X75] :
        ( ~ sP5(sK3,X75,k1_xboole_0)
        | ~ sP5(k1_xboole_0,k4_xboole_0(sK1,X74),sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f921,f3648])).

fof(f3209,plain,
    ( spl8_158
    | spl8_76
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f3205,f1211,f649,f3207])).

fof(f3207,plain,
    ( spl8_158
  <=> ! [X22,X21] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),sK1)
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),X22) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f3205,plain,
    ( ! [X21,X22] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),sK1)
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),X22) )
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f3183,f50])).

fof(f3183,plain,
    ( ! [X21,X22] :
        ( k4_xboole_0(k1_xboole_0,X21) = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),sK1)
        | ~ r2_hidden(sK4(k1_xboole_0,X21,sK3),X22) )
    | ~ spl8_116 ),
    inference(resolution,[],[f2577,f270])).

fof(f3204,plain,
    ( spl8_156
    | spl8_76
    | ~ spl8_72
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f3200,f1211,f513,f649,f3202])).

fof(f3200,plain,
    ( ! [X19] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X19,sK3),sK1) )
    | ~ spl8_72
    | ~ spl8_116 ),
    inference(forward_demodulation,[],[f3181,f50])).

fof(f3181,plain,
    ( ! [X19] :
        ( k4_xboole_0(k1_xboole_0,X19) = sK3
        | ~ r2_hidden(sK4(k1_xboole_0,X19,sK3),sK1) )
    | ~ spl8_72
    | ~ spl8_116 ),
    inference(resolution,[],[f2577,f514])).

fof(f2904,plain,
    ( spl8_154
    | spl8_76
    | ~ spl8_153
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2889,f1211,f2898,f649,f2902])).

fof(f2902,plain,
    ( spl8_154
  <=> ! [X8] : ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f2898,plain,
    ( spl8_153
  <=> ~ r2_hidden(sK3,sK4(sK3,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f2889,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK3,sK4(sK3,sK1,k1_xboole_0))
        | k1_xboole_0 = sK3
        | ~ r2_hidden(sK4(sK3,sK1,k1_xboole_0),X8) )
    | ~ spl8_116 ),
    inference(resolution,[],[f2620,f270])).

fof(f2900,plain,
    ( spl8_76
    | ~ spl8_153
    | ~ spl8_72
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2887,f1211,f513,f2898,f649])).

fof(f2887,plain,
    ( ~ r2_hidden(sK3,sK4(sK3,sK1,k1_xboole_0))
    | k1_xboole_0 = sK3
    | ~ spl8_72
    | ~ spl8_116 ),
    inference(resolution,[],[f2620,f514])).

fof(f2746,plain,
    ( ~ spl8_39
    | spl8_22
    | spl8_151 ),
    inference(avatar_split_clause,[],[f2744,f2727,f143,f208])).

fof(f208,plain,
    ( spl8_39
  <=> ~ r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f2727,plain,
    ( spl8_151
  <=> ~ sP5(sK3,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f2744,plain,
    ( r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK3,sK3)
    | ~ spl8_151 ),
    inference(resolution,[],[f2728,f37])).

fof(f2728,plain,
    ( ~ sP5(sK3,sK1,sK3)
    | ~ spl8_151 ),
    inference(avatar_component_clause,[],[f2727])).

fof(f2745,plain,
    ( ~ spl8_39
    | ~ spl8_116
    | spl8_151 ),
    inference(avatar_split_clause,[],[f2740,f2727,f1211,f208])).

fof(f2740,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ spl8_116
    | ~ spl8_151 ),
    inference(resolution,[],[f2728,f2445])).

fof(f2729,plain,
    ( ~ spl8_151
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2722,f1211,f2727])).

fof(f2722,plain,
    ( ~ sP5(sK3,sK1,sK3)
    | ~ spl8_116 ),
    inference(duplicate_literal_removal,[],[f2721])).

fof(f2721,plain,
    ( ~ sP5(sK3,sK1,sK3)
    | ~ sP5(sK3,sK1,sK3)
    | ~ spl8_116 ),
    inference(superposition,[],[f2452,f1212])).

fof(f2415,plain,
    ( ~ spl8_7
    | spl8_149 ),
    inference(avatar_split_clause,[],[f2411,f2390,f85])).

fof(f2390,plain,
    ( spl8_149
  <=> ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f2411,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_149 ),
    inference(resolution,[],[f2391,f245])).

fof(f2391,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(sK0))
    | ~ spl8_149 ),
    inference(avatar_component_clause,[],[f2390])).

fof(f2392,plain,
    ( spl8_134
    | ~ spl8_7
    | ~ spl8_149
    | ~ spl8_136 ),
    inference(avatar_split_clause,[],[f2385,f2052,f2390,f85,f2049])).

fof(f2049,plain,
    ( spl8_134
  <=> r1_tarski(sK3,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f2052,plain,
    ( spl8_136
  <=> ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK3,k4_xboole_0(sK3,sK1)),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f2385,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl8_136 ),
    inference(duplicate_literal_removal,[],[f2381])).

fof(f2381,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl8_136 ),
    inference(resolution,[],[f2053,f54])).

fof(f2053,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK3,k4_xboole_0(sK3,sK1)),sK0)
        | ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) )
    | ~ spl8_136 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f2319,plain,
    ( spl8_76
    | spl8_146
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2310,f1211,f2317,f649])).

fof(f2317,plain,
    ( spl8_146
  <=> ! [X19] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X19,sK3),sK1)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f2310,plain,
    ( ! [X19] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X19,sK3),sK1)
        | ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0,X19,sK3))
        | k1_xboole_0 = sK3 )
    | ~ spl8_116 ),
    inference(resolution,[],[f2266,f428])).

fof(f2266,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl8_116 ),
    inference(resolution,[],[f2134,f39])).

fof(f2134,plain,
    ( ! [X3] :
        ( sP5(X3,sK1,sK3)
        | ~ r2_hidden(X3,sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f59,f1212])).

fof(f2315,plain,
    ( ~ spl8_121
    | ~ spl8_114
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2309,f1211,f1202,f1256])).

fof(f2309,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,sK3),sK1)
    | ~ spl8_114
    | ~ spl8_116 ),
    inference(resolution,[],[f2266,f1203])).

fof(f2232,plain,
    ( ~ spl8_145
    | spl8_52
    | spl8_141 ),
    inference(avatar_split_clause,[],[f2224,f2196,f303,f2230])).

fof(f2230,plain,
    ( spl8_145
  <=> ~ r2_hidden(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f2196,plain,
    ( spl8_141
  <=> ~ sP5(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f2224,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ r2_hidden(k1_xboole_0,sK3)
    | ~ spl8_141 ),
    inference(resolution,[],[f2197,f37])).

fof(f2197,plain,
    ( ~ sP5(k1_xboole_0,sK1,sK3)
    | ~ spl8_141 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2201,plain,
    ( ~ spl8_141
    | spl8_142
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f2154,f1211,f2199,f2196])).

fof(f2154,plain,
    ( ! [X35] :
        ( ~ sP5(sK3,X35,k1_xboole_0)
        | ~ sP5(k1_xboole_0,sK1,sK3) )
    | ~ spl8_116 ),
    inference(superposition,[],[f921,f1212])).

fof(f2122,plain,
    ( ~ spl8_6
    | spl8_139 ),
    inference(avatar_contradiction_clause,[],[f2121])).

fof(f2121,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_139 ),
    inference(resolution,[],[f2099,f89])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2099,plain,
    ( ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | ~ spl8_139 ),
    inference(resolution,[],[f2066,f1946])).

fof(f2066,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,sK1),sK3)
    | ~ spl8_139 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f2065,plain,
    ( spl8_139
  <=> ~ r1_tarski(k4_xboole_0(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f2067,plain,
    ( spl8_116
    | ~ spl8_139
    | ~ spl8_134 ),
    inference(avatar_split_clause,[],[f2057,f2049,f2065,f1211])).

fof(f2057,plain,
    ( ~ r1_tarski(k4_xboole_0(sK3,sK1),sK3)
    | k4_xboole_0(sK3,sK1) = sK3
    | ~ spl8_134 ),
    inference(resolution,[],[f2050,f48])).

fof(f2050,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl8_134 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f2054,plain,
    ( spl8_134
    | spl8_136 ),
    inference(avatar_split_clause,[],[f2044,f2052,f2049])).

fof(f2044,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | r1_tarski(sK3,k4_xboole_0(sK3,sK1))
      | ~ m1_subset_1(sK6(X0,sK3,k4_xboole_0(sK3,sK1)),sK0) ) ),
    inference(duplicate_literal_removal,[],[f2034])).

fof(f2034,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | r1_tarski(sK3,k4_xboole_0(sK3,sK1))
      | ~ m1_subset_1(sK6(X0,sK3,k4_xboole_0(sK3,sK1)),sK0)
      | ~ m1_subset_1(k4_xboole_0(sK3,sK1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | r1_tarski(sK3,k4_xboole_0(sK3,sK1)) ) ),
    inference(resolution,[],[f1679,f55])).

fof(f2006,plain,
    ( spl8_102
    | ~ spl8_30
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f2005,f382,f172,f1026])).

fof(f382,plain,
    ( spl8_66
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f2005,plain,
    ( r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ spl8_30
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f173,f383])).

fof(f383,plain,
    ( sK1 = sK2
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f382])).

fof(f2004,plain,
    ( ~ spl8_131
    | spl8_33
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f2003,f382,f181,f1973])).

fof(f2003,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ spl8_33
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f182,f383])).

fof(f2002,plain,
    ( spl8_104
    | ~ spl8_46
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f2001,f382,f247,f1033])).

fof(f2001,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_46
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f248,f383])).

fof(f248,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f247])).

fof(f2000,plain,
    ( ~ spl8_105
    | ~ spl8_133
    | spl8_107 ),
    inference(avatar_split_clause,[],[f1058,f1043,f1985,f1036])).

fof(f1036,plain,
    ( spl8_105
  <=> ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f1058,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_107 ),
    inference(extensionality_resolution,[],[f48,f1044])).

fof(f1044,plain,
    ( k4_xboole_0(sK1,sK3) != sK1
    | ~ spl8_107 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1999,plain,
    ( ~ spl8_133
    | ~ spl8_105
    | spl8_107 ),
    inference(avatar_split_clause,[],[f1059,f1043,f1036,f1985])).

fof(f1059,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl8_107 ),
    inference(extensionality_resolution,[],[f48,f1044])).

fof(f1998,plain,
    ( ~ spl8_103
    | ~ spl8_131
    | spl8_101 ),
    inference(avatar_split_clause,[],[f1052,f1021,f1973,f1029])).

fof(f1029,plain,
    ( spl8_103
  <=> ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f1052,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ spl8_101 ),
    inference(extensionality_resolution,[],[f48,f1022])).

fof(f1997,plain,
    ( ~ spl8_131
    | ~ spl8_103
    | spl8_101 ),
    inference(avatar_split_clause,[],[f1053,f1021,f1029,f1973])).

fof(f1053,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ spl8_101 ),
    inference(extensionality_resolution,[],[f48,f1022])).

fof(f1996,plain,
    ( ~ spl8_133
    | ~ spl8_105
    | spl8_49
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1995,f382,f257,f1036,f1985])).

fof(f1995,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1994,f383])).

fof(f1994,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f262,f383])).

fof(f1993,plain,
    ( ~ spl8_105
    | ~ spl8_133
    | spl8_49
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1992,f382,f257,f1985,f1036])).

fof(f1992,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1991,f383])).

fof(f1991,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f263,f383])).

fof(f1990,plain,
    ( ~ spl8_133
    | ~ spl8_105
    | spl8_49
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1989,f382,f257,f1036,f1985])).

fof(f1989,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1988,f383])).

fof(f1988,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f787,f383])).

fof(f1987,plain,
    ( ~ spl8_105
    | ~ spl8_133
    | spl8_49
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1980,f382,f257,f1985,f1036])).

fof(f1980,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK3))
    | ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1979,f383])).

fof(f1979,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f788,f383])).

fof(f1978,plain,
    ( ~ spl8_131
    | ~ spl8_103
    | spl8_5
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1977,f382,f81,f1029,f1973])).

fof(f81,plain,
    ( spl8_5
  <=> k7_subset_1(sK0,sK2,sK3) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1977,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ spl8_5
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1976,f383])).

fof(f1976,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_5
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f764,f383])).

fof(f764,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_5 ),
    inference(extensionality_resolution,[],[f48,f82])).

fof(f82,plain,
    ( k7_subset_1(sK0,sK2,sK3) != sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1975,plain,
    ( ~ spl8_103
    | ~ spl8_131
    | spl8_5
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1968,f382,f81,f1973,f1029])).

fof(f1968,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK1,sK3))
    | ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ spl8_5
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1967,f383])).

fof(f1967,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ spl8_5
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f765,f383])).

fof(f765,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ spl8_5 ),
    inference(extensionality_resolution,[],[f48,f82])).

fof(f1966,plain,
    ( ~ spl8_0
    | spl8_105 ),
    inference(avatar_contradiction_clause,[],[f1965])).

fof(f1965,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_105 ),
    inference(resolution,[],[f1947,f68])).

fof(f1947,plain,
    ( ! [X0] : ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | ~ spl8_105 ),
    inference(resolution,[],[f1946,f1037])).

fof(f1037,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f1607,plain,
    ( ~ spl8_127
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1594,f1571,f1600])).

fof(f1600,plain,
    ( spl8_127
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f1571,plain,
    ( spl8_124
  <=> ! [X0] : ~ sP5(k1_xboole_0,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f1594,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl8_124 ),
    inference(resolution,[],[f1572,f186])).

fof(f1572,plain,
    ( ! [X0] : ~ sP5(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1606,plain,
    ( ~ spl8_127
    | spl8_128
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1593,f1571,f1604,f1600])).

fof(f1604,plain,
    ( spl8_128
  <=> ! [X1] : r2_hidden(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f1593,plain,
    ( ! [X1] :
        ( r2_hidden(k1_xboole_0,X1)
        | ~ r2_hidden(k1_xboole_0,k1_xboole_0) )
    | ~ spl8_124 ),
    inference(resolution,[],[f1572,f37])).

fof(f1602,plain,
    ( ~ spl8_127
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1590,f1571,f1600])).

fof(f1590,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl8_124 ),
    inference(resolution,[],[f1572,f185])).

fof(f1573,plain,
    ( spl8_124
    | spl8_124 ),
    inference(avatar_split_clause,[],[f1563,f1571,f1571])).

fof(f1563,plain,(
    ! [X0,X1] :
      ( ~ sP5(k1_xboole_0,X1,k1_xboole_0)
      | ~ sP5(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(superposition,[],[f921,f50])).

fof(f1282,plain,
    ( ~ spl8_123
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f1274,f1202,f1280])).

fof(f1280,plain,
    ( spl8_123
  <=> ~ r2_hidden(sK3,sK4(sK3,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f1274,plain,
    ( ~ r2_hidden(sK3,sK4(sK3,sK1,sK3))
    | ~ spl8_114 ),
    inference(resolution,[],[f1203,f57])).

fof(f1258,plain,
    ( ~ spl8_121
    | spl8_116
    | spl8_115 ),
    inference(avatar_split_clause,[],[f1247,f1205,f1211,f1256])).

fof(f1205,plain,
    ( spl8_115
  <=> ~ r2_hidden(sK4(sK3,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1247,plain,
    ( k4_xboole_0(sK3,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,sK3),sK1)
    | ~ spl8_115 ),
    inference(resolution,[],[f1206,f281])).

fof(f1206,plain,
    ( ~ r2_hidden(sK4(sK3,sK1,sK3),sK3)
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1251,plain,
    ( spl8_116
    | spl8_115 ),
    inference(avatar_split_clause,[],[f1244,f1205,f1211])).

fof(f1244,plain,
    ( k4_xboole_0(sK3,sK1) = sK3
    | ~ spl8_115 ),
    inference(resolution,[],[f1206,f422])).

fof(f1219,plain,
    ( ~ spl8_115
    | spl8_116
    | ~ spl8_119 ),
    inference(avatar_split_clause,[],[f1200,f1217,f1211,f1205])).

fof(f1217,plain,
    ( spl8_119
  <=> ~ m1_subset_1(sK4(sK3,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f1200,plain,
    ( ~ m1_subset_1(sK4(sK3,sK1,sK3),sK0)
    | k4_xboole_0(sK3,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,sK3),sK3) ),
    inference(duplicate_literal_removal,[],[f1198])).

fof(f1198,plain,
    ( ~ m1_subset_1(sK4(sK3,sK1,sK3),sK0)
    | k4_xboole_0(sK3,sK1) = sK3
    | k4_xboole_0(sK3,sK1) = sK3
    | ~ r2_hidden(sK4(sK3,sK1,sK3),sK3)
    | ~ r2_hidden(sK4(sK3,sK1,sK3),sK3) ),
    inference(resolution,[],[f618,f287])).

fof(f618,plain,(
    ! [X13] :
      ( ~ r2_hidden(sK4(sK3,X13,sK3),sK1)
      | ~ m1_subset_1(sK4(sK3,X13,sK3),sK0)
      | k4_xboole_0(sK3,X13) = sK3 ) ),
    inference(resolution,[],[f422,f31])).

fof(f1112,plain,
    ( spl8_106
    | ~ spl8_111
    | ~ spl8_113 ),
    inference(avatar_split_clause,[],[f1096,f1110,f1104,f1040])).

fof(f1104,plain,
    ( spl8_111
  <=> ~ m1_subset_1(sK4(sK1,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f1096,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ m1_subset_1(sK4(sK1,sK3,sK1),sK0)
    | k4_xboole_0(sK1,sK3) = sK1 ),
    inference(duplicate_literal_removal,[],[f1092])).

fof(f1092,plain,
    ( ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ r2_hidden(sK4(sK1,sK3,sK1),sK1)
    | ~ m1_subset_1(sK4(sK1,sK3,sK1),sK0)
    | k4_xboole_0(sK1,sK3) = sK1
    | k4_xboole_0(sK1,sK3) = sK1 ),
    inference(resolution,[],[f434,f422])).

fof(f434,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(sK4(X15,sK3,X16),sK1)
      | ~ r2_hidden(sK4(X15,sK3,X16),X16)
      | ~ r2_hidden(sK4(X15,sK3,X16),X15)
      | ~ m1_subset_1(sK4(X15,sK3,X16),sK0)
      | k4_xboole_0(X15,sK3) = X16 ) ),
    inference(resolution,[],[f287,f31])).

fof(f1088,plain,
    ( spl8_92
    | spl8_108 ),
    inference(avatar_split_clause,[],[f1087,f1084,f760])).

fof(f760,plain,
    ( spl8_92
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1084,plain,
    ( spl8_108
  <=> ! [X5,X7] : ~ sP5(X7,X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f1087,plain,(
    ! [X14,X12,X13] :
      ( ~ sP5(X14,X12,X12)
      | ~ v1_xboole_0(X13) ) ),
    inference(global_subsumption,[],[f1082])).

fof(f1082,plain,(
    ! [X6,X7,X5] :
      ( ~ sP5(X7,X5,X5)
      | ~ v1_xboole_0(X6) ) ),
    inference(global_subsumption,[],[f53,f1072])).

fof(f1072,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(X7,X6)
      | ~ sP5(X7,X5,X5)
      | ~ v1_xboole_0(X6) ) ),
    inference(superposition,[],[f60,f962])).

fof(f962,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f952])).

fof(f952,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | ~ v1_xboole_0(X3)
      | k4_xboole_0(X2,X2) = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f417,f408])).

fof(f408,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X3,X4,X5),X4)
      | k4_xboole_0(X3,X4) = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f281,f53])).

fof(f417,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X3)
      | k4_xboole_0(X3,X4) = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f282,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t7_boole)).

fof(f1086,plain,
    ( spl8_92
    | spl8_108 ),
    inference(avatar_split_clause,[],[f1082,f1084,f760])).

fof(f1045,plain,
    ( ~ spl8_107
    | spl8_49
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f992,f382,f257,f1043])).

fof(f992,plain,
    ( k4_xboole_0(sK1,sK3) != sK1
    | ~ spl8_49
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f383,f258])).

fof(f1038,plain,
    ( ~ spl8_105
    | spl8_47
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f991,f382,f250,f1036])).

fof(f991,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl8_47
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f383,f251])).

fof(f251,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f250])).

fof(f1031,plain,
    ( ~ spl8_103
    | spl8_31
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f988,f382,f175,f1029])).

fof(f175,plain,
    ( spl8_31
  <=> ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f988,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK1,sK3),sK1)
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f383,f176])).

fof(f176,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1024,plain,
    ( ~ spl8_45
    | spl8_19
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f986,f382,f133,f226])).

fof(f226,plain,
    ( spl8_45
  <=> ~ m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f133,plain,
    ( spl8_19
  <=> ~ m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f986,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl8_19
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f383,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1023,plain,
    ( ~ spl8_101
    | spl8_5
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f982,f382,f81,f1021])).

fof(f982,plain,
    ( k7_subset_1(sK0,sK1,sK3) != sK1
    | ~ spl8_5
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f383,f82])).

fof(f978,plain,
    ( spl8_62
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f977,f374,f71,f64,f371])).

fof(f371,plain,
    ( spl8_62
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f374,plain,
    ( spl8_64
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK6(X0,sK1,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f977,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl8_64 ),
    inference(duplicate_literal_removal,[],[f976])).

fof(f976,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl8_64 ),
    inference(resolution,[],[f375,f54])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(X0,sK1,sK2),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f374])).

fof(f975,plain,
    ( spl8_68
    | spl8_98 ),
    inference(avatar_split_clause,[],[f971,f973,f385])).

fof(f385,plain,
    ( spl8_68
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f973,plain,
    ( spl8_98
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ r2_hidden(sK3,sK6(X0,sK2,sK1))
        | ~ m1_subset_1(sK6(X0,sK2,sK1),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f971,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,sK2,sK1),sK0)
      | ~ r2_hidden(sK3,sK6(X0,sK2,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f967])).

fof(f967,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK6(X0,sK2,sK1),sK0)
      | ~ r2_hidden(sK3,sK6(X0,sK2,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,sK1) ) ),
    inference(resolution,[],[f275,f55])).

fof(f275,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK6(X6,X7,sK1),sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | r1_tarski(X7,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X6))
      | ~ m1_subset_1(sK6(X6,X7,sK1),sK0)
      | ~ r2_hidden(sK3,sK6(X6,X7,sK1)) ) ),
    inference(resolution,[],[f56,f119])).

fof(f782,plain,
    ( ~ spl8_97
    | ~ spl8_95
    | spl8_77 ),
    inference(avatar_split_clause,[],[f768,f646,f773,f779])).

fof(f773,plain,
    ( spl8_95
  <=> ~ r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f646,plain,
    ( spl8_77
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f768,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_77 ),
    inference(extensionality_resolution,[],[f48,f647])).

fof(f647,plain,
    ( k1_xboole_0 != sK3
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f646])).

fof(f781,plain,
    ( ~ spl8_95
    | ~ spl8_97
    | spl8_77 ),
    inference(avatar_split_clause,[],[f767,f646,f779,f773])).

fof(f767,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl8_77 ),
    inference(extensionality_resolution,[],[f48,f647])).

fof(f762,plain,
    ( spl8_72
    | spl8_92 ),
    inference(avatar_split_clause,[],[f546,f760,f513])).

fof(f546,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f531])).

fof(f531,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X3,k1_xboole_0)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f503,f53])).

fof(f503,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,X9)
      | ~ v1_xboole_0(X9)
      | ~ r2_hidden(X8,k1_xboole_0) ) ),
    inference(resolution,[],[f272,f38])).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X2,X0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f185,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t6_boole)).

fof(f758,plain,
    ( spl8_90
    | spl8_90 ),
    inference(avatar_split_clause,[],[f555,f756,f756])).

fof(f756,plain,
    ( spl8_90
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f555,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f508,f503])).

fof(f508,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X20,X19)
      | ~ v1_xboole_0(X20)
      | ~ r2_hidden(X19,k1_xboole_0) ) ),
    inference(resolution,[],[f272,f342])).

fof(f725,plain,
    ( ~ spl8_89
    | spl8_49
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f668,f649,f257,f723])).

fof(f723,plain,
    ( spl8_89
  <=> k4_xboole_0(sK2,k1_xboole_0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f668,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != sK1
    | ~ spl8_49
    | ~ spl8_76 ),
    inference(backward_demodulation,[],[f650,f258])).

fof(f650,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f649])).

fof(f717,plain,
    ( ~ spl8_87
    | spl8_31
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f665,f649,f175,f715])).

fof(f715,plain,
    ( spl8_87
  <=> ~ r1_tarski(k7_subset_1(sK0,sK2,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f665,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK2,k1_xboole_0),sK1)
    | ~ spl8_31
    | ~ spl8_76 ),
    inference(backward_demodulation,[],[f650,f176])).

fof(f710,plain,
    ( ~ spl8_85
    | spl8_13
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f661,f649,f112,f708])).

fof(f708,plain,
    ( spl8_85
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f112,plain,
    ( spl8_13
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f661,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_13
    | ~ spl8_76 ),
    inference(backward_demodulation,[],[f650,f113])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f703,plain,
    ( spl8_82
    | ~ spl8_6
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f660,f649,f88,f701])).

fof(f660,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_6
    | ~ spl8_76 ),
    inference(backward_demodulation,[],[f650,f89])).

fof(f696,plain,
    ( ~ spl8_81
    | spl8_5
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f659,f649,f81,f694])).

fof(f694,plain,
    ( spl8_81
  <=> k7_subset_1(sK0,sK2,k1_xboole_0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f659,plain,
    ( k7_subset_1(sK0,sK2,k1_xboole_0) != sK1
    | ~ spl8_5
    | ~ spl8_76 ),
    inference(backward_demodulation,[],[f650,f82])).

fof(f656,plain,
    ( spl8_78
    | spl8_76 ),
    inference(avatar_split_clause,[],[f652,f649,f654])).

fof(f654,plain,
    ( spl8_78
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(sK4(k1_xboole_0,X11,sK3),sK0)
        | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),X12)
        | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f652,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 = sK3
      | ~ m1_subset_1(sK4(k1_xboole_0,X11,sK3),sK0)
      | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),sK1)
      | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),X12) ) ),
    inference(forward_demodulation,[],[f636,f50])).

fof(f636,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(k1_xboole_0,X11) = sK3
      | ~ m1_subset_1(sK4(k1_xboole_0,X11,sK3),sK0)
      | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),sK1)
      | ~ r2_hidden(sK4(k1_xboole_0,X11,sK3),X12) ) ),
    inference(resolution,[],[f421,f270])).

fof(f651,plain,
    ( spl8_74
    | spl8_76
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f641,f513,f649,f643])).

fof(f643,plain,
    ( spl8_74
  <=> ! [X10] :
        ( ~ m1_subset_1(sK4(k1_xboole_0,X10,sK3),sK0)
        | ~ r2_hidden(sK4(k1_xboole_0,X10,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f641,plain,
    ( ! [X10] :
        ( k1_xboole_0 = sK3
        | ~ m1_subset_1(sK4(k1_xboole_0,X10,sK3),sK0)
        | ~ r2_hidden(sK4(k1_xboole_0,X10,sK3),sK1) )
    | ~ spl8_72 ),
    inference(forward_demodulation,[],[f635,f50])).

fof(f635,plain,
    ( ! [X10] :
        ( k4_xboole_0(k1_xboole_0,X10) = sK3
        | ~ m1_subset_1(sK4(k1_xboole_0,X10,sK3),sK0)
        | ~ r2_hidden(sK4(k1_xboole_0,X10,sK3),sK1) )
    | ~ spl8_72 ),
    inference(resolution,[],[f421,f514])).

fof(f515,plain,
    ( spl8_70
    | spl8_72 ),
    inference(avatar_split_clause,[],[f501,f513,f510])).

fof(f510,plain,
    ( spl8_70
  <=> ! [X3,X4] :
        ( ~ v1_xboole_0(X3)
        | ~ v1_xboole_0(k4_xboole_0(X3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f501,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ v1_xboole_0(X3)
      | ~ v1_xboole_0(k4_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f272,f231])).

fof(f231,plain,(
    ! [X6,X8,X7] :
      ( ~ sP5(X6,X7,X8)
      | ~ v1_xboole_0(k4_xboole_0(X8,X7)) ) ),
    inference(resolution,[],[f60,f53])).

fof(f390,plain,
    ( spl8_66
    | ~ spl8_69
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f377,f371,f388,f382])).

fof(f388,plain,
    ( spl8_69
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f377,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | ~ spl8_62 ),
    inference(resolution,[],[f372,f48])).

fof(f372,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f371])).

fof(f376,plain,
    ( spl8_62
    | spl8_64 ),
    inference(avatar_split_clause,[],[f366,f374,f371])).

fof(f366,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r1_tarski(sK1,sK2)
      | ~ m1_subset_1(sK6(X0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r1_tarski(sK1,sK2)
      | ~ m1_subset_1(sK6(X0,sK1,sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f276,f55])).

fof(f362,plain,
    ( ~ spl8_61
    | spl8_55 ),
    inference(avatar_split_clause,[],[f354,f312,f360])).

fof(f360,plain,
    ( spl8_61
  <=> ~ v1_xboole_0(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f312,plain,
    ( spl8_55
  <=> ~ m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f354,plain,
    ( ~ v1_xboole_0(sK7(sK0))
    | ~ spl8_55 ),
    inference(resolution,[],[f345,f58])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_55 ),
    inference(superposition,[],[f313,f49])).

fof(f313,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f312])).

fof(f336,plain,
    ( ~ spl8_57
    | ~ spl8_55
    | ~ spl8_59
    | spl8_53 ),
    inference(avatar_split_clause,[],[f322,f306,f334,f312,f328])).

fof(f334,plain,
    ( spl8_59
  <=> ~ r2_hidden(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f322,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_53 ),
    inference(resolution,[],[f307,f119])).

fof(f307,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f306])).

fof(f314,plain,
    ( spl8_50
    | ~ spl8_53
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f298,f312,f306,f300])).

fof(f298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,sK0)
      | ~ r2_hidden(k1_xboole_0,sK1)
      | ~ sP5(sK2,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f293,f50])).

fof(f293,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,sK1)
      | ~ m1_subset_1(k4_xboole_0(k1_xboole_0,X0),sK0)
      | ~ sP5(sK2,X0,k1_xboole_0) ) ),
    inference(superposition,[],[f232,f50])).

fof(f259,plain,
    ( ~ spl8_3
    | ~ spl8_49
    | spl8_5 ),
    inference(avatar_split_clause,[],[f243,f81,f257,f71])).

fof(f243,plain,
    ( k4_xboole_0(sK2,sK3) != sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_5 ),
    inference(superposition,[],[f82,f44])).

fof(f252,plain,
    ( ~ spl8_3
    | ~ spl8_47
    | spl8_31 ),
    inference(avatar_split_clause,[],[f242,f175,f250,f71])).

fof(f242,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_31 ),
    inference(superposition,[],[f176,f44])).

fof(f228,plain,
    ( ~ spl8_39
    | ~ spl8_25
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f189,f226,f220,f214,f201,f152,f208])).

fof(f152,plain,
    ( spl8_25
  <=> ~ m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f201,plain,
    ( spl8_37
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f220,plain,
    ( spl8_43
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK1)
    | ~ r2_hidden(sK3,sK2)
    | ~ m1_subset_1(sK3,sK0)
    | ~ r2_hidden(sK3,sK3) ),
    inference(resolution,[],[f155,f119])).

fof(f203,plain,
    ( spl8_22
    | ~ spl8_35
    | ~ spl8_37
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f190,f152,f201,f195,f143])).

fof(f190,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK3,sK1) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK3,sK2)
    | ~ m1_subset_1(sK3,sK0)
    | r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f155,f32])).

fof(f184,plain,
    ( ~ spl8_33
    | ~ spl8_31
    | spl8_5 ),
    inference(avatar_split_clause,[],[f169,f81,f175,f181])).

fof(f169,plain,
    ( ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ spl8_5 ),
    inference(extensionality_resolution,[],[f48,f82])).

fof(f183,plain,
    ( ~ spl8_31
    | ~ spl8_33
    | spl8_5 ),
    inference(avatar_split_clause,[],[f168,f81,f181,f175])).

fof(f168,plain,
    ( ~ r1_tarski(sK1,k7_subset_1(sK0,sK2,sK3))
    | ~ r1_tarski(k7_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_5 ),
    inference(extensionality_resolution,[],[f48,f82])).

fof(f167,plain,
    ( ~ spl8_27
    | spl8_28 ),
    inference(avatar_split_clause,[],[f156,f165,f162])).

fof(f162,plain,
    ( spl8_27
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f165,plain,
    ( spl8_28
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(sK3,X1)
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f156,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(sK3,X1)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f119,f53])).

fof(f154,plain,
    ( spl8_16
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f121,f152,f146,f140,f133,f124])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK2,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f118,f32])).

fof(f135,plain,
    ( ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f122,f133,f127])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ r2_hidden(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f118,f30])).

fof(f117,plain,
    ( ~ spl8_13
    | spl8_14 ),
    inference(avatar_split_clause,[],[f106,f115,f112])).

fof(f115,plain,
    ( spl8_14
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,sK0)
      | r2_hidden(X1,sK1)
      | ~ v1_xboole_0(sK3) ) ),
    inference(resolution,[],[f32,f53])).

fof(f104,plain,
    ( spl8_8
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f94,f102,f96])).

fof(f96,plain,
    ( spl8_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f102,plain,
    ( spl8_11
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f53,f30])).

fof(f90,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    k7_subset_1(sK0,sK2,sK3) != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f69,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f36,f67])).
%------------------------------------------------------------------------------
