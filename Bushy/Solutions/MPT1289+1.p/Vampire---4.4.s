%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t111_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:26 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  726 (2391 expanded)
%              Number of leaves         :  199 (1024 expanded)
%              Depth                    :   11
%              Number of atoms          : 1763 (5625 expanded)
%              Number of equality atoms :   51 ( 122 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f134,f141,f148,f155,f167,f179,f197,f218,f233,f240,f251,f260,f278,f290,f301,f326,f334,f343,f384,f391,f405,f416,f426,f440,f453,f460,f485,f492,f510,f524,f557,f574,f607,f627,f634,f642,f655,f662,f674,f691,f727,f734,f741,f748,f755,f770,f875,f882,f902,f921,f928,f968,f975,f982,f989,f996,f1003,f1051,f1073,f1080,f1087,f1108,f1119,f1126,f1133,f1156,f1183,f1310,f1317,f1324,f1331,f1338,f1345,f1366,f1379,f1386,f1393,f1416,f1429,f1436,f1443,f1450,f1457,f1464,f1488,f1495,f1511,f1524,f1586,f1633,f1798,f1805,f1812,f1819,f1834,f1890,f1897,f1904,f1965,f1984,f2009,f2070,f2083,f2090,f2097,f2104,f2111,f2118,f2125,f2132,f2139,f2152,f2159,f2176,f2230,f2243,f2295,f2356,f2407,f2414,f2421,f2428,f2435,f2442,f2449,f2456,f2463,f2470,f2477,f2503,f2536,f2642,f2841,f2848,f2855,f2862,f2869,f2876,f2883,f2890,f2953,f2960,f2967,f3029,f3036,f3043,f3050,f3057,f3075,f3082,f3089,f3096,f3103,f3222,f3246,f3253,f3282,f3303,f3310,f3324,f3331,f3338,f3413,f3420,f3427,f3443,f3450,f3469,f3492,f3509,f3523,f3542])).

fof(f3542,plain,
    ( ~ spl4_0
    | ~ spl4_66
    | ~ spl4_106
    | ~ spl4_116
    | ~ spl4_190
    | spl4_337 ),
    inference(avatar_contradiction_clause,[],[f3541])).

fof(f3541,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_66
    | ~ spl4_106
    | ~ spl4_116
    | ~ spl4_190
    | ~ spl4_337 ),
    inference(subsumption_resolution,[],[f3528,f1053])).

fof(f1053,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_66
    | ~ spl4_106
    | ~ spl4_116 ),
    inference(unit_resulting_resolution,[],[f126,f573,f967,f1002,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t49_pre_topc)).

fof(f1002,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1001,plain,
    ( spl4_116
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f967,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f966])).

fof(f966,plain,
    ( spl4_106
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f573,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl4_66
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f3528,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_190
    | ~ spl4_337 ),
    inference(unit_resulting_resolution,[],[f1818,f3449,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t1_xboole_1)).

fof(f3449,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_337 ),
    inference(avatar_component_clause,[],[f3448])).

fof(f3448,plain,
    ( spl4_337
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_337])])).

fof(f1818,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_190 ),
    inference(avatar_component_clause,[],[f1817])).

fof(f1817,plain,
    ( spl4_190
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f3523,plain,
    ( spl4_342
    | ~ spl4_338 ),
    inference(avatar_split_clause,[],[f3502,f3490,f3521])).

fof(f3521,plain,
    ( spl4_342
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_342])])).

fof(f3490,plain,
    ( spl4_338
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_338])])).

fof(f3502,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_338 ),
    inference(unit_resulting_resolution,[],[f3491,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t3_subset)).

fof(f3491,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_338 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f3509,plain,
    ( spl4_340
    | ~ spl4_52
    | ~ spl4_334 ),
    inference(avatar_split_clause,[],[f3473,f3438,f451,f3507])).

fof(f3507,plain,
    ( spl4_340
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_340])])).

fof(f451,plain,
    ( spl4_52
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f3438,plain,
    ( spl4_334
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_334])])).

fof(f3473,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_52
    | ~ spl4_334 ),
    inference(unit_resulting_resolution,[],[f452,f3439,f118])).

fof(f3439,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_334 ),
    inference(avatar_component_clause,[],[f3438])).

fof(f452,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f451])).

fof(f3492,plain,
    ( spl4_338
    | ~ spl4_50
    | ~ spl4_334 ),
    inference(avatar_split_clause,[],[f3478,f3438,f438,f3490])).

fof(f438,plain,
    ( spl4_50
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f3478,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_50
    | ~ spl4_334 ),
    inference(unit_resulting_resolution,[],[f439,f3439,f118])).

fof(f439,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f438])).

fof(f3469,plain,
    ( ~ spl4_0
    | ~ spl4_60
    | ~ spl4_132
    | ~ spl4_148
    | ~ spl4_164
    | spl4_335 ),
    inference(avatar_contradiction_clause,[],[f3468])).

fof(f3468,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_60
    | ~ spl4_132
    | ~ spl4_148
    | ~ spl4_164
    | ~ spl4_335 ),
    inference(subsumption_resolution,[],[f3453,f1735])).

fof(f1735,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_60
    | ~ spl4_148
    | ~ spl4_164 ),
    inference(unit_resulting_resolution,[],[f126,f509,f1344,f1442,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t48_tops_1)).

fof(f1442,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1441,plain,
    ( spl4_164
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f1344,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_148 ),
    inference(avatar_component_clause,[],[f1343])).

fof(f1343,plain,
    ( spl4_148
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f509,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl4_60
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f3453,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_132
    | ~ spl4_335 ),
    inference(unit_resulting_resolution,[],[f1132,f3442,f118])).

fof(f3442,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_335 ),
    inference(avatar_component_clause,[],[f3441])).

fof(f3441,plain,
    ( spl4_335
  <=> ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_335])])).

fof(f1132,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f1131,plain,
    ( spl4_132
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f3450,plain,
    ( ~ spl4_337
    | ~ spl4_0
    | spl4_21
    | ~ spl4_60
    | ~ spl4_102
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f3436,f973,f919,f508,f231,f125,f3448])).

fof(f231,plain,
    ( spl4_21
  <=> ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f919,plain,
    ( spl4_102
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f973,plain,
    ( spl4_108
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f3436,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_21
    | ~ spl4_60
    | ~ spl4_102
    | ~ spl4_108 ),
    inference(subsumption_resolution,[],[f3435,f974])).

fof(f974,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f973])).

fof(f3435,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_21
    | ~ spl4_60
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3434,f920])).

fof(f920,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f919])).

fof(f3434,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_21
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f3430,f509])).

fof(f3430,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_21 ),
    inference(resolution,[],[f953,f232])).

fof(f232,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f231])).

fof(f953,plain,
    ( ! [X0] :
        ( v4_tops_1(X0,sK0)
        | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f98,f126])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',d6_tops_1)).

fof(f3443,plain,
    ( ~ spl4_335
    | ~ spl4_0
    | spl4_19
    | ~ spl4_66
    | ~ spl4_104
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f3433,f1377,f926,f572,f225,f125,f3441])).

fof(f225,plain,
    ( spl4_19
  <=> ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f926,plain,
    ( spl4_104
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1377,plain,
    ( spl4_152
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f3433,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_19
    | ~ spl4_66
    | ~ spl4_104
    | ~ spl4_152 ),
    inference(subsumption_resolution,[],[f3432,f1378])).

fof(f1378,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_152 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f3432,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_19
    | ~ spl4_66
    | ~ spl4_104 ),
    inference(forward_demodulation,[],[f3431,f927])).

fof(f927,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f926])).

fof(f3431,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_19
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f3429,f573])).

fof(f3429,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_19 ),
    inference(resolution,[],[f953,f226])).

fof(f226,plain,
    ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f225])).

fof(f3427,plain,
    ( spl4_332
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f443,f438,f3425])).

fof(f3425,plain,
    ( spl4_332
  <=> r1_tarski(k3_subset_1(k1_tops_1(sK0,sK1),sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_332])])).

fof(f443,plain,
    ( r1_tarski(k3_subset_1(k1_tops_1(sK0,sK1),sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),sK1)
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f359,f439,f118])).

fof(f359,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,sK2(k1_zfmisc_1(X0))),X0) ),
    inference(unit_resulting_resolution,[],[f281,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f281,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f101,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',dt_k3_subset_1)).

fof(f101,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',existence_m1_subset_1)).

fof(f3420,plain,
    ( spl4_330
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f417,f414,f3418])).

fof(f3418,plain,
    ( spl4_330
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_330])])).

fof(f414,plain,
    ( spl4_46
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f417,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = sK1
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f415,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',involutiveness_k3_subset_1)).

fof(f415,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f414])).

fof(f3413,plain,
    ( spl4_328
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f354,f341,f3411])).

fof(f3411,plain,
    ( spl4_328
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_328])])).

fof(f341,plain,
    ( spl4_38
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f354,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))))),u1_struct_0(sK0))
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f188,f342,f118])).

fof(f342,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f341])).

fof(f188,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(X0)))),X0) ),
    inference(unit_resulting_resolution,[],[f171,f171,f118])).

fof(f171,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f101,f113])).

fof(f3338,plain,
    ( spl4_326
    | ~ spl4_74
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f676,f672,f640,f3336])).

fof(f3336,plain,
    ( spl4_326
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_326])])).

fof(f640,plain,
    ( spl4_74
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f672,plain,
    ( spl4_80
  <=> r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f676,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_74
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f641,f673,f118])).

fof(f673,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f672])).

fof(f641,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f640])).

fof(f3331,plain,
    ( spl4_324
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f427,f332,f125,f3329])).

fof(f3329,plain,
    ( spl4_324
  <=> r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_324])])).

fof(f332,plain,
    ( spl4_36
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f427,plain,
    ( r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f126,f333,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t44_tops_1)).

fof(f333,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f332])).

fof(f3324,plain,
    ( spl4_322
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f392,f332,f125,f3322])).

fof(f3322,plain,
    ( spl4_322
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).

fof(f392,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f126,f333,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t48_pre_topc)).

fof(f3310,plain,
    ( spl4_320
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f790,f139,f3308])).

fof(f3308,plain,
    ( spl4_320
  <=> k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k3_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_320])])).

fof(f139,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f790,plain,
    ( k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k3_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',d1_tops_1)).

fof(f140,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f3303,plain,
    ( spl4_318
    | ~ spl4_12
    | ~ spl4_316 ),
    inference(avatar_split_clause,[],[f3283,f3280,f177,f3301])).

fof(f3301,plain,
    ( spl4_318
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_318])])).

fof(f177,plain,
    ( spl4_12
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f3280,plain,
    ( spl4_316
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_316])])).

fof(f3283,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_316 ),
    inference(unit_resulting_resolution,[],[f178,f3281,f118])).

fof(f3281,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),sK1)
    | ~ spl4_316 ),
    inference(avatar_component_clause,[],[f3280])).

fof(f178,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f3282,plain,
    ( spl4_316
    | ~ spl4_312 ),
    inference(avatar_split_clause,[],[f3274,f3244,f3280])).

fof(f3244,plain,
    ( spl4_312
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_312])])).

fof(f3274,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),sK1)
    | ~ spl4_312 ),
    inference(unit_resulting_resolution,[],[f3245,f113])).

fof(f3245,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_312 ),
    inference(avatar_component_clause,[],[f3244])).

fof(f3253,plain,
    ( spl4_314
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1931,f1895,f3251])).

fof(f3251,plain,
    ( spl4_314
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).

fof(f1895,plain,
    ( spl4_196
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f1931,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),k1_zfmisc_1(sK1))
    | ~ spl4_196 ),
    inference(unit_resulting_resolution,[],[f1896,f114])).

fof(f1896,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),sK1)
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f3246,plain,
    ( spl4_312
    | ~ spl4_178 ),
    inference(avatar_split_clause,[],[f1525,f1522,f3244])).

fof(f1522,plain,
    ( spl4_178
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f1525,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_178 ),
    inference(unit_resulting_resolution,[],[f1523,f105])).

fof(f1523,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_178 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f3222,plain,
    ( spl4_310
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f789,f125,f3220])).

fof(f3220,plain,
    ( spl4_310
  <=> k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f789,plain,
    ( k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f95])).

fof(f3103,plain,
    ( spl4_308
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f2691,f177,f3101])).

fof(f3101,plain,
    ( spl4_308
  <=> r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_308])])).

fof(f2691,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f178,f2601,f118])).

fof(f2601,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(X0))))),X0) ),
    inference(unit_resulting_resolution,[],[f829,f113])).

fof(f829,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(X0))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f270,f105])).

fof(f270,plain,(
    ! [X0] : m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f188,f114])).

fof(f3096,plain,
    ( spl4_306
    | ~ spl4_12
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f2537,f2534,f177,f3094])).

fof(f3094,plain,
    ( spl4_306
  <=> r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f2534,plain,
    ( spl4_264
  <=> r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_264])])).

fof(f2537,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_264 ),
    inference(unit_resulting_resolution,[],[f178,f2535,f118])).

fof(f2535,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),sK1)
    | ~ spl4_264 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f3089,plain,
    ( spl4_304
    | ~ spl4_234 ),
    inference(avatar_split_clause,[],[f2252,f2241,f3087])).

fof(f3087,plain,
    ( spl4_304
  <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_304])])).

fof(f2241,plain,
    ( spl4_234
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f2252,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_234 ),
    inference(unit_resulting_resolution,[],[f2242,f114])).

fof(f2242,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_234 ),
    inference(avatar_component_clause,[],[f2241])).

fof(f3082,plain,
    ( spl4_302
    | ~ spl4_12
    | ~ spl4_234 ),
    inference(avatar_split_clause,[],[f2244,f2241,f177,f3080])).

fof(f3080,plain,
    ( spl4_302
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).

fof(f2244,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_234 ),
    inference(unit_resulting_resolution,[],[f178,f2242,f118])).

fof(f3075,plain,
    ( spl4_300
    | ~ spl4_232 ),
    inference(avatar_split_clause,[],[f2232,f2228,f3073])).

fof(f3073,plain,
    ( spl4_300
  <=> r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_300])])).

fof(f2228,plain,
    ( spl4_232
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f2232,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),u1_struct_0(sK0))
    | ~ spl4_232 ),
    inference(unit_resulting_resolution,[],[f171,f2229,f118])).

fof(f2229,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl4_232 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f3057,plain,
    ( spl4_298
    | ~ spl4_190 ),
    inference(avatar_split_clause,[],[f1880,f1817,f3055])).

fof(f3055,plain,
    ( spl4_298
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_298])])).

fof(f1880,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_190 ),
    inference(unit_resulting_resolution,[],[f1818,f114])).

fof(f3050,plain,
    ( spl4_296
    | ~ spl4_188 ),
    inference(avatar_split_clause,[],[f1854,f1810,f3048])).

fof(f3048,plain,
    ( spl4_296
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_296])])).

fof(f1810,plain,
    ( spl4_188
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f1854,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_188 ),
    inference(unit_resulting_resolution,[],[f1811,f114])).

fof(f1811,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_188 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f3043,plain,
    ( spl4_294
    | ~ spl4_186 ),
    inference(avatar_split_clause,[],[f1843,f1803,f3041])).

fof(f3041,plain,
    ( spl4_294
  <=> m1_subset_1(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_294])])).

fof(f1803,plain,
    ( spl4_186
  <=> r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f1843,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_186 ),
    inference(unit_resulting_resolution,[],[f1804,f114])).

fof(f1804,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),sK1)
    | ~ spl4_186 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f3036,plain,
    ( spl4_292
    | ~ spl4_184 ),
    inference(avatar_split_clause,[],[f1827,f1796,f3034])).

fof(f3034,plain,
    ( spl4_292
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_292])])).

fof(f1796,plain,
    ( spl4_184
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_184])])).

fof(f1827,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_184 ),
    inference(unit_resulting_resolution,[],[f1797,f114])).

fof(f1797,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_184 ),
    inference(avatar_component_clause,[],[f1796])).

fof(f3029,plain,
    ( spl4_290
    | ~ spl4_182 ),
    inference(avatar_split_clause,[],[f1637,f1631,f3027])).

fof(f3027,plain,
    ( spl4_290
  <=> r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_290])])).

fof(f1631,plain,
    ( spl4_182
  <=> r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f1637,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl4_182 ),
    inference(unit_resulting_resolution,[],[f171,f1632,f118])).

fof(f1632,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_182 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f2967,plain,
    ( spl4_288
    | ~ spl4_180 ),
    inference(avatar_split_clause,[],[f1589,f1584,f2965])).

fof(f2965,plain,
    ( spl4_288
  <=> r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).

fof(f1584,plain,
    ( spl4_180
  <=> r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f1589,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0))
    | ~ spl4_180 ),
    inference(unit_resulting_resolution,[],[f171,f1585,f118])).

fof(f1585,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_180 ),
    inference(avatar_component_clause,[],[f1584])).

fof(f2960,plain,
    ( spl4_286
    | ~ spl4_176 ),
    inference(avatar_split_clause,[],[f1513,f1509,f2958])).

fof(f2958,plain,
    ( spl4_286
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_286])])).

fof(f1509,plain,
    ( spl4_176
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f1513,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0))
    | ~ spl4_176 ),
    inference(unit_resulting_resolution,[],[f171,f1510,f118])).

fof(f1510,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_176 ),
    inference(avatar_component_clause,[],[f1509])).

fof(f2953,plain,
    ( spl4_284
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f893,f880,f2951])).

fof(f2951,plain,
    ( spl4_284
  <=> r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f880,plain,
    ( spl4_98
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f893,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl4_98 ),
    inference(unit_resulting_resolution,[],[f171,f881,f118])).

fof(f881,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f880])).

fof(f2890,plain,
    ( spl4_282
    | ~ spl4_12
    | ~ spl4_238 ),
    inference(avatar_split_clause,[],[f2357,f2354,f177,f2888])).

fof(f2888,plain,
    ( spl4_282
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_282])])).

fof(f2354,plain,
    ( spl4_238
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_238])])).

fof(f2357,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_238 ),
    inference(unit_resulting_resolution,[],[f178,f2355,f118])).

fof(f2355,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),sK1)
    | ~ spl4_238 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f2883,plain,
    ( spl4_280
    | ~ spl4_170 ),
    inference(avatar_split_clause,[],[f1782,f1462,f2881])).

fof(f2881,plain,
    ( spl4_280
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).

fof(f1462,plain,
    ( spl4_170
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f1782,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl4_170 ),
    inference(unit_resulting_resolution,[],[f1463,f114])).

fof(f1463,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_170 ),
    inference(avatar_component_clause,[],[f1462])).

fof(f2876,plain,
    ( spl4_278
    | ~ spl4_168 ),
    inference(avatar_split_clause,[],[f1763,f1455,f2874])).

fof(f2874,plain,
    ( spl4_278
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f1455,plain,
    ( spl4_168
  <=> r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f1763,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_168 ),
    inference(unit_resulting_resolution,[],[f1456,f114])).

fof(f1456,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_168 ),
    inference(avatar_component_clause,[],[f1455])).

fof(f2869,plain,
    ( spl4_276
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f1748,f1441,f2867])).

fof(f2867,plain,
    ( spl4_276
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_276])])).

fof(f1748,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_164 ),
    inference(unit_resulting_resolution,[],[f1442,f114])).

fof(f2862,plain,
    ( spl4_274
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f1653,f1377,f2860])).

fof(f2860,plain,
    ( spl4_274
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_274])])).

fof(f1653,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_152 ),
    inference(unit_resulting_resolution,[],[f1378,f114])).

fof(f2855,plain,
    ( spl4_272
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f595,f139,f2853])).

fof(f2853,plain,
    ( spl4_272
  <=> k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_272])])).

fof(f595,plain,
    ( k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',projectivity_k1_tops_1)).

fof(f2848,plain,
    ( spl4_270
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1481,f1322,f2846])).

fof(f2846,plain,
    ( spl4_270
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).

fof(f1322,plain,
    ( spl4_142
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f1481,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK2(k1_zfmisc_1(sK1))))
    | ~ spl4_142 ),
    inference(unit_resulting_resolution,[],[f1323,f114])).

fof(f1323,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK2(k1_zfmisc_1(sK1)))
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f2841,plain,
    ( spl4_268
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f1470,f1315,f2839])).

fof(f2839,plain,
    ( spl4_268
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).

fof(f1315,plain,
    ( spl4_140
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f1470,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1)))))
    | ~ spl4_140 ),
    inference(unit_resulting_resolution,[],[f1316,f114])).

fof(f1316,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))))
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f2642,plain,
    ( spl4_266
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f545,f139,f2640])).

fof(f2640,plain,
    ( spl4_266
  <=> k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f545,plain,
    ( k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',projectivity_k2_pre_topc)).

fof(f2536,plain,
    ( spl4_264
    | ~ spl4_244 ),
    inference(avatar_split_clause,[],[f2528,f2419,f2534])).

fof(f2419,plain,
    ( spl4_244
  <=> m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_244])])).

fof(f2528,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),sK1)
    | ~ spl4_244 ),
    inference(unit_resulting_resolution,[],[f2420,f113])).

fof(f2420,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_244 ),
    inference(avatar_component_clause,[],[f2419])).

fof(f2503,plain,
    ( spl4_262
    | ~ spl4_240 ),
    inference(avatar_split_clause,[],[f2489,f2405,f2501])).

fof(f2501,plain,
    ( spl4_262
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_262])])).

fof(f2405,plain,
    ( spl4_240
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f2489,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_240 ),
    inference(unit_resulting_resolution,[],[f2406,f113])).

fof(f2406,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_240 ),
    inference(avatar_component_clause,[],[f2405])).

fof(f2477,plain,
    ( spl4_260
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f1210,f1131,f2475])).

fof(f2475,plain,
    ( spl4_260
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f1210,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl4_132 ),
    inference(unit_resulting_resolution,[],[f1132,f114])).

fof(f2470,plain,
    ( spl4_258
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f594,f125,f2468])).

fof(f2468,plain,
    ( spl4_258
  <=> k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_258])])).

fof(f594,plain,
    ( k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f112])).

fof(f2463,plain,
    ( spl4_256
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f1196,f1124,f2461])).

fof(f2461,plain,
    ( spl4_256
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).

fof(f1124,plain,
    ( spl4_130
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f1196,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_130 ),
    inference(unit_resulting_resolution,[],[f1125,f114])).

fof(f1125,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f2456,plain,
    ( spl4_254
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f1190,f1117,f2454])).

fof(f2454,plain,
    ( spl4_254
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_254])])).

fof(f1117,plain,
    ( spl4_128
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1190,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),k1_zfmisc_1(sK1))
    | ~ spl4_128 ),
    inference(unit_resulting_resolution,[],[f1118,f114])).

fof(f1118,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),sK1)
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f2449,plain,
    ( spl4_252
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f1176,f1085,f2447])).

fof(f2447,plain,
    ( spl4_252
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_252])])).

fof(f1085,plain,
    ( spl4_124
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f1176,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_124 ),
    inference(unit_resulting_resolution,[],[f1086,f114])).

fof(f1086,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k2_pre_topc(sK0,sK1))
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f2442,plain,
    ( spl4_250
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f1170,f1078,f2440])).

fof(f2440,plain,
    ( spl4_250
  <=> m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).

fof(f1078,plain,
    ( spl4_122
  <=> r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f1170,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_122 ),
    inference(unit_resulting_resolution,[],[f1079,f114])).

fof(f1079,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f2435,plain,
    ( spl4_248
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f1164,f1071,f2433])).

fof(f2433,plain,
    ( spl4_248
  <=> m1_subset_1(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_248])])).

fof(f1071,plain,
    ( spl4_120
  <=> r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f1164,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_120 ),
    inference(unit_resulting_resolution,[],[f1072,f114])).

fof(f1072,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0))
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f2428,plain,
    ( spl4_246
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f544,f125,f2426])).

fof(f2426,plain,
    ( spl4_246
  <=> k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_246])])).

fof(f544,plain,
    ( k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f111])).

fof(f2421,plain,
    ( spl4_244
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f814,f746,f2419])).

fof(f746,plain,
    ( spl4_90
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f814,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_90 ),
    inference(unit_resulting_resolution,[],[f747,f105])).

fof(f747,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f746])).

fof(f2414,plain,
    ( spl4_242
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f618,f389,f2412])).

fof(f2412,plain,
    ( spl4_242
  <=> r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f389,plain,
    ( spl4_42
  <=> r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f618,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))))),u1_struct_0(sK0))
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f171,f390,f118])).

fof(f390,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f389])).

fof(f2407,plain,
    ( spl4_240
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f280,f276,f2405])).

fof(f276,plain,
    ( spl4_28
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f280,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f277,f105])).

fof(f277,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f276])).

fof(f2356,plain,
    ( spl4_238
    | ~ spl4_220 ),
    inference(avatar_split_clause,[],[f2348,f2123,f2354])).

fof(f2123,plain,
    ( spl4_220
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).

fof(f2348,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),sK1)
    | ~ spl4_220 ),
    inference(unit_resulting_resolution,[],[f2124,f113])).

fof(f2124,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_220 ),
    inference(avatar_component_clause,[],[f2123])).

fof(f2295,plain,
    ( spl4_236
    | ~ spl4_232 ),
    inference(avatar_split_clause,[],[f2236,f2228,f2293])).

fof(f2293,plain,
    ( spl4_236
  <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_236])])).

fof(f2236,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_232 ),
    inference(unit_resulting_resolution,[],[f2229,f114])).

fof(f2243,plain,
    ( spl4_234
    | ~ spl4_46
    | ~ spl4_92
    | ~ spl4_210
    | ~ spl4_230 ),
    inference(avatar_split_clause,[],[f2223,f2174,f2088,f753,f414,f2241])).

fof(f753,plain,
    ( spl4_92
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f2088,plain,
    ( spl4_210
  <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_210])])).

fof(f2174,plain,
    ( spl4_230
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_230])])).

fof(f2223,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_46
    | ~ spl4_92
    | ~ spl4_210
    | ~ spl4_230 ),
    inference(forward_demodulation,[],[f2213,f417])).

fof(f2213,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl4_92
    | ~ spl4_210
    | ~ spl4_230 ),
    inference(unit_resulting_resolution,[],[f754,f2089,f2175,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t31_subset_1)).

fof(f2175,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_230 ),
    inference(avatar_component_clause,[],[f2174])).

fof(f2089,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_210 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f754,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f753])).

fof(f2230,plain,
    ( spl4_232
    | ~ spl4_62
    | ~ spl4_230 ),
    inference(avatar_split_clause,[],[f2214,f2174,f522,f2228])).

fof(f522,plain,
    ( spl4_62
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f2214,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl4_62
    | ~ spl4_230 ),
    inference(unit_resulting_resolution,[],[f523,f2175,f118])).

fof(f523,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f522])).

fof(f2176,plain,
    ( spl4_230
    | ~ spl4_210 ),
    inference(avatar_split_clause,[],[f2168,f2088,f2174])).

fof(f2168,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_210 ),
    inference(unit_resulting_resolution,[],[f2089,f113])).

fof(f2159,plain,
    ( spl4_228
    | ~ spl4_116 ),
    inference(avatar_split_clause,[],[f1063,f1001,f2157])).

fof(f2157,plain,
    ( spl4_228
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f1063,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_116 ),
    inference(unit_resulting_resolution,[],[f1002,f114])).

fof(f2152,plain,
    ( spl4_226
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f1044,f987,f2150])).

fof(f2150,plain,
    ( spl4_226
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f987,plain,
    ( spl4_112
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f1044,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_112 ),
    inference(unit_resulting_resolution,[],[f988,f114])).

fof(f988,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f987])).

fof(f2139,plain,
    ( spl4_224
    | ~ spl4_110 ),
    inference(avatar_split_clause,[],[f1040,f980,f2137])).

fof(f2137,plain,
    ( spl4_224
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f980,plain,
    ( spl4_110
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f1040,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k1_zfmisc_1(sK1))
    | ~ spl4_110 ),
    inference(unit_resulting_resolution,[],[f981,f114])).

fof(f981,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),sK1)
    | ~ spl4_110 ),
    inference(avatar_component_clause,[],[f980])).

fof(f2132,plain,
    ( spl4_222
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1030,f973,f2130])).

fof(f2130,plain,
    ( spl4_222
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f1030,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_108 ),
    inference(unit_resulting_resolution,[],[f974,f114])).

fof(f2125,plain,
    ( spl4_220
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f683,f660,f2123])).

fof(f660,plain,
    ( spl4_78
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f683,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_78 ),
    inference(unit_resulting_resolution,[],[f661,f105])).

fof(f661,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f660])).

fof(f2118,plain,
    ( spl4_218
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f664,f653,f2116])).

fof(f2116,plain,
    ( spl4_218
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).

fof(f653,plain,
    ( spl4_76
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f664,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl4_76 ),
    inference(unit_resulting_resolution,[],[f171,f654,f118])).

fof(f654,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f653])).

fof(f2111,plain,
    ( spl4_216
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f530,f522,f2109])).

fof(f2109,plain,
    ( spl4_216
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_216])])).

fof(f530,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0))
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f188,f523,f118])).

fof(f2104,plain,
    ( spl4_214
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f787,f153,f125,f2102])).

fof(f2102,plain,
    ( spl4_214
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_214])])).

fof(f153,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f787,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f95])).

fof(f154,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2097,plain,
    ( spl4_212
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f463,f451,f2095])).

fof(f2095,plain,
    ( spl4_212
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_212])])).

fof(f463,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),u1_struct_0(sK0))
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f188,f452,f118])).

fof(f2090,plain,
    ( spl4_210
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f418,f414,f2088])).

fof(f418,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f415,f105])).

fof(f2083,plain,
    ( spl4_208
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f266,f258,f2081])).

fof(f2081,plain,
    ( spl4_208
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f258,plain,
    ( spl4_26
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f266,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))))),u1_struct_0(sK0))
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f259,f188,f118])).

fof(f259,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f258])).

fof(f2070,plain,
    ( spl4_206
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f2025,f1982,f2068])).

fof(f2068,plain,
    ( spl4_206
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f1982,plain,
    ( spl4_202
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f2025,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_202 ),
    inference(unit_resulting_resolution,[],[f1983,f113])).

fof(f1983,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_202 ),
    inference(avatar_component_clause,[],[f1982])).

fof(f2009,plain,
    ( spl4_204
    | ~ spl4_200 ),
    inference(avatar_split_clause,[],[f1994,f1963,f2007])).

fof(f2007,plain,
    ( spl4_204
  <=> r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f1963,plain,
    ( spl4_200
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f1994,plain,
    ( r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_200 ),
    inference(unit_resulting_resolution,[],[f1964,f113])).

fof(f1964,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_200 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f1984,plain,
    ( spl4_202
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f497,f332,f125,f1982])).

fof(f497,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f126,f333,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',dt_k2_pre_topc)).

fof(f1965,plain,
    ( spl4_200
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f465,f332,f125,f1963])).

fof(f465,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f126,f333,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',dt_k1_tops_1)).

fof(f1904,plain,
    ( spl4_198
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f433,f139,f1902])).

fof(f1902,plain,
    ( spl4_198
  <=> r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),sK2(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f433,plain,
    ( r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),sK2(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f94])).

fof(f1897,plain,
    ( spl4_196
    | ~ spl4_172 ),
    inference(avatar_split_clause,[],[f1500,f1486,f1895])).

fof(f1486,plain,
    ( spl4_172
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f1500,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))))),sK1)
    | ~ spl4_172 ),
    inference(unit_resulting_resolution,[],[f171,f1487,f118])).

fof(f1487,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK1)
    | ~ spl4_172 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1890,plain,
    ( spl4_194
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f895,f880,f1888])).

fof(f1888,plain,
    ( spl4_194
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f895,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_98 ),
    inference(unit_resulting_resolution,[],[f881,f114])).

fof(f1834,plain,
    ( spl4_192
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f398,f139,f1832])).

fof(f1832,plain,
    ( spl4_192
  <=> r1_tarski(sK2(k1_zfmisc_1(u1_struct_0(sK3))),k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f398,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(u1_struct_0(sK3))),k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f93])).

fof(f1819,plain,
    ( spl4_190
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_66
    | ~ spl4_80
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f1613,f1343,f672,f572,f153,f125,f1817])).

fof(f1613,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_66
    | ~ spl4_80
    | ~ spl4_148 ),
    inference(forward_demodulation,[],[f1597,f575])).

fof(f575,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f126,f573,f111])).

fof(f1597,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_80
    | ~ spl4_148 ),
    inference(unit_resulting_resolution,[],[f126,f154,f673,f1344,f99])).

fof(f1812,plain,
    ( spl4_188
    | ~ spl4_48
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1473,f1322,f424,f1810])).

fof(f424,plain,
    ( spl4_48
  <=> r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f1473,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_48
    | ~ spl4_142 ),
    inference(unit_resulting_resolution,[],[f425,f1323,f118])).

fof(f425,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f424])).

fof(f1805,plain,
    ( spl4_186
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f775,f768,f1803])).

fof(f768,plain,
    ( spl4_94
  <=> r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f775,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),sK1)
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f171,f769,f118])).

fof(f769,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f768])).

fof(f1798,plain,
    ( spl4_184
    | ~ spl4_44
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f772,f768,f403,f1796])).

fof(f403,plain,
    ( spl4_44
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f772,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_44
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f404,f769,f118])).

fof(f404,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f403])).

fof(f1633,plain,
    ( spl4_182
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f1609,f1343,f1631])).

fof(f1609,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_148 ),
    inference(unit_resulting_resolution,[],[f1344,f113])).

fof(f1586,plain,
    ( spl4_180
    | ~ spl4_146 ),
    inference(avatar_split_clause,[],[f1575,f1336,f1584])).

fof(f1336,plain,
    ( spl4_146
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f1575,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_146 ),
    inference(unit_resulting_resolution,[],[f1337,f113])).

fof(f1337,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_146 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1524,plain,
    ( spl4_178
    | ~ spl4_172 ),
    inference(avatar_split_clause,[],[f1504,f1486,f1522])).

fof(f1504,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_172 ),
    inference(unit_resulting_resolution,[],[f1487,f114])).

fof(f1511,plain,
    ( spl4_176
    | ~ spl4_26
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1472,f1322,f258,f1509])).

fof(f1472,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_26
    | ~ spl4_142 ),
    inference(unit_resulting_resolution,[],[f259,f1323,f118])).

fof(f1495,plain,
    ( spl4_174
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f432,f125,f1493])).

fof(f1493,plain,
    ( spl4_174
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f432,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f94])).

fof(f1488,plain,
    ( spl4_172
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1471,f1322,f1486])).

fof(f1471,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK1)
    | ~ spl4_142 ),
    inference(unit_resulting_resolution,[],[f171,f1323,f118])).

fof(f1464,plain,
    ( spl4_170
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f909,f276,f153,f125,f1462])).

fof(f909,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f171,f277,f154,f100])).

fof(f1457,plain,
    ( spl4_168
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f862,f276,f153,f125,f1455])).

fof(f862,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f171,f277,f154,f99])).

fof(f1450,plain,
    ( spl4_166
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f397,f125,f1448])).

fof(f1448,plain,
    ( spl4_166
  <=> r1_tarski(sK2(k1_zfmisc_1(u1_struct_0(sK0))),k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f397,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(u1_struct_0(sK0))),k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f93])).

fof(f1443,plain,
    ( spl4_164
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_50
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f861,f572,f438,f153,f125,f1441])).

fof(f861,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_50
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f126,f439,f573,f154,f99])).

fof(f1436,plain,
    ( spl4_162
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f813,f739,f1434])).

fof(f1434,plain,
    ( spl4_162
  <=> m1_subset_1(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f739,plain,
    ( spl4_88
  <=> r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f813,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_88 ),
    inference(unit_resulting_resolution,[],[f740,f114])).

fof(f740,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f739])).

fof(f1429,plain,
    ( spl4_160
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f759,f625,f1427])).

fof(f1427,plain,
    ( spl4_160
  <=> m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f625,plain,
    ( spl4_70
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f759,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_70 ),
    inference(unit_resulting_resolution,[],[f626,f114])).

fof(f626,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f625])).

fof(f1416,plain,
    ( spl4_158
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1403,f1308,f1414])).

fof(f1414,plain,
    ( spl4_158
  <=> r1_tarski(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f1308,plain,
    ( spl4_138
  <=> m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f1403,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3))
    | ~ spl4_138 ),
    inference(unit_resulting_resolution,[],[f1309,f113])).

fof(f1309,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1393,plain,
    ( spl4_156
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f620,f389,f1391])).

fof(f1391,plain,
    ( spl4_156
  <=> m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f620,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f390,f114])).

fof(f1386,plain,
    ( spl4_154
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f586,f382,f1384])).

fof(f1384,plain,
    ( spl4_154
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f382,plain,
    ( spl4_40
  <=> r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f586,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f383,f114])).

fof(f383,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f382])).

fof(f1379,plain,
    ( spl4_152
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f579,f572,f125,f1377])).

fof(f579,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f126,f573,f93])).

fof(f1366,plain,
    ( spl4_150
    | ~ spl4_136 ),
    inference(avatar_split_clause,[],[f1355,f1181,f1364])).

fof(f1364,plain,
    ( spl4_150
  <=> r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f1181,plain,
    ( spl4_136
  <=> m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f1355,plain,
    ( r1_tarski(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),u1_struct_0(sK3))
    | ~ spl4_136 ),
    inference(unit_resulting_resolution,[],[f1182,f113])).

fof(f1182,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_136 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1345,plain,
    ( spl4_148
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f576,f572,f125,f1343])).

fof(f576,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f126,f573,f110])).

fof(f1338,plain,
    ( spl4_146
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f501,f276,f125,f1336])).

fof(f501,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f277,f110])).

fof(f1331,plain,
    ( spl4_144
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f469,f276,f125,f1329])).

fof(f1329,plain,
    ( spl4_144
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f469,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f277,f109])).

fof(f1324,plain,
    ( spl4_142
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f431,f276,f125,f1322])).

fof(f431,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(sK1))),sK2(k1_zfmisc_1(sK1)))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f277,f94])).

fof(f1317,plain,
    ( spl4_140
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f396,f276,f125,f1315])).

fof(f396,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK2(k1_zfmisc_1(sK1))))
    | ~ spl4_0
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f126,f277,f93])).

fof(f1310,plain,
    ( spl4_138
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f503,f139,f1308])).

fof(f503,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f110])).

fof(f1183,plain,
    ( spl4_136
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f471,f139,f1181])).

fof(f471,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f140,f101,f109])).

fof(f1156,plain,
    ( spl4_134
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f1143,f1049,f1154])).

fof(f1154,plain,
    ( spl4_134
  <=> r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f1049,plain,
    ( spl4_118
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f1143,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl4_118 ),
    inference(unit_resulting_resolution,[],[f1050,f113])).

fof(f1050,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1133,plain,
    ( spl4_132
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_60
    | ~ spl4_74
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1019,f966,f640,f508,f153,f125,f1131])).

fof(f1019,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_60
    | ~ spl4_74
    | ~ spl4_106 ),
    inference(forward_demodulation,[],[f1008,f588])).

fof(f588,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f126,f509,f112])).

fof(f1008,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_74
    | ~ spl4_106 ),
    inference(unit_resulting_resolution,[],[f126,f154,f641,f967,f100])).

fof(f1126,plain,
    ( spl4_130
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f494,f483,f1124])).

fof(f483,plain,
    ( spl4_56
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f494,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f171,f484,f118])).

fof(f484,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f483])).

fof(f1119,plain,
    ( spl4_128
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f445,f438,f1117])).

fof(f445,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))))),sK1)
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f188,f439,f118])).

fof(f1108,plain,
    ( spl4_126
    | ~ spl4_114 ),
    inference(avatar_split_clause,[],[f1097,f994,f1106])).

fof(f1106,plain,
    ( spl4_126
  <=> r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f994,plain,
    ( spl4_114
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f1097,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl4_114 ),
    inference(unit_resulting_resolution,[],[f995,f113])).

fof(f995,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_114 ),
    inference(avatar_component_clause,[],[f994])).

fof(f1087,plain,
    ( spl4_124
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f408,f403,f1085])).

fof(f408,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),k2_pre_topc(sK0,sK1))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f188,f404,f118])).

fof(f1080,plain,
    ( spl4_122
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f406,f403,f1078])).

fof(f406,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f359,f404,f118])).

fof(f1073,plain,
    ( spl4_120
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f353,f341,f1071])).

fof(f353,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0))
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f171,f342,f118])).

fof(f1051,plain,
    ( spl4_118
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f502,f125,f1049])).

fof(f502,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f110])).

fof(f1003,plain,
    ( spl4_116
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_44
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f906,f508,f403,f153,f125,f1001])).

fof(f906,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_44
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f126,f154,f404,f509,f100])).

fof(f996,plain,
    ( spl4_114
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f470,f125,f994])).

fof(f470,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f126,f101,f109])).

fof(f989,plain,
    ( spl4_112
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f679,f672,f987])).

fof(f679,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f171,f673,f118])).

fof(f982,plain,
    ( spl4_110
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f646,f640,f980])).

fof(f646,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),sK1)
    | ~ spl4_74 ),
    inference(unit_resulting_resolution,[],[f171,f641,f118])).

fof(f975,plain,
    ( spl4_108
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f513,f508,f125,f973])).

fof(f513,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f126,f509,f94])).

fof(f968,plain,
    ( spl4_106
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f512,f508,f125,f966])).

fof(f512,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f126,f509,f109])).

fof(f928,plain,
    ( spl4_104
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f592,f153,f125,f926])).

fof(f592,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f112])).

fof(f921,plain,
    ( spl4_102
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f542,f153,f125,f919])).

fof(f542,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f111])).

fof(f902,plain,
    ( spl4_100
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f346,f153,f900])).

fof(f900,plain,
    ( spl4_100
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f346,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f154,f106])).

fof(f882,plain,
    ( spl4_98
    | ~ spl4_12
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f771,f768,f177,f880])).

fof(f771,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_94 ),
    inference(unit_resulting_resolution,[],[f178,f769,f118])).

fof(f875,plain,
    ( spl4_96
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f616,f605,f873])).

fof(f873,plain,
    ( spl4_96
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f605,plain,
    ( spl4_68
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f616,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl4_68 ),
    inference(unit_resulting_resolution,[],[f606,f114])).

fof(f606,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f605])).

fof(f770,plain,
    ( spl4_94
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f762,f632,f768])).

fof(f632,plain,
    ( spl4_72
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f762,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl4_72 ),
    inference(unit_resulting_resolution,[],[f633,f113])).

fof(f633,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f632])).

fof(f755,plain,
    ( spl4_92
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f567,f555,f753])).

fof(f555,plain,
    ( spl4_64
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f567,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_64 ),
    inference(unit_resulting_resolution,[],[f556,f114])).

fof(f556,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f555])).

fof(f748,plain,
    ( spl4_90
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f537,f490,f746])).

fof(f490,plain,
    ( spl4_58
  <=> r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f537,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl4_58 ),
    inference(unit_resulting_resolution,[],[f491,f114])).

fof(f491,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f490])).

fof(f741,plain,
    ( spl4_88
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f529,f522,f739])).

fof(f529,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_62 ),
    inference(unit_resulting_resolution,[],[f171,f523,f118])).

fof(f734,plain,
    ( spl4_86
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f496,f483,f732])).

fof(f732,plain,
    ( spl4_86
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f496,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f484,f114])).

fof(f727,plain,
    ( spl4_84
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f478,f424,f725])).

fof(f725,plain,
    ( spl4_84
  <=> m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f478,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f425,f114])).

fof(f691,plain,
    ( spl4_82
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f681,f672,f689])).

fof(f689,plain,
    ( spl4_82
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f681,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl4_80 ),
    inference(unit_resulting_resolution,[],[f673,f114])).

fof(f674,plain,
    ( spl4_80
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f667,f153,f146,f125,f672])).

fof(f146,plain,
    ( spl4_6
  <=> v4_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f667,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f147,f154,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f147,plain,
    ( v4_tops_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f662,plain,
    ( spl4_78
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f648,f640,f660])).

fof(f648,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_74 ),
    inference(unit_resulting_resolution,[],[f641,f114])).

fof(f655,plain,
    ( spl4_76
    | ~ spl4_12
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f643,f640,f177,f653])).

fof(f643,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_74 ),
    inference(unit_resulting_resolution,[],[f178,f641,f118])).

fof(f642,plain,
    ( spl4_74
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f635,f153,f146,f125,f640])).

fof(f635,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f147,f154,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f634,plain,
    ( spl4_72
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f473,f458,f632])).

fof(f458,plain,
    ( spl4_54
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f473,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_54 ),
    inference(unit_resulting_resolution,[],[f459,f105])).

fof(f459,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f458])).

fof(f627,plain,
    ( spl4_70
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f462,f451,f625])).

fof(f462,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f171,f452,f118])).

fof(f607,plain,
    ( spl4_68
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f599,f572,f153,f125,f605])).

fof(f599,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_66 ),
    inference(backward_demodulation,[],[f592,f578])).

fof(f578,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_66 ),
    inference(unit_resulting_resolution,[],[f126,f573,f94])).

fof(f574,plain,
    ( spl4_66
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f464,f451,f572])).

fof(f464,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f452,f114])).

fof(f557,plain,
    ( spl4_64
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f549,f508,f153,f125,f555])).

fof(f549,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f542,f514])).

fof(f514,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f126,f509,f93])).

fof(f524,plain,
    ( spl4_62
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f517,f508,f522])).

fof(f517,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_60 ),
    inference(unit_resulting_resolution,[],[f509,f113])).

fof(f510,plain,
    ( spl4_60
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f500,f153,f125,f508])).

fof(f500,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f110])).

fof(f492,plain,
    ( spl4_58
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f444,f438,f490])).

fof(f444,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1)
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f171,f439,f118])).

fof(f485,plain,
    ( spl4_56
    | ~ spl4_44
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f442,f438,f403,f483])).

fof(f442,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_44
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f404,f439,f118])).

fof(f460,plain,
    ( spl4_54
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f446,f438,f458])).

fof(f446,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f439,f114])).

fof(f453,plain,
    ( spl4_52
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f441,f438,f177,f451])).

fof(f441,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_50 ),
    inference(unit_resulting_resolution,[],[f178,f439,f118])).

fof(f440,plain,
    ( spl4_50
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f430,f153,f125,f438])).

fof(f430,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f94])).

fof(f426,plain,
    ( spl4_48
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f407,f403,f424])).

fof(f407,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f171,f404,f118])).

fof(f416,plain,
    ( spl4_46
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f409,f403,f414])).

fof(f409,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f404,f114])).

fof(f405,plain,
    ( spl4_44
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f395,f153,f125,f403])).

fof(f395,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f126,f154,f93])).

fof(f391,plain,
    ( spl4_42
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f368,f177,f389])).

fof(f368,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2(k1_zfmisc_1(sK1))),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f178,f359,f118])).

fof(f384,plain,
    ( spl4_40
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f261,f258,f382])).

fof(f261,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(sK1)))),u1_struct_0(sK0))
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f171,f259,f118])).

fof(f343,plain,
    ( spl4_38
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f336,f332,f341])).

fof(f336,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f333,f113])).

fof(f334,plain,
    ( spl4_36
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f282,f153,f332])).

fof(f282,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f154,f105])).

fof(f326,plain,
    ( spl4_34
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f307,f299,f132,f324])).

fof(f324,plain,
    ( spl4_34
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f132,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f299,plain,
    ( spl4_32
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f307,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f300,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f156,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t6_boole)).

fof(f156,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f133,f92])).

fof(f133,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f300,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f299])).

fof(f301,plain,
    ( spl4_32
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f294,f288,f132,f299])).

fof(f288,plain,
    ( spl4_30
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f294,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f101,f292,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t2_subset)).

fof(f292,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f133,f289,f119])).

fof(f119,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t5_subset)).

fof(f289,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl4_30
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f283,f249,f288])).

fof(f249,plain,
    ( spl4_24
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f283,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f250,f105])).

fof(f250,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f278,plain,
    ( spl4_28
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f262,f258,f276])).

fof(f262,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f259,f114])).

fof(f260,plain,
    ( spl4_26
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f187,f177,f258])).

fof(f187,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f171,f178,f118])).

fof(f251,plain,
    ( spl4_24
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f220,f216,f249])).

fof(f216,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f220,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f101,f217])).

fof(f217,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f240,plain,
    ( spl4_22
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f219,f216,f238])).

fof(f238,plain,
    ( spl4_22
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f219,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_16 ),
    inference(superposition,[],[f171,f217])).

fof(f233,plain,
    ( ~ spl4_19
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f88,f231,f225])).

fof(f88,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
      | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) )
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(sK0,X1),sK0)
            | ~ v4_tops_1(k1_tops_1(sK0,X1),sK0) )
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_tops_1(k2_pre_topc(X0,sK1),X0)
          | ~ v4_tops_1(k1_tops_1(X0,sK1),X0) )
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',t111_tops_1)).

fof(f218,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f203,f195,f132,f216])).

fof(f195,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f203,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f196,f158])).

fof(f196,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f190,f132,f195])).

fof(f190,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f101,f189,f104])).

fof(f189,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f133,f101,f119])).

fof(f179,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f172,f153,f177])).

fof(f172,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f154,f113])).

fof(f167,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f156,f132,f165])).

fof(f165,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f155,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f86,f153])).

fof(f86,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

fof(f148,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f87,f146])).

fof(f87,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f141,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f120,f139])).

fof(f120,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f83])).

fof(f83,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',existence_l1_pre_topc)).

fof(f134,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f89,f132])).

fof(f89,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t111_tops_1.p',dt_o_0_0_xboole_0)).

fof(f127,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f85,f125])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
