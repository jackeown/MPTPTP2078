%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t23_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:16 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  674 (2466 expanded)
%              Number of leaves         :  192 (1036 expanded)
%              Depth                    :   12
%              Number of atoms          : 1500 (6702 expanded)
%              Number of equality atoms :   27 ( 119 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f80,f87,f94,f104,f125,f138,f147,f157,f168,f189,f196,f219,f228,f256,f267,f275,f286,f298,f307,f336,f343,f366,f379,f386,f393,f415,f424,f431,f440,f453,f481,f488,f525,f532,f554,f577,f601,f616,f626,f633,f640,f661,f668,f684,f691,f716,f725,f734,f751,f767,f774,f801,f808,f830,f837,f869,f876,f886,f898,f933,f949,f956,f963,f991,f998,f1005,f1017,f1024,f1031,f1038,f1060,f1067,f1091,f1098,f1154,f1161,f1168,f1175,f1182,f1189,f1196,f1203,f1210,f1220,f1264,f1285,f1292,f1299,f1306,f1313,f1344,f1351,f1386,f1400,f1412,f1435,f1447,f1474,f1488,f1561,f1575,f1594,f1602,f1615,f1632,f1646,f1653,f1690,f1697,f1704,f1711,f1761,f1768,f1775,f1794,f1808,f1821,f1828,f1841,f1848,f1855,f1873,f1909,f1934,f1941,f1948,f2059,f2066,f2073,f2080,f2163,f2260,f2293,f2300,f2327,f2342,f2366,f2391,f2450,f2452,f2717,f2728,f2759,f2791,f2805,f2812,f2832,f2839,f2846,f2853,f2860,f2900,f2907,f2919,f2936,f3003,f3010,f3017,f3024,f3031,f3038,f3045,f3066,f3083,f3099,f3114,f3121,f3135,f3149,f3156,f3164,f3172,f3189])).

fof(f3189,plain,
    ( spl6_7
    | ~ spl6_82
    | ~ spl6_158
    | ~ spl6_306 ),
    inference(avatar_contradiction_clause,[],[f3188])).

fof(f3188,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_82
    | ~ spl6_158
    | ~ spl6_306 ),
    inference(subsumption_resolution,[],[f3185,f1325])).

fof(f1325,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK5(sK2,sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_7
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f93,f1181,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r1_tarski(sK4(X0,X1),X3)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK5(X1,X4))
              & r2_hidden(sK5(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK5(X1,X4))
        & r2_hidden(sK5(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',d2_setfam_1)).

fof(f1181,plain,
    ( r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,sK2))),sK2)
    | ~ spl6_158 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1180,plain,
    ( spl6_158
  <=> r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f93,plain,
    ( ~ r1_setfam_1(sK0,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_7
  <=> ~ r1_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f3185,plain,
    ( r1_tarski(sK4(sK0,sK2),sK5(sK2,sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_82
    | ~ spl6_306 ),
    inference(unit_resulting_resolution,[],[f639,f2918,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t1_xboole_1)).

fof(f2918,plain,
    ( r1_tarski(sK5(sK1,sK4(sK0,sK2)),sK5(sK2,sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_306 ),
    inference(avatar_component_clause,[],[f2917])).

fof(f2917,plain,
    ( spl6_306
  <=> r1_tarski(sK5(sK1,sK4(sK0,sK2)),sK5(sK2,sK5(sK1,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_306])])).

fof(f639,plain,
    ( r1_tarski(sK4(sK0,sK2),sK5(sK1,sK4(sK0,sK2)))
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl6_82
  <=> r1_tarski(sK4(sK0,sK2),sK5(sK1,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f3172,plain,
    ( ~ spl6_343
    | spl6_335 ),
    inference(avatar_split_clause,[],[f3136,f3133,f3170])).

fof(f3170,plain,
    ( spl6_343
  <=> ~ r1_tarski(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_343])])).

fof(f3133,plain,
    ( spl6_335
  <=> ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_335])])).

fof(f3136,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK3(sK1)))))
    | ~ spl6_335 ),
    inference(unit_resulting_resolution,[],[f108,f3134,f64])).

fof(f3134,plain,
    ( ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK1)))
    | ~ spl6_335 ),
    inference(avatar_component_clause,[],[f3133])).

fof(f108,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t3_subset)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',existence_m1_subset_1)).

fof(f3164,plain,
    ( ~ spl6_341
    | spl6_329 ),
    inference(avatar_split_clause,[],[f3104,f3097,f3162])).

fof(f3162,plain,
    ( spl6_341
  <=> ~ r2_hidden(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_341])])).

fof(f3097,plain,
    ( spl6_329
  <=> ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_329])])).

fof(f3104,plain,
    ( ~ r2_hidden(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK1)))
    | ~ spl6_329 ),
    inference(unit_resulting_resolution,[],[f3098,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t1_subset)).

fof(f3098,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK1)))
    | ~ spl6_329 ),
    inference(avatar_component_clause,[],[f3097])).

fof(f3156,plain,
    ( spl6_338
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f737,f666,f3154])).

fof(f3154,plain,
    ( spl6_338
  <=> r1_tarski(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK4(sK0,sK2))))),sK5(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_338])])).

fof(f666,plain,
    ( spl6_86
  <=> r1_tarski(sK4(sK0,sK2),sK5(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f737,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK4(sK0,sK2))))),sK5(sK0,sK4(sK0,sK2)))
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f118,f667,f64])).

fof(f667,plain,
    ( r1_tarski(sK4(sK0,sK2),sK5(sK0,sK4(sK0,sK2)))
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f666])).

fof(f118,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))),X0) ),
    inference(unit_resulting_resolution,[],[f108,f108,f64])).

fof(f3149,plain,
    ( ~ spl6_337
    | spl6_333 ),
    inference(avatar_split_clause,[],[f3125,f3119,f3147])).

fof(f3147,plain,
    ( spl6_337
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_337])])).

fof(f3119,plain,
    ( spl6_333
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_333])])).

fof(f3125,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK1))))
    | ~ spl6_333 ),
    inference(unit_resulting_resolution,[],[f3120,f54])).

fof(f3120,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK1))))
    | ~ spl6_333 ),
    inference(avatar_component_clause,[],[f3119])).

fof(f3135,plain,
    ( ~ spl6_335
    | spl6_333 ),
    inference(avatar_split_clause,[],[f3122,f3119,f3133])).

fof(f3122,plain,
    ( ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK1)))
    | ~ spl6_333 ),
    inference(unit_resulting_resolution,[],[f3120,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3121,plain,
    ( ~ spl6_333
    | ~ spl6_10
    | spl6_329 ),
    inference(avatar_split_clause,[],[f3101,f3097,f123,f3119])).

fof(f123,plain,
    ( spl6_10
  <=> r2_hidden(sK4(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f3101,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK1))))
    | ~ spl6_10
    | ~ spl6_329 ),
    inference(unit_resulting_resolution,[],[f124,f3098,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t4_subset)).

fof(f124,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f3114,plain,
    ( spl6_330
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f708,f638,f3112])).

fof(f3112,plain,
    ( spl6_330
  <=> r1_tarski(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK4(sK0,sK2))))),sK5(sK1,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_330])])).

fof(f708,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK4(sK0,sK2))))),sK5(sK1,sK4(sK0,sK2)))
    | ~ spl6_82 ),
    inference(unit_resulting_resolution,[],[f118,f639,f64])).

fof(f3099,plain,
    ( ~ spl6_329
    | spl6_327 ),
    inference(avatar_split_clause,[],[f3090,f3081,f3097])).

fof(f3081,plain,
    ( spl6_327
  <=> ~ r1_tarski(sK4(sK0,sK2),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_327])])).

fof(f3090,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK1)))
    | ~ spl6_327 ),
    inference(unit_resulting_resolution,[],[f3082,f60])).

fof(f3082,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK3(sK1))
    | ~ spl6_327 ),
    inference(avatar_component_clause,[],[f3081])).

fof(f3083,plain,
    ( ~ spl6_327
    | ~ spl6_150
    | spl6_313 ),
    inference(avatar_split_clause,[],[f3073,f3008,f1152,f3081])).

fof(f1152,plain,
    ( spl6_150
  <=> r1_tarski(sK3(sK1),sK5(sK2,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).

fof(f3008,plain,
    ( spl6_313
  <=> ~ r1_tarski(sK4(sK0,sK2),sK5(sK2,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_313])])).

fof(f3073,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK3(sK1))
    | ~ spl6_150
    | ~ spl6_313 ),
    inference(unit_resulting_resolution,[],[f1153,f3009,f64])).

fof(f3009,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK5(sK2,sK3(sK1)))
    | ~ spl6_313 ),
    inference(avatar_component_clause,[],[f3008])).

fof(f1153,plain,
    ( r1_tarski(sK3(sK1),sK5(sK2,sK3(sK1)))
    | ~ spl6_150 ),
    inference(avatar_component_clause,[],[f1152])).

fof(f3066,plain,
    ( spl6_324
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f511,f422,f3064])).

fof(f3064,plain,
    ( spl6_324
  <=> r1_tarski(sK5(sK0,sK4(sK0,sK2)),sK5(sK0,sK5(sK0,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_324])])).

fof(f422,plain,
    ( spl6_54
  <=> r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f511,plain,
    ( r1_tarski(sK5(sK0,sK4(sK0,sK2)),sK5(sK0,sK5(sK0,sK4(sK0,sK2))))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f52,f423,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK5(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f423,plain,
    ( r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK0)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f422])).

fof(f52,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',reflexivity_r1_setfam_1)).

fof(f3045,plain,
    ( spl6_322
    | ~ spl6_152 ),
    inference(avatar_split_clause,[],[f1223,f1159,f3043])).

fof(f3043,plain,
    ( spl6_322
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(sK5(sK1,sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_322])])).

fof(f1159,plain,
    ( spl6_152
  <=> r1_tarski(sK3(sK1),sK5(sK1,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f1223,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(sK5(sK1,sK3(sK1))))
    | ~ spl6_152 ),
    inference(unit_resulting_resolution,[],[f1160,f61])).

fof(f1160,plain,
    ( r1_tarski(sK3(sK1),sK5(sK1,sK3(sK1)))
    | ~ spl6_152 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f3038,plain,
    ( spl6_320
    | ~ spl6_150 ),
    inference(avatar_split_clause,[],[f1213,f1152,f3036])).

fof(f3036,plain,
    ( spl6_320
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(sK5(sK2,sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_320])])).

fof(f1213,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(sK5(sK2,sK3(sK1))))
    | ~ spl6_150 ),
    inference(unit_resulting_resolution,[],[f1153,f61])).

fof(f3031,plain,
    ( spl6_318
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f852,f689,f3029])).

fof(f3029,plain,
    ( spl6_318
  <=> r2_hidden(sK5(sK1,sK5(sK1,sK3(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_318])])).

fof(f689,plain,
    ( spl6_90
  <=> r2_hidden(sK5(sK1,sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f852,plain,
    ( r2_hidden(sK5(sK1,sK5(sK1,sK3(sK1))),sK1)
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f52,f690,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(sK5(X1,X4),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f690,plain,
    ( r2_hidden(sK5(sK1,sK3(sK1)),sK1)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f689])).

fof(f3024,plain,
    ( spl6_316
    | ~ spl6_4
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f851,f689,f85,f3022])).

fof(f3022,plain,
    ( spl6_316
  <=> r2_hidden(sK5(sK2,sK5(sK1,sK3(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_316])])).

fof(f85,plain,
    ( spl6_4
  <=> r1_setfam_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f851,plain,
    ( r2_hidden(sK5(sK2,sK5(sK1,sK3(sK1))),sK2)
    | ~ spl6_4
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f86,f690,f56])).

fof(f86,plain,
    ( r1_setfam_1(sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f3017,plain,
    ( spl6_314
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f510,f422,f78,f3015])).

fof(f3015,plain,
    ( spl6_314
  <=> r1_tarski(sK5(sK0,sK4(sK0,sK2)),sK5(sK1,sK5(sK0,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_314])])).

fof(f78,plain,
    ( spl6_2
  <=> r1_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f510,plain,
    ( r1_tarski(sK5(sK0,sK4(sK0,sK2)),sK5(sK1,sK5(sK0,sK4(sK0,sK2))))
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f79,f423,f57])).

fof(f79,plain,
    ( r1_setfam_1(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f3010,plain,
    ( ~ spl6_313
    | spl6_7
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f698,f682,f92,f3008])).

fof(f682,plain,
    ( spl6_88
  <=> r2_hidden(sK5(sK2,sK3(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f698,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK5(sK2,sK3(sK1)))
    | ~ spl6_7
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f93,f683,f59])).

fof(f683,plain,
    ( r2_hidden(sK5(sK2,sK3(sK1)),sK2)
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f682])).

fof(f3003,plain,
    ( spl6_310
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f695,f682,f3001])).

fof(f3001,plain,
    ( spl6_310
  <=> r2_hidden(sK5(sK2,sK5(sK2,sK3(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_310])])).

fof(f695,plain,
    ( r2_hidden(sK5(sK2,sK5(sK2,sK3(sK1))),sK2)
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f52,f683,f56])).

fof(f2936,plain,
    ( spl6_308
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f461,f377,f2934])).

fof(f2934,plain,
    ( spl6_308
  <=> r1_tarski(sK5(sK1,sK4(sK0,sK2)),sK5(sK1,sK5(sK1,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_308])])).

fof(f377,plain,
    ( spl6_46
  <=> r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f461,plain,
    ( r1_tarski(sK5(sK1,sK4(sK0,sK2)),sK5(sK1,sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f52,f378,f57])).

fof(f378,plain,
    ( r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK1)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f377])).

fof(f2919,plain,
    ( spl6_306
    | ~ spl6_4
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f460,f377,f85,f2917])).

fof(f460,plain,
    ( r1_tarski(sK5(sK1,sK4(sK0,sK2)),sK5(sK2,sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_4
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f86,f378,f57])).

fof(f2907,plain,
    ( spl6_304
    | ~ spl6_256 ),
    inference(avatar_split_clause,[],[f2128,f2064,f2905])).

fof(f2905,plain,
    ( spl6_304
  <=> m1_subset_1(sK5(sK0,sK5(sK0,sK3(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_304])])).

fof(f2064,plain,
    ( spl6_256
  <=> r2_hidden(sK5(sK0,sK5(sK0,sK3(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_256])])).

fof(f2128,plain,
    ( m1_subset_1(sK5(sK0,sK5(sK0,sK3(sK0))),sK0)
    | ~ spl6_256 ),
    inference(unit_resulting_resolution,[],[f2065,f54])).

fof(f2065,plain,
    ( r2_hidden(sK5(sK0,sK5(sK0,sK3(sK0))),sK0)
    | ~ spl6_256 ),
    inference(avatar_component_clause,[],[f2064])).

fof(f2900,plain,
    ( ~ spl6_303
    | ~ spl6_256 ),
    inference(avatar_split_clause,[],[f2127,f2064,f2898])).

fof(f2898,plain,
    ( spl6_303
  <=> ~ r2_hidden(sK0,sK5(sK0,sK5(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_303])])).

fof(f2127,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK5(sK0,sK3(sK0))))
    | ~ spl6_256 ),
    inference(unit_resulting_resolution,[],[f2065,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',antisymmetry_r2_hidden)).

fof(f2860,plain,
    ( spl6_300
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f2113,f2057,f2858])).

fof(f2858,plain,
    ( spl6_300
  <=> m1_subset_1(sK5(sK1,sK5(sK0,sK3(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_300])])).

fof(f2057,plain,
    ( spl6_254
  <=> r2_hidden(sK5(sK1,sK5(sK0,sK3(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_254])])).

fof(f2113,plain,
    ( m1_subset_1(sK5(sK1,sK5(sK0,sK3(sK0))),sK1)
    | ~ spl6_254 ),
    inference(unit_resulting_resolution,[],[f2058,f54])).

fof(f2058,plain,
    ( r2_hidden(sK5(sK1,sK5(sK0,sK3(sK0))),sK1)
    | ~ spl6_254 ),
    inference(avatar_component_clause,[],[f2057])).

fof(f2853,plain,
    ( ~ spl6_299
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f2112,f2057,f2851])).

fof(f2851,plain,
    ( spl6_299
  <=> ~ r2_hidden(sK1,sK5(sK1,sK5(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_299])])).

fof(f2112,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK5(sK0,sK3(sK0))))
    | ~ spl6_254 ),
    inference(unit_resulting_resolution,[],[f2058,f53])).

fof(f2846,plain,
    ( spl6_296
    | ~ spl6_252 ),
    inference(avatar_split_clause,[],[f2098,f1946,f2844])).

fof(f2844,plain,
    ( spl6_296
  <=> m1_subset_1(sK5(sK1,sK5(sK1,sK3(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_296])])).

fof(f1946,plain,
    ( spl6_252
  <=> r2_hidden(sK5(sK1,sK5(sK1,sK3(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_252])])).

fof(f2098,plain,
    ( m1_subset_1(sK5(sK1,sK5(sK1,sK3(sK0))),sK1)
    | ~ spl6_252 ),
    inference(unit_resulting_resolution,[],[f1947,f54])).

fof(f1947,plain,
    ( r2_hidden(sK5(sK1,sK5(sK1,sK3(sK0))),sK1)
    | ~ spl6_252 ),
    inference(avatar_component_clause,[],[f1946])).

fof(f2839,plain,
    ( ~ spl6_295
    | ~ spl6_252 ),
    inference(avatar_split_clause,[],[f2097,f1946,f2837])).

fof(f2837,plain,
    ( spl6_295
  <=> ~ r2_hidden(sK1,sK5(sK1,sK5(sK1,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_295])])).

fof(f2097,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK5(sK1,sK3(sK0))))
    | ~ spl6_252 ),
    inference(unit_resulting_resolution,[],[f1947,f53])).

fof(f2832,plain,
    ( spl6_292
    | ~ spl6_250 ),
    inference(avatar_split_clause,[],[f2083,f1939,f2830])).

fof(f2830,plain,
    ( spl6_292
  <=> m1_subset_1(sK5(sK2,sK5(sK1,sK3(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_292])])).

fof(f1939,plain,
    ( spl6_250
  <=> r2_hidden(sK5(sK2,sK5(sK1,sK3(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_250])])).

fof(f2083,plain,
    ( m1_subset_1(sK5(sK2,sK5(sK1,sK3(sK0))),sK2)
    | ~ spl6_250 ),
    inference(unit_resulting_resolution,[],[f1940,f54])).

fof(f1940,plain,
    ( r2_hidden(sK5(sK2,sK5(sK1,sK3(sK0))),sK2)
    | ~ spl6_250 ),
    inference(avatar_component_clause,[],[f1939])).

fof(f2812,plain,
    ( ~ spl6_291
    | ~ spl6_250 ),
    inference(avatar_split_clause,[],[f2082,f1939,f2810])).

fof(f2810,plain,
    ( spl6_291
  <=> ~ r2_hidden(sK2,sK5(sK2,sK5(sK1,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_291])])).

fof(f2082,plain,
    ( ~ r2_hidden(sK2,sK5(sK2,sK5(sK1,sK3(sK0))))
    | ~ spl6_250 ),
    inference(unit_resulting_resolution,[],[f1940,f53])).

fof(f2805,plain,
    ( ~ spl6_289
    | spl6_59 ),
    inference(avatar_split_clause,[],[f1122,f438,f2803])).

fof(f2803,plain,
    ( spl6_289
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_289])])).

fof(f438,plain,
    ( spl6_59
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f1122,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f439,f562,f65])).

fof(f562,plain,(
    ! [X0] : m1_subset_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f118,f61])).

fof(f439,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f438])).

fof(f2791,plain,
    ( spl6_286
    | ~ spl6_0
    | ~ spl6_282 ),
    inference(avatar_split_clause,[],[f2760,f2726,f71,f2789])).

fof(f2789,plain,
    ( spl6_286
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_286])])).

fof(f71,plain,
    ( spl6_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f2726,plain,
    ( spl6_282
  <=> r2_hidden(sK4(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_282])])).

fof(f2760,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_282 ),
    inference(unit_resulting_resolution,[],[f2727,f1660])).

fof(f1660,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_zfmisc_1(o_0_0_xboole_0))
        | o_0_0_xboole_0 = X3 )
    | ~ spl6_0 ),
    inference(resolution,[],[f1585,f54])).

fof(f1585,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_0 ),
    inference(resolution,[],[f605,f72])).

fof(f72,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f71])).

fof(f605,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_0 ),
    inference(resolution,[],[f313,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t5_subset)).

fof(f313,plain,
    ( ! [X7] :
        ( r2_hidden(sK3(X7),X7)
        | o_0_0_xboole_0 = X7 )
    | ~ spl6_0 ),
    inference(resolution,[],[f114,f51])).

fof(f114,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_0 ),
    inference(resolution,[],[f55,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_0 ),
    inference(backward_demodulation,[],[f95,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t6_boole)).

fof(f95,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f72,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t2_subset)).

fof(f2727,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_282 ),
    inference(avatar_component_clause,[],[f2726])).

fof(f2759,plain,
    ( ~ spl6_285
    | spl6_273 ),
    inference(avatar_split_clause,[],[f2625,f2325,f2757])).

fof(f2757,plain,
    ( spl6_285
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_285])])).

fof(f2325,plain,
    ( spl6_273
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_273])])).

fof(f2625,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_273 ),
    inference(unit_resulting_resolution,[],[f51,f2326,f65])).

fof(f2326,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_273 ),
    inference(avatar_component_clause,[],[f2325])).

fof(f2728,plain,
    ( spl6_282
    | spl6_271 ),
    inference(avatar_split_clause,[],[f2319,f2298,f2726])).

fof(f2298,plain,
    ( spl6_271
  <=> ~ r1_setfam_1(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_271])])).

fof(f2319,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_271 ),
    inference(unit_resulting_resolution,[],[f2299,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2299,plain,
    ( ~ r1_setfam_1(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_271 ),
    inference(avatar_component_clause,[],[f2298])).

fof(f2717,plain,
    ( spl6_280
    | ~ spl6_0
    | ~ spl6_278 ),
    inference(avatar_split_clause,[],[f2684,f2389,f71,f2715])).

fof(f2715,plain,
    ( spl6_280
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_280])])).

fof(f2389,plain,
    ( spl6_278
  <=> r2_hidden(sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_278])])).

fof(f2684,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_278 ),
    inference(unit_resulting_resolution,[],[f2390,f1660])).

fof(f2390,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_278 ),
    inference(avatar_component_clause,[],[f2389])).

fof(f2452,plain,
    ( ~ spl6_0
    | ~ spl6_262
    | spl6_271 ),
    inference(avatar_contradiction_clause,[],[f2451])).

fof(f2451,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_262
    | ~ spl6_271 ),
    inference(subsumption_resolution,[],[f2418,f105])).

fof(f105,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t7_boole)).

fof(f2418,plain,
    ( r2_hidden(sK4(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_262
    | ~ spl6_271 ),
    inference(backward_demodulation,[],[f2156,f2319])).

fof(f2156,plain,
    ( o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl6_262 ),
    inference(avatar_component_clause,[],[f2155])).

fof(f2155,plain,
    ( spl6_262
  <=> o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_262])])).

fof(f2450,plain,
    ( ~ spl6_0
    | ~ spl6_262
    | spl6_271 ),
    inference(avatar_contradiction_clause,[],[f2449])).

fof(f2449,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_262
    | ~ spl6_271 ),
    inference(subsumption_resolution,[],[f2417,f116])).

fof(f116,plain,
    ( ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0)
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f105,f58])).

fof(f2417,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_262
    | ~ spl6_271 ),
    inference(backward_demodulation,[],[f2156,f2299])).

fof(f2391,plain,
    ( spl6_278
    | ~ spl6_264 ),
    inference(avatar_split_clause,[],[f2275,f2161,f2389])).

fof(f2161,plain,
    ( spl6_264
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_264])])).

fof(f2275,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_264 ),
    inference(unit_resulting_resolution,[],[f52,f2162,f56])).

fof(f2162,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_264 ),
    inference(avatar_component_clause,[],[f2161])).

fof(f2366,plain,
    ( spl6_276
    | ~ spl6_264 ),
    inference(avatar_split_clause,[],[f2277,f2161,f2364])).

fof(f2364,plain,
    ( spl6_276
  <=> r1_tarski(o_0_0_xboole_0,sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_276])])).

fof(f2277,plain,
    ( r1_tarski(o_0_0_xboole_0,sK5(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl6_264 ),
    inference(unit_resulting_resolution,[],[f52,f2162,f57])).

fof(f2342,plain,
    ( ~ spl6_275
    | ~ spl6_0
    | spl6_263 ),
    inference(avatar_split_clause,[],[f2198,f2152,f71,f2340])).

fof(f2340,plain,
    ( spl6_275
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_275])])).

fof(f2152,plain,
    ( spl6_263
  <=> o_0_0_xboole_0 != k1_zfmisc_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_263])])).

fof(f2198,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_263 ),
    inference(unit_resulting_resolution,[],[f2153,f1660])).

fof(f2153,plain,
    ( o_0_0_xboole_0 != k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl6_263 ),
    inference(avatar_component_clause,[],[f2152])).

fof(f2327,plain,
    ( ~ spl6_273
    | ~ spl6_0
    | spl6_263 ),
    inference(avatar_split_clause,[],[f2196,f2152,f71,f2325])).

fof(f2196,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_263 ),
    inference(unit_resulting_resolution,[],[f2153,f1585])).

fof(f2300,plain,
    ( ~ spl6_271
    | ~ spl6_0
    | ~ spl6_264 ),
    inference(avatar_split_clause,[],[f2276,f2161,f71,f2298])).

fof(f2276,plain,
    ( ~ r1_setfam_1(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_264 ),
    inference(unit_resulting_resolution,[],[f105,f2162,f56])).

fof(f2293,plain,
    ( ~ spl6_269
    | ~ spl6_0
    | spl6_263 ),
    inference(avatar_split_clause,[],[f2197,f2152,f71,f2291])).

fof(f2291,plain,
    ( spl6_269
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_269])])).

fof(f2197,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_263 ),
    inference(unit_resulting_resolution,[],[f2153,f1658])).

fof(f1658,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_0 ),
    inference(resolution,[],[f1585,f61])).

fof(f2260,plain,
    ( ~ spl6_267
    | ~ spl6_0
    | spl6_263 ),
    inference(avatar_split_clause,[],[f2219,f2152,f71,f2258])).

fof(f2258,plain,
    ( spl6_267
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_267])])).

fof(f2219,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_263 ),
    inference(unit_resulting_resolution,[],[f72,f2153,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t8_boole)).

fof(f2163,plain,
    ( spl6_262
    | spl6_264
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f312,f296,f71,f2161,f2155])).

fof(f296,plain,
    ( spl6_36
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f312,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | o_0_0_xboole_0 = k1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(resolution,[],[f114,f297])).

fof(f297,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f296])).

fof(f2080,plain,
    ( spl6_260
    | ~ spl6_144 ),
    inference(avatar_split_clause,[],[f1073,f1065,f2078])).

fof(f2078,plain,
    ( spl6_260
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK5(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).

fof(f1065,plain,
    ( spl6_144
  <=> r1_tarski(sK3(sK0),sK5(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f1073,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK5(sK0,sK3(sK0))))
    | ~ spl6_144 ),
    inference(unit_resulting_resolution,[],[f1066,f61])).

fof(f1066,plain,
    ( r1_tarski(sK3(sK0),sK5(sK0,sK3(sK0)))
    | ~ spl6_144 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f2073,plain,
    ( spl6_258
    | ~ spl6_142 ),
    inference(avatar_split_clause,[],[f1070,f1058,f2071])).

fof(f2071,plain,
    ( spl6_258
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK5(sK1,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_258])])).

fof(f1058,plain,
    ( spl6_142
  <=> r1_tarski(sK3(sK0),sK5(sK1,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f1070,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK5(sK1,sK3(sK0))))
    | ~ spl6_142 ),
    inference(unit_resulting_resolution,[],[f1059,f61])).

fof(f1059,plain,
    ( r1_tarski(sK3(sK0),sK5(sK1,sK3(sK0)))
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f2066,plain,
    ( spl6_256
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f584,f391,f2064])).

fof(f391,plain,
    ( spl6_50
  <=> r2_hidden(sK5(sK0,sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f584,plain,
    ( r2_hidden(sK5(sK0,sK5(sK0,sK3(sK0))),sK0)
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f52,f392,f56])).

fof(f392,plain,
    ( r2_hidden(sK5(sK0,sK3(sK0)),sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f391])).

fof(f2059,plain,
    ( spl6_254
    | ~ spl6_2
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f583,f391,f78,f2057])).

fof(f583,plain,
    ( r2_hidden(sK5(sK1,sK5(sK0,sK3(sK0))),sK1)
    | ~ spl6_2
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f79,f392,f56])).

fof(f1948,plain,
    ( spl6_252
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f398,f384,f1946])).

fof(f384,plain,
    ( spl6_48
  <=> r2_hidden(sK5(sK1,sK3(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f398,plain,
    ( r2_hidden(sK5(sK1,sK5(sK1,sK3(sK0))),sK1)
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f52,f385,f56])).

fof(f385,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0)),sK1)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1941,plain,
    ( spl6_250
    | ~ spl6_4
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f397,f384,f85,f1939])).

fof(f397,plain,
    ( r2_hidden(sK5(sK2,sK5(sK1,sK3(sK0))),sK2)
    | ~ spl6_4
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f86,f385,f56])).

fof(f1934,plain,
    ( ~ spl6_249
    | spl6_17 ),
    inference(avatar_split_clause,[],[f1126,f155,f1932])).

fof(f1932,plain,
    ( spl6_249
  <=> ~ r2_hidden(sK0,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_249])])).

fof(f155,plain,
    ( spl6_17
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1126,plain,
    ( ~ r2_hidden(sK0,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f562,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl6_17 ),
    inference(resolution,[],[f65,f156])).

fof(f156,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1909,plain,
    ( ~ spl6_247
    | spl6_233 ),
    inference(avatar_split_clause,[],[f1809,f1806,f1907])).

fof(f1907,plain,
    ( spl6_247
  <=> ~ r1_tarski(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK3(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).

fof(f1806,plain,
    ( spl6_233
  <=> ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_233])])).

fof(f1809,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK3(sK2)))))
    | ~ spl6_233 ),
    inference(unit_resulting_resolution,[],[f108,f1807,f64])).

fof(f1807,plain,
    ( ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK2)))
    | ~ spl6_233 ),
    inference(avatar_component_clause,[],[f1806])).

fof(f1873,plain,
    ( ~ spl6_245
    | spl6_225 ),
    inference(avatar_split_clause,[],[f1780,f1759,f1871])).

fof(f1871,plain,
    ( spl6_245
  <=> ~ r2_hidden(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_245])])).

fof(f1759,plain,
    ( spl6_225
  <=> ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_225])])).

fof(f1780,plain,
    ( ~ r2_hidden(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK2)))
    | ~ spl6_225 ),
    inference(unit_resulting_resolution,[],[f1760,f54])).

fof(f1760,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK2)))
    | ~ spl6_225 ),
    inference(avatar_component_clause,[],[f1759])).

fof(f1855,plain,
    ( spl6_242
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f736,f666,f1853])).

fof(f1853,plain,
    ( spl6_242
  <=> r1_tarski(sK3(k1_zfmisc_1(sK4(sK0,sK2))),sK5(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_242])])).

fof(f736,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK4(sK0,sK2))),sK5(sK0,sK4(sK0,sK2)))
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f108,f667,f64])).

fof(f1848,plain,
    ( ~ spl6_241
    | spl6_203 ),
    inference(avatar_split_clause,[],[f1577,f1573,f1846])).

fof(f1846,plain,
    ( spl6_241
  <=> ~ r1_tarski(sK0,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_241])])).

fof(f1573,plain,
    ( spl6_203
  <=> ~ r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_203])])).

fof(f1577,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))))
    | ~ spl6_203 ),
    inference(unit_resulting_resolution,[],[f118,f1574,f64])).

fof(f1574,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl6_203 ),
    inference(avatar_component_clause,[],[f1573])).

fof(f1841,plain,
    ( ~ spl6_239
    | spl6_189 ),
    inference(avatar_split_clause,[],[f1402,f1398,f1839])).

fof(f1839,plain,
    ( spl6_239
  <=> ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_239])])).

fof(f1398,plain,
    ( spl6_189
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_189])])).

fof(f1402,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))))
    | ~ spl6_189 ),
    inference(unit_resulting_resolution,[],[f118,f1399,f64])).

fof(f1399,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_189 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1828,plain,
    ( spl6_236
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f707,f638,f1826])).

fof(f1826,plain,
    ( spl6_236
  <=> r1_tarski(sK3(k1_zfmisc_1(sK4(sK0,sK2))),sK5(sK1,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_236])])).

fof(f707,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK4(sK0,sK2))),sK5(sK1,sK4(sK0,sK2)))
    | ~ spl6_82 ),
    inference(unit_resulting_resolution,[],[f108,f639,f64])).

fof(f1821,plain,
    ( ~ spl6_235
    | spl6_231 ),
    inference(avatar_split_clause,[],[f1798,f1792,f1819])).

fof(f1819,plain,
    ( spl6_235
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_235])])).

fof(f1792,plain,
    ( spl6_231
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_231])])).

fof(f1798,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK2))))
    | ~ spl6_231 ),
    inference(unit_resulting_resolution,[],[f1793,f54])).

fof(f1793,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK2))))
    | ~ spl6_231 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f1808,plain,
    ( ~ spl6_233
    | spl6_231 ),
    inference(avatar_split_clause,[],[f1795,f1792,f1806])).

fof(f1795,plain,
    ( ~ r1_tarski(sK0,k1_zfmisc_1(sK3(sK2)))
    | ~ spl6_231 ),
    inference(unit_resulting_resolution,[],[f1793,f61])).

fof(f1794,plain,
    ( ~ spl6_231
    | ~ spl6_10
    | spl6_225 ),
    inference(avatar_split_clause,[],[f1777,f1759,f123,f1792])).

fof(f1777,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(sK3(sK2))))
    | ~ spl6_10
    | ~ spl6_225 ),
    inference(unit_resulting_resolution,[],[f124,f1760,f65])).

fof(f1775,plain,
    ( spl6_228
    | ~ spl6_220 ),
    inference(avatar_split_clause,[],[f1718,f1702,f1773])).

fof(f1773,plain,
    ( spl6_228
  <=> m1_subset_1(sK5(sK2,sK4(sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_228])])).

fof(f1702,plain,
    ( spl6_220
  <=> r2_hidden(sK5(sK2,sK4(sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_220])])).

fof(f1718,plain,
    ( m1_subset_1(sK5(sK2,sK4(sK2,o_0_0_xboole_0)),sK2)
    | ~ spl6_220 ),
    inference(unit_resulting_resolution,[],[f1703,f54])).

fof(f1703,plain,
    ( r2_hidden(sK5(sK2,sK4(sK2,o_0_0_xboole_0)),sK2)
    | ~ spl6_220 ),
    inference(avatar_component_clause,[],[f1702])).

fof(f1768,plain,
    ( ~ spl6_227
    | ~ spl6_220 ),
    inference(avatar_split_clause,[],[f1717,f1702,f1766])).

fof(f1766,plain,
    ( spl6_227
  <=> ~ r2_hidden(sK2,sK5(sK2,sK4(sK2,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_227])])).

fof(f1717,plain,
    ( ~ r2_hidden(sK2,sK5(sK2,sK4(sK2,o_0_0_xboole_0)))
    | ~ spl6_220 ),
    inference(unit_resulting_resolution,[],[f1703,f53])).

fof(f1761,plain,
    ( ~ spl6_225
    | spl6_127 ),
    inference(avatar_split_clause,[],[f982,f961,f1759])).

fof(f961,plain,
    ( spl6_127
  <=> ~ r1_tarski(sK4(sK0,sK2),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f982,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK3(sK2)))
    | ~ spl6_127 ),
    inference(unit_resulting_resolution,[],[f962,f60])).

fof(f962,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK3(sK2))
    | ~ spl6_127 ),
    inference(avatar_component_clause,[],[f961])).

fof(f1711,plain,
    ( ~ spl6_223
    | spl6_7
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f816,f806,f92,f1709])).

fof(f1709,plain,
    ( spl6_223
  <=> ~ r1_tarski(sK4(sK0,sK2),sK4(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_223])])).

fof(f806,plain,
    ( spl6_106
  <=> r2_hidden(sK4(sK2,o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f816,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK4(sK2,o_0_0_xboole_0))
    | ~ spl6_7
    | ~ spl6_106 ),
    inference(unit_resulting_resolution,[],[f93,f807,f59])).

fof(f807,plain,
    ( r2_hidden(sK4(sK2,o_0_0_xboole_0),sK2)
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f806])).

fof(f1704,plain,
    ( spl6_220
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f813,f806,f1702])).

fof(f813,plain,
    ( r2_hidden(sK5(sK2,sK4(sK2,o_0_0_xboole_0)),sK2)
    | ~ spl6_106 ),
    inference(unit_resulting_resolution,[],[f52,f807,f56])).

fof(f1697,plain,
    ( spl6_218
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f738,f666,f1695])).

fof(f1695,plain,
    ( spl6_218
  <=> m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK5(sK0,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_218])])).

fof(f738,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK5(sK0,sK4(sK0,sK2))))
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f667,f61])).

fof(f1690,plain,
    ( spl6_216
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f786,f765,f1688])).

fof(f1688,plain,
    ( spl6_216
  <=> r1_tarski(sK3(sK2),sK5(sK2,sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_216])])).

fof(f765,plain,
    ( spl6_100
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f786,plain,
    ( r1_tarski(sK3(sK2),sK5(sK2,sK3(sK2)))
    | ~ spl6_100 ),
    inference(unit_resulting_resolution,[],[f52,f766,f57])).

fof(f766,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f765])).

fof(f1653,plain,
    ( spl6_214
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f709,f638,f1651])).

fof(f1651,plain,
    ( spl6_214
  <=> m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK5(sK1,sK4(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_214])])).

fof(f709,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(sK5(sK1,sK4(sK0,sK2))))
    | ~ spl6_82 ),
    inference(unit_resulting_resolution,[],[f639,f61])).

fof(f1646,plain,
    ( ~ spl6_213
    | spl6_211 ),
    inference(avatar_split_clause,[],[f1636,f1630,f1644])).

fof(f1644,plain,
    ( spl6_213
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_213])])).

fof(f1630,plain,
    ( spl6_211
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_211])])).

fof(f1636,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_211 ),
    inference(unit_resulting_resolution,[],[f1631,f54])).

fof(f1631,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_211 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1632,plain,
    ( ~ spl6_211
    | spl6_207 ),
    inference(avatar_split_clause,[],[f1606,f1600,f1630])).

fof(f1600,plain,
    ( spl6_207
  <=> ~ r1_tarski(sK0,sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_207])])).

fof(f1606,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_207 ),
    inference(unit_resulting_resolution,[],[f1601,f60])).

fof(f1601,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_207 ),
    inference(avatar_component_clause,[],[f1600])).

fof(f1615,plain,
    ( ~ spl6_209
    | spl6_201 ),
    inference(avatar_split_clause,[],[f1564,f1559,f1613])).

fof(f1613,plain,
    ( spl6_209
  <=> ~ r2_hidden(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_209])])).

fof(f1559,plain,
    ( spl6_201
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_201])])).

fof(f1564,plain,
    ( ~ r2_hidden(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl6_201 ),
    inference(unit_resulting_resolution,[],[f51,f1560,f65])).

fof(f1560,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | ~ spl6_201 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f1602,plain,
    ( ~ spl6_207
    | spl6_203 ),
    inference(avatar_split_clause,[],[f1576,f1573,f1600])).

fof(f1576,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_203 ),
    inference(unit_resulting_resolution,[],[f108,f1574,f64])).

fof(f1594,plain,
    ( ~ spl6_205
    | spl6_201 ),
    inference(avatar_split_clause,[],[f1565,f1559,f1592])).

fof(f1592,plain,
    ( spl6_205
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_205])])).

fof(f1565,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK2))
    | ~ spl6_201 ),
    inference(unit_resulting_resolution,[],[f1560,f54])).

fof(f1575,plain,
    ( ~ spl6_203
    | spl6_201 ),
    inference(avatar_split_clause,[],[f1562,f1559,f1573])).

fof(f1562,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl6_201 ),
    inference(unit_resulting_resolution,[],[f1560,f61])).

fof(f1561,plain,
    ( ~ spl6_201
    | ~ spl6_54
    | spl6_185 ),
    inference(avatar_split_clause,[],[f1551,f1349,f422,f1559])).

fof(f1349,plain,
    ( spl6_185
  <=> ~ m1_subset_1(sK5(sK0,sK4(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).

fof(f1551,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | ~ spl6_54
    | ~ spl6_185 ),
    inference(unit_resulting_resolution,[],[f423,f1350,f65])).

fof(f1350,plain,
    ( ~ m1_subset_1(sK5(sK0,sK4(sK0,sK2)),sK2)
    | ~ spl6_185 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1488,plain,
    ( ~ spl6_199
    | spl6_197 ),
    inference(avatar_split_clause,[],[f1478,f1472,f1486])).

fof(f1486,plain,
    ( spl6_199
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_199])])).

fof(f1472,plain,
    ( spl6_197
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_197])])).

fof(f1478,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_197 ),
    inference(unit_resulting_resolution,[],[f1473,f54])).

fof(f1473,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_197 ),
    inference(avatar_component_clause,[],[f1472])).

fof(f1474,plain,
    ( ~ spl6_197
    | spl6_193 ),
    inference(avatar_split_clause,[],[f1438,f1433,f1472])).

fof(f1433,plain,
    ( spl6_193
  <=> ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_193])])).

fof(f1438,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_193 ),
    inference(unit_resulting_resolution,[],[f1434,f60])).

fof(f1434,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_193 ),
    inference(avatar_component_clause,[],[f1433])).

fof(f1447,plain,
    ( ~ spl6_195
    | spl6_187 ),
    inference(avatar_split_clause,[],[f1389,f1384,f1445])).

fof(f1445,plain,
    ( spl6_195
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f1384,plain,
    ( spl6_187
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_187])])).

fof(f1389,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl6_187 ),
    inference(unit_resulting_resolution,[],[f51,f1385,f65])).

fof(f1385,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_187 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1435,plain,
    ( ~ spl6_193
    | spl6_189 ),
    inference(avatar_split_clause,[],[f1401,f1398,f1433])).

fof(f1401,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_189 ),
    inference(unit_resulting_resolution,[],[f108,f1399,f64])).

fof(f1412,plain,
    ( ~ spl6_191
    | spl6_187 ),
    inference(avatar_split_clause,[],[f1390,f1384,f1410])).

fof(f1410,plain,
    ( spl6_191
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_191])])).

fof(f1390,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_187 ),
    inference(unit_resulting_resolution,[],[f1385,f54])).

fof(f1400,plain,
    ( ~ spl6_189
    | spl6_187 ),
    inference(avatar_split_clause,[],[f1387,f1384,f1398])).

fof(f1387,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_187 ),
    inference(unit_resulting_resolution,[],[f1385,f61])).

fof(f1386,plain,
    ( ~ spl6_187
    | ~ spl6_46
    | spl6_183 ),
    inference(avatar_split_clause,[],[f1361,f1342,f377,f1384])).

fof(f1342,plain,
    ( spl6_183
  <=> ~ m1_subset_1(sK5(sK1,sK4(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).

fof(f1361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_46
    | ~ spl6_183 ),
    inference(unit_resulting_resolution,[],[f378,f1343,f65])).

fof(f1343,plain,
    ( ~ m1_subset_1(sK5(sK1,sK4(sK0,sK2)),sK2)
    | ~ spl6_183 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1351,plain,
    ( ~ spl6_185
    | spl6_93
    | spl6_141 ),
    inference(avatar_split_clause,[],[f1052,f1036,f714,f1349])).

fof(f714,plain,
    ( spl6_93
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f1036,plain,
    ( spl6_141
  <=> ~ r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f1052,plain,
    ( ~ m1_subset_1(sK5(sK0,sK4(sK0,sK2)),sK2)
    | ~ spl6_93
    | ~ spl6_141 ),
    inference(unit_resulting_resolution,[],[f715,f1037,f55])).

fof(f1037,plain,
    ( ~ r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK2)
    | ~ spl6_141 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f715,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f714])).

fof(f1344,plain,
    ( ~ spl6_183
    | spl6_93
    | spl6_139 ),
    inference(avatar_split_clause,[],[f1050,f1029,f714,f1342])).

fof(f1029,plain,
    ( spl6_139
  <=> ~ r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f1050,plain,
    ( ~ m1_subset_1(sK5(sK1,sK4(sK0,sK2)),sK2)
    | ~ spl6_93
    | ~ spl6_139 ),
    inference(unit_resulting_resolution,[],[f715,f1030,f55])).

fof(f1030,plain,
    ( ~ r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK2)
    | ~ spl6_139 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f1313,plain,
    ( spl6_180
    | ~ spl6_156 ),
    inference(avatar_split_clause,[],[f1240,f1173,f1311])).

fof(f1311,plain,
    ( spl6_180
  <=> m1_subset_1(sK5(sK1,sK4(sK1,o_0_0_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f1173,plain,
    ( spl6_156
  <=> r2_hidden(sK5(sK1,sK4(sK1,o_0_0_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f1240,plain,
    ( m1_subset_1(sK5(sK1,sK4(sK1,o_0_0_xboole_0)),sK1)
    | ~ spl6_156 ),
    inference(unit_resulting_resolution,[],[f1174,f54])).

fof(f1174,plain,
    ( r2_hidden(sK5(sK1,sK4(sK1,o_0_0_xboole_0)),sK1)
    | ~ spl6_156 ),
    inference(avatar_component_clause,[],[f1173])).

fof(f1306,plain,
    ( ~ spl6_179
    | ~ spl6_156 ),
    inference(avatar_split_clause,[],[f1239,f1173,f1304])).

fof(f1304,plain,
    ( spl6_179
  <=> ~ r2_hidden(sK1,sK5(sK1,sK4(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f1239,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK4(sK1,o_0_0_xboole_0)))
    | ~ spl6_156 ),
    inference(unit_resulting_resolution,[],[f1174,f53])).

fof(f1299,plain,
    ( spl6_176
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f508,f422,f1297])).

fof(f1297,plain,
    ( spl6_176
  <=> r2_hidden(sK5(sK0,sK5(sK0,sK4(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f508,plain,
    ( r2_hidden(sK5(sK0,sK5(sK0,sK4(sK0,sK2))),sK0)
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f52,f423,f56])).

fof(f1292,plain,
    ( spl6_174
    | ~ spl6_154 ),
    inference(avatar_split_clause,[],[f1226,f1166,f1290])).

fof(f1290,plain,
    ( spl6_174
  <=> m1_subset_1(sK5(sK2,sK4(sK1,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_174])])).

fof(f1166,plain,
    ( spl6_154
  <=> r2_hidden(sK5(sK2,sK4(sK1,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).

fof(f1226,plain,
    ( m1_subset_1(sK5(sK2,sK4(sK1,o_0_0_xboole_0)),sK2)
    | ~ spl6_154 ),
    inference(unit_resulting_resolution,[],[f1167,f54])).

fof(f1167,plain,
    ( r2_hidden(sK5(sK2,sK4(sK1,o_0_0_xboole_0)),sK2)
    | ~ spl6_154 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1285,plain,
    ( ~ spl6_173
    | ~ spl6_154 ),
    inference(avatar_split_clause,[],[f1225,f1166,f1283])).

fof(f1283,plain,
    ( spl6_173
  <=> ~ r2_hidden(sK2,sK5(sK2,sK4(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).

fof(f1225,plain,
    ( ~ r2_hidden(sK2,sK5(sK2,sK4(sK1,o_0_0_xboole_0)))
    | ~ spl6_154 ),
    inference(unit_resulting_resolution,[],[f1167,f53])).

fof(f1264,plain,
    ( spl6_170
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f507,f422,f78,f1262])).

fof(f1262,plain,
    ( spl6_170
  <=> r2_hidden(sK5(sK1,sK5(sK0,sK4(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f507,plain,
    ( r2_hidden(sK5(sK1,sK5(sK0,sK4(sK0,sK2))),sK1)
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f79,f423,f56])).

fof(f1220,plain,
    ( spl6_168
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f458,f377,f1218])).

fof(f1218,plain,
    ( spl6_168
  <=> r2_hidden(sK5(sK1,sK5(sK1,sK4(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_168])])).

fof(f458,plain,
    ( r2_hidden(sK5(sK1,sK5(sK1,sK4(sK0,sK2))),sK1)
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f52,f378,f56])).

fof(f1210,plain,
    ( spl6_166
    | ~ spl6_148 ),
    inference(avatar_split_clause,[],[f1135,f1096,f1208])).

fof(f1208,plain,
    ( spl6_166
  <=> m1_subset_1(sK5(sK0,sK4(sK0,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f1096,plain,
    ( spl6_148
  <=> r2_hidden(sK5(sK0,sK4(sK0,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f1135,plain,
    ( m1_subset_1(sK5(sK0,sK4(sK0,o_0_0_xboole_0)),sK0)
    | ~ spl6_148 ),
    inference(unit_resulting_resolution,[],[f1097,f54])).

fof(f1097,plain,
    ( r2_hidden(sK5(sK0,sK4(sK0,o_0_0_xboole_0)),sK0)
    | ~ spl6_148 ),
    inference(avatar_component_clause,[],[f1096])).

fof(f1203,plain,
    ( ~ spl6_165
    | ~ spl6_148 ),
    inference(avatar_split_clause,[],[f1134,f1096,f1201])).

fof(f1201,plain,
    ( spl6_165
  <=> ~ r2_hidden(sK0,sK5(sK0,sK4(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f1134,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK4(sK0,o_0_0_xboole_0)))
    | ~ spl6_148 ),
    inference(unit_resulting_resolution,[],[f1097,f53])).

fof(f1196,plain,
    ( spl6_162
    | ~ spl6_146 ),
    inference(avatar_split_clause,[],[f1108,f1089,f1194])).

fof(f1194,plain,
    ( spl6_162
  <=> m1_subset_1(sK5(sK1,sK4(sK0,o_0_0_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_162])])).

fof(f1089,plain,
    ( spl6_146
  <=> r2_hidden(sK5(sK1,sK4(sK0,o_0_0_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).

fof(f1108,plain,
    ( m1_subset_1(sK5(sK1,sK4(sK0,o_0_0_xboole_0)),sK1)
    | ~ spl6_146 ),
    inference(unit_resulting_resolution,[],[f1090,f54])).

fof(f1090,plain,
    ( r2_hidden(sK5(sK1,sK4(sK0,o_0_0_xboole_0)),sK1)
    | ~ spl6_146 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1189,plain,
    ( ~ spl6_161
    | ~ spl6_146 ),
    inference(avatar_split_clause,[],[f1107,f1089,f1187])).

fof(f1187,plain,
    ( spl6_161
  <=> ~ r2_hidden(sK1,sK5(sK1,sK4(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f1107,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK4(sK0,o_0_0_xboole_0)))
    | ~ spl6_146 ),
    inference(unit_resulting_resolution,[],[f1090,f53])).

fof(f1182,plain,
    ( spl6_158
    | ~ spl6_4
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f457,f377,f85,f1180])).

fof(f457,plain,
    ( r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,sK2))),sK2)
    | ~ spl6_4
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f86,f378,f56])).

fof(f1175,plain,
    ( spl6_156
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f537,f530,f1173])).

fof(f530,plain,
    ( spl6_68
  <=> r2_hidden(sK4(sK1,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f537,plain,
    ( r2_hidden(sK5(sK1,sK4(sK1,o_0_0_xboole_0)),sK1)
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f52,f531,f56])).

fof(f531,plain,
    ( r2_hidden(sK4(sK1,o_0_0_xboole_0),sK1)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f530])).

fof(f1168,plain,
    ( spl6_154
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f536,f530,f85,f1166])).

fof(f536,plain,
    ( r2_hidden(sK5(sK2,sK4(sK1,o_0_0_xboole_0)),sK2)
    | ~ spl6_4
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f86,f531,f56])).

fof(f1161,plain,
    ( spl6_152
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f496,f479,f1159])).

fof(f479,plain,
    ( spl6_62
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f496,plain,
    ( r1_tarski(sK3(sK1),sK5(sK1,sK3(sK1)))
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f52,f480,f57])).

fof(f480,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1154,plain,
    ( spl6_150
    | ~ spl6_4
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f495,f479,f85,f1152])).

fof(f495,plain,
    ( r1_tarski(sK3(sK1),sK5(sK2,sK3(sK1)))
    | ~ spl6_4
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f86,f480,f57])).

fof(f1098,plain,
    ( spl6_148
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f319,f305,f1096])).

fof(f305,plain,
    ( spl6_38
  <=> r2_hidden(sK4(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f319,plain,
    ( r2_hidden(sK5(sK0,sK4(sK0,o_0_0_xboole_0)),sK0)
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f52,f306,f56])).

fof(f306,plain,
    ( r2_hidden(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f305])).

fof(f1091,plain,
    ( spl6_146
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f318,f305,f78,f1089])).

fof(f318,plain,
    ( r2_hidden(sK5(sK1,sK4(sK0,o_0_0_xboole_0)),sK1)
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f79,f306,f56])).

fof(f1067,plain,
    ( spl6_144
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f260,f145,f1065])).

fof(f145,plain,
    ( spl6_14
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f260,plain,
    ( r1_tarski(sK3(sK0),sK5(sK0,sK3(sK0)))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f52,f146,f57])).

fof(f146,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1060,plain,
    ( spl6_142
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f259,f145,f78,f1058])).

fof(f259,plain,
    ( r1_tarski(sK3(sK0),sK5(sK1,sK3(sK0)))
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f79,f146,f57])).

fof(f1038,plain,
    ( ~ spl6_141
    | spl6_7
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f735,f666,f92,f1036])).

fof(f735,plain,
    ( ~ r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK2)
    | ~ spl6_7
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f93,f667,f59])).

fof(f1031,plain,
    ( ~ spl6_139
    | spl6_7
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f706,f638,f92,f1029])).

fof(f706,plain,
    ( ~ r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK2)
    | ~ spl6_7
    | ~ spl6_82 ),
    inference(unit_resulting_resolution,[],[f93,f639,f59])).

fof(f1024,plain,
    ( spl6_136
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f506,f422,f1022])).

fof(f1022,plain,
    ( spl6_136
  <=> m1_subset_1(sK5(sK0,sK4(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f506,plain,
    ( m1_subset_1(sK5(sK0,sK4(sK0,sK2)),sK0)
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f423,f54])).

fof(f1017,plain,
    ( ~ spl6_135
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f505,f422,f1015])).

fof(f1015,plain,
    ( spl6_135
  <=> ~ r2_hidden(sK0,sK5(sK0,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f505,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK4(sK0,sK2)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f423,f53])).

fof(f1005,plain,
    ( spl6_132
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f456,f377,f1003])).

fof(f1003,plain,
    ( spl6_132
  <=> m1_subset_1(sK5(sK1,sK4(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f456,plain,
    ( m1_subset_1(sK5(sK1,sK4(sK0,sK2)),sK1)
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f378,f54])).

fof(f998,plain,
    ( spl6_130
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f966,f947,f996])).

fof(f996,plain,
    ( spl6_130
  <=> m1_subset_1(sK5(sK2,sK3(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f947,plain,
    ( spl6_122
  <=> r2_hidden(sK5(sK2,sK3(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f966,plain,
    ( m1_subset_1(sK5(sK2,sK3(sK2)),sK2)
    | ~ spl6_122 ),
    inference(unit_resulting_resolution,[],[f948,f54])).

fof(f948,plain,
    ( r2_hidden(sK5(sK2,sK3(sK2)),sK2)
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f947])).

fof(f991,plain,
    ( ~ spl6_129
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f965,f947,f989])).

fof(f989,plain,
    ( spl6_129
  <=> ~ r2_hidden(sK2,sK5(sK2,sK3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f965,plain,
    ( ~ r2_hidden(sK2,sK5(sK2,sK3(sK2)))
    | ~ spl6_122 ),
    inference(unit_resulting_resolution,[],[f948,f53])).

fof(f963,plain,
    ( ~ spl6_127
    | spl6_7
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f787,f765,f92,f961])).

fof(f787,plain,
    ( ~ r1_tarski(sK4(sK0,sK2),sK3(sK2))
    | ~ spl6_7
    | ~ spl6_100 ),
    inference(unit_resulting_resolution,[],[f93,f766,f59])).

fof(f956,plain,
    ( ~ spl6_125
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f455,f377,f954])).

fof(f954,plain,
    ( spl6_125
  <=> ~ r2_hidden(sK1,sK5(sK1,sK4(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f455,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK4(sK0,sK2)))
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f378,f53])).

fof(f949,plain,
    ( spl6_122
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f784,f765,f947])).

fof(f784,plain,
    ( r2_hidden(sK5(sK2,sK3(sK2)),sK2)
    | ~ spl6_100 ),
    inference(unit_resulting_resolution,[],[f52,f766,f56])).

fof(f933,plain,
    ( ~ spl6_121
    | spl6_97 ),
    inference(avatar_split_clause,[],[f740,f732,f931])).

fof(f931,plain,
    ( spl6_121
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f732,plain,
    ( spl6_97
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f740,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_97 ),
    inference(unit_resulting_resolution,[],[f51,f733,f65])).

fof(f733,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f732])).

fof(f898,plain,
    ( spl6_118
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f850,f689,f896])).

fof(f896,plain,
    ( spl6_118
  <=> m1_subset_1(sK5(sK1,sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f850,plain,
    ( m1_subset_1(sK5(sK1,sK3(sK1)),sK1)
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f690,f54])).

fof(f886,plain,
    ( ~ spl6_117
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f849,f689,f884])).

fof(f884,plain,
    ( spl6_117
  <=> ~ r2_hidden(sK1,sK5(sK1,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f849,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK3(sK1)))
    | ~ spl6_90 ),
    inference(unit_resulting_resolution,[],[f690,f53])).

fof(f876,plain,
    ( spl6_114
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f694,f682,f874])).

fof(f874,plain,
    ( spl6_114
  <=> m1_subset_1(sK5(sK2,sK3(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f694,plain,
    ( m1_subset_1(sK5(sK2,sK3(sK1)),sK2)
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f683,f54])).

fof(f869,plain,
    ( ~ spl6_113
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f693,f682,f867])).

fof(f867,plain,
    ( spl6_113
  <=> ~ r2_hidden(sK2,sK5(sK2,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f693,plain,
    ( ~ r2_hidden(sK2,sK5(sK2,sK3(sK1)))
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f683,f53])).

fof(f837,plain,
    ( spl6_110
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f812,f806,f835])).

fof(f835,plain,
    ( spl6_110
  <=> m1_subset_1(sK4(sK2,o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f812,plain,
    ( m1_subset_1(sK4(sK2,o_0_0_xboole_0),sK2)
    | ~ spl6_106 ),
    inference(unit_resulting_resolution,[],[f807,f54])).

fof(f830,plain,
    ( ~ spl6_109
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f811,f806,f828])).

fof(f828,plain,
    ( spl6_109
  <=> ~ r2_hidden(sK2,sK4(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f811,plain,
    ( ~ r2_hidden(sK2,sK4(sK2,o_0_0_xboole_0))
    | ~ spl6_106 ),
    inference(unit_resulting_resolution,[],[f807,f53])).

fof(f808,plain,
    ( spl6_106
    | spl6_95 ),
    inference(avatar_split_clause,[],[f726,f723,f806])).

fof(f723,plain,
    ( spl6_95
  <=> ~ r1_setfam_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f726,plain,
    ( r2_hidden(sK4(sK2,o_0_0_xboole_0),sK2)
    | ~ spl6_95 ),
    inference(unit_resulting_resolution,[],[f724,f58])).

fof(f724,plain,
    ( ~ r1_setfam_1(sK2,o_0_0_xboole_0)
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f723])).

fof(f801,plain,
    ( ~ spl6_105
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f782,f765,f799])).

fof(f799,plain,
    ( spl6_105
  <=> ~ r2_hidden(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f782,plain,
    ( ~ r2_hidden(sK2,sK3(sK2))
    | ~ spl6_100 ),
    inference(unit_resulting_resolution,[],[f766,f53])).

fof(f774,plain,
    ( ~ spl6_103
    | spl6_97 ),
    inference(avatar_split_clause,[],[f741,f732,f772])).

fof(f772,plain,
    ( spl6_103
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f741,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_97 ),
    inference(unit_resulting_resolution,[],[f733,f54])).

fof(f767,plain,
    ( spl6_100
    | spl6_93 ),
    inference(avatar_split_clause,[],[f717,f714,f765])).

fof(f717,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl6_93 ),
    inference(unit_resulting_resolution,[],[f51,f715,f55])).

fof(f751,plain,
    ( ~ spl6_99
    | spl6_97 ),
    inference(avatar_split_clause,[],[f739,f732,f749])).

fof(f749,plain,
    ( spl6_99
  <=> ~ r1_tarski(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f739,plain,
    ( ~ r1_tarski(sK2,o_0_0_xboole_0)
    | ~ spl6_97 ),
    inference(unit_resulting_resolution,[],[f733,f61])).

fof(f734,plain,
    ( ~ spl6_97
    | ~ spl6_0
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f700,f682,f71,f732])).

fof(f700,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f72,f683,f66])).

fof(f725,plain,
    ( ~ spl6_95
    | ~ spl6_0
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f696,f682,f71,f723])).

fof(f696,plain,
    ( ~ r1_setfam_1(sK2,o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f105,f683,f56])).

fof(f716,plain,
    ( ~ spl6_93
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f699,f682,f714])).

fof(f699,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_88 ),
    inference(unit_resulting_resolution,[],[f683,f63])).

fof(f691,plain,
    ( spl6_90
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f493,f479,f689])).

fof(f493,plain,
    ( r2_hidden(sK5(sK1,sK3(sK1)),sK1)
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f52,f480,f56])).

fof(f684,plain,
    ( spl6_88
    | ~ spl6_4
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f492,f479,f85,f682])).

fof(f492,plain,
    ( r2_hidden(sK5(sK2,sK3(sK1)),sK2)
    | ~ spl6_4
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f86,f480,f56])).

fof(f668,plain,
    ( spl6_86
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f258,f123,f666])).

fof(f258,plain,
    ( r1_tarski(sK4(sK0,sK2),sK5(sK0,sK4(sK0,sK2)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f52,f124,f57])).

fof(f661,plain,
    ( ~ spl6_85
    | spl6_59 ),
    inference(avatar_split_clause,[],[f442,f438,f659])).

fof(f659,plain,
    ( spl6_85
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f442,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f51,f439,f65])).

fof(f640,plain,
    ( spl6_82
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f257,f123,f78,f638])).

fof(f257,plain,
    ( r1_tarski(sK4(sK0,sK2),sK5(sK1,sK4(sK0,sK2)))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f79,f124,f57])).

fof(f633,plain,
    ( spl6_80
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f582,f391,f631])).

fof(f631,plain,
    ( spl6_80
  <=> m1_subset_1(sK5(sK0,sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f582,plain,
    ( m1_subset_1(sK5(sK0,sK3(sK0)),sK0)
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f392,f54])).

fof(f626,plain,
    ( ~ spl6_79
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f581,f391,f624])).

fof(f624,plain,
    ( spl6_79
  <=> ~ r2_hidden(sK0,sK5(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f581,plain,
    ( ~ r2_hidden(sK0,sK5(sK0,sK3(sK0)))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f392,f53])).

fof(f616,plain,
    ( spl6_76
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f396,f384,f614])).

fof(f614,plain,
    ( spl6_76
  <=> m1_subset_1(sK5(sK1,sK3(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f396,plain,
    ( m1_subset_1(sK5(sK1,sK3(sK0)),sK1)
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f385,f54])).

fof(f601,plain,
    ( ~ spl6_75
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f395,f384,f599])).

fof(f599,plain,
    ( spl6_75
  <=> ~ r2_hidden(sK1,sK5(sK1,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f395,plain,
    ( ~ r2_hidden(sK1,sK5(sK1,sK3(sK0)))
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f385,f53])).

fof(f577,plain,
    ( spl6_72
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f535,f530,f575])).

fof(f575,plain,
    ( spl6_72
  <=> m1_subset_1(sK4(sK1,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f535,plain,
    ( m1_subset_1(sK4(sK1,o_0_0_xboole_0),sK1)
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f531,f54])).

fof(f554,plain,
    ( ~ spl6_71
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f534,f530,f552])).

fof(f552,plain,
    ( spl6_71
  <=> ~ r2_hidden(sK1,sK4(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f534,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,o_0_0_xboole_0))
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f531,f53])).

fof(f532,plain,
    ( spl6_68
    | spl6_57 ),
    inference(avatar_split_clause,[],[f432,f429,f530])).

fof(f429,plain,
    ( spl6_57
  <=> ~ r1_setfam_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f432,plain,
    ( r2_hidden(sK4(sK1,o_0_0_xboole_0),sK1)
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f430,f58])).

fof(f430,plain,
    ( ~ r1_setfam_1(sK1,o_0_0_xboole_0)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f429])).

fof(f525,plain,
    ( ~ spl6_67
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f490,f479,f523])).

fof(f523,plain,
    ( spl6_67
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f490,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f480,f53])).

fof(f488,plain,
    ( ~ spl6_65
    | spl6_59 ),
    inference(avatar_split_clause,[],[f443,f438,f486])).

fof(f486,plain,
    ( spl6_65
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f443,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f439,f54])).

fof(f481,plain,
    ( spl6_62
    | spl6_53 ),
    inference(avatar_split_clause,[],[f416,f413,f479])).

fof(f413,plain,
    ( spl6_53
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f416,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_53 ),
    inference(unit_resulting_resolution,[],[f51,f414,f55])).

fof(f414,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f413])).

fof(f453,plain,
    ( ~ spl6_61
    | spl6_59 ),
    inference(avatar_split_clause,[],[f441,f438,f451])).

fof(f451,plain,
    ( spl6_61
  <=> ~ r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f441,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f439,f61])).

fof(f440,plain,
    ( ~ spl6_59
    | ~ spl6_0
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f403,f384,f71,f438])).

fof(f403,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f72,f385,f66])).

fof(f431,plain,
    ( ~ spl6_57
    | ~ spl6_0
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f399,f384,f71,f429])).

fof(f399,plain,
    ( ~ r1_setfam_1(sK1,o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f105,f385,f56])).

fof(f424,plain,
    ( spl6_54
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f200,f123,f422])).

fof(f200,plain,
    ( r2_hidden(sK5(sK0,sK4(sK0,sK2)),sK0)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f52,f124,f56])).

fof(f415,plain,
    ( ~ spl6_53
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f402,f384,f413])).

fof(f402,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_48 ),
    inference(unit_resulting_resolution,[],[f385,f63])).

fof(f393,plain,
    ( spl6_50
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f202,f145,f391])).

fof(f202,plain,
    ( r2_hidden(sK5(sK0,sK3(sK0)),sK0)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f52,f146,f56])).

fof(f386,plain,
    ( spl6_48
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f201,f145,f78,f384])).

fof(f201,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f79,f146,f56])).

fof(f379,plain,
    ( spl6_46
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f199,f123,f78,f377])).

fof(f199,plain,
    ( r2_hidden(sK5(sK1,sK4(sK0,sK2)),sK1)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f79,f124,f56])).

fof(f366,plain,
    ( ~ spl6_45
    | spl6_17 ),
    inference(avatar_split_clause,[],[f181,f155,f364])).

fof(f364,plain,
    ( spl6_45
  <=> ~ r2_hidden(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f181,plain,
    ( ~ r2_hidden(sK0,sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f156,f51,f65])).

fof(f343,plain,
    ( spl6_42
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f317,f305,f341])).

fof(f341,plain,
    ( spl6_42
  <=> m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f317,plain,
    ( m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f306,f54])).

fof(f336,plain,
    ( ~ spl6_41
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f316,f305,f334])).

fof(f334,plain,
    ( spl6_41
  <=> ~ r2_hidden(sK0,sK4(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f316,plain,
    ( ~ r2_hidden(sK0,sK4(sK0,o_0_0_xboole_0))
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f306,f53])).

fof(f307,plain,
    ( spl6_38
    | spl6_25 ),
    inference(avatar_split_clause,[],[f220,f217,f305])).

fof(f217,plain,
    ( spl6_25
  <=> ~ r1_setfam_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f220,plain,
    ( r2_hidden(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f218,f58])).

fof(f218,plain,
    ( ~ r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f298,plain,
    ( spl6_36
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f277,f273,f296])).

fof(f273,plain,
    ( spl6_32
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f277,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_32 ),
    inference(superposition,[],[f51,f274])).

fof(f274,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f286,plain,
    ( spl6_34
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f276,f273,f284])).

fof(f284,plain,
    ( spl6_34
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f276,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_32 ),
    inference(superposition,[],[f108,f274])).

fof(f275,plain,
    ( spl6_32
    | ~ spl6_0
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f236,f226,f71,f273])).

fof(f226,plain,
    ( spl6_26
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f236,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f227,f97])).

fof(f227,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f267,plain,
    ( ~ spl6_31
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f128,f123,f265])).

fof(f265,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK0,sK4(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,sK4(sK0,sK2))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f124,f53])).

fof(f256,plain,
    ( spl6_28
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f126,f123,f254])).

fof(f254,plain,
    ( spl6_28
  <=> m1_subset_1(sK4(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f126,plain,
    ( m1_subset_1(sK4(sK0,sK2),sK0)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f124,f54])).

fof(f228,plain,
    ( spl6_26
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f197,f71,f226])).

fof(f197,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f51,f149,f55])).

fof(f149,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f72,f51,f66])).

fof(f219,plain,
    ( ~ spl6_25
    | ~ spl6_0
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f204,f145,f71,f217])).

fof(f204,plain,
    ( ~ r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl6_0
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f146,f105,f56])).

fof(f196,plain,
    ( ~ spl6_23
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f176,f145,f194])).

fof(f194,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f176,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f146,f53])).

fof(f189,plain,
    ( ~ spl6_21
    | spl6_17 ),
    inference(avatar_split_clause,[],[f159,f155,f187])).

fof(f187,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f159,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f156,f54])).

fof(f168,plain,
    ( ~ spl6_19
    | spl6_17 ),
    inference(avatar_split_clause,[],[f158,f155,f166])).

fof(f166,plain,
    ( spl6_19
  <=> ~ r1_tarski(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f158,plain,
    ( ~ r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f156,f61])).

fof(f157,plain,
    ( ~ spl6_17
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f148,f123,f71,f155])).

fof(f148,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f72,f124,f66])).

fof(f147,plain,
    ( spl6_14
    | spl6_13 ),
    inference(avatar_split_clause,[],[f139,f136,f145])).

fof(f136,plain,
    ( spl6_13
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f51,f137,f55])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( ~ spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f129,f123,f136])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f124,f63])).

fof(f125,plain,
    ( spl6_10
    | spl6_7 ),
    inference(avatar_split_clause,[],[f115,f92,f123])).

fof(f115,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f93,f58])).

fof(f104,plain,
    ( spl6_8
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f95,f71,f102])).

fof(f102,plain,
    ( spl6_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f94,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    ~ r1_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_setfam_1(sK0,sK2)
    & r1_setfam_1(sK1,sK2)
    & r1_setfam_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_setfam_1(X0,X2)
        & r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK2)
      & r1_setfam_1(sK1,sK2)
      & r1_setfam_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t23_setfam_1)).

fof(f87,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f49,f71])).

fof(f49,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
