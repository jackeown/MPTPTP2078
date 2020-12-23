%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t73_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  754 (2608 expanded)
%              Number of leaves         :  193 (1045 expanded)
%              Depth                    :   12
%              Number of atoms          : 2091 (6587 expanded)
%              Number of equality atoms :  242 ( 849 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f116,f123,f130,f137,f144,f159,f166,f177,f191,f193,f203,f215,f240,f253,f267,f272,f286,f298,f305,f316,f323,f333,f347,f361,f373,f380,f395,f399,f418,f432,f455,f462,f483,f492,f501,f522,f532,f541,f555,f568,f577,f591,f641,f648,f661,f674,f687,f701,f713,f728,f752,f764,f806,f816,f861,f865,f890,f897,f910,f917,f950,f964,f1002,f1006,f1031,f1038,f1067,f1078,f1095,f1102,f1106,f1112,f1118,f1124,f1145,f1164,f1168,f1182,f1215,f1226,f1243,f1247,f1252,f1336,f1343,f1350,f1357,f1364,f1371,f1378,f1403,f1416,f1424,f1432,f1439,f1446,f1453,f1460,f1475,f1490,f1519,f1548,f1569,f1576,f1583,f1590,f1597,f1628,f1640,f1671,f1675,f1682,f1690,f1699,f1741,f1742,f1743,f1744,f1750,f1891,f1894,f1897,f1899,f1935,f1942,f1955,f1956,f1957,f1964,f1971,f1972,f1979,f1986,f1994,f2004,f2296,f2310,f2322,f2360,f2424,f2447,f2457,f2492,f2515,f2525,f2560,f2583,f2593,f2617])).

fof(f2617,plain,
    ( ~ spl4_48
    | ~ spl4_60
    | ~ spl4_166
    | spl4_283
    | ~ spl4_312 ),
    inference(avatar_contradiction_clause,[],[f2616])).

fof(f2616,plain,
    ( $false
    | ~ spl4_48
    | ~ spl4_60
    | ~ spl4_166
    | ~ spl4_283
    | ~ spl4_312 ),
    inference(subsumption_resolution,[],[f2615,f1993])).

fof(f1993,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) != sK0
    | ~ spl4_283 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f1992,plain,
    ( spl4_283
  <=> k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_283])])).

fof(f2615,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = sK0
    | ~ spl4_48
    | ~ spl4_60
    | ~ spl4_166
    | ~ spl4_312 ),
    inference(forward_demodulation,[],[f2614,f1066])).

fof(f1066,plain,
    ( k9_relat_1(sK1,sK0) = sK0
    | ~ spl4_166 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1065,plain,
    ( spl4_166
  <=> k9_relat_1(sK1,sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f2614,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,sK0)
    | ~ spl4_48
    | ~ spl4_60
    | ~ spl4_312 ),
    inference(forward_demodulation,[],[f2613,f379])).

fof(f379,plain,
    ( k2_relat_1(sK2) = sK0
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl4_60
  <=> k2_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f2613,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl4_48
    | ~ spl4_312 ),
    inference(forward_demodulation,[],[f2595,f322])).

fof(f322,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl4_48
  <=> k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f2595,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl4_312 ),
    inference(resolution,[],[f2592,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',redefinition_k2_relset_1)).

fof(f2592,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_312 ),
    inference(avatar_component_clause,[],[f2591])).

fof(f2591,plain,
    ( spl4_312
  <=> m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_312])])).

fof(f2593,plain,
    ( spl4_312
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f2387,f1984,f128,f121,f2591])).

fof(f121,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f128,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1984,plain,
    ( spl4_280
  <=> k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).

fof(f2387,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_280 ),
    inference(forward_demodulation,[],[f2369,f1985])).

fof(f1985,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl4_280 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f2369,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f1555,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1555,plain,
    ( ! [X33,X34,X32] :
        ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | m1_subset_1(k4_relset_1(sK0,sK0,X33,X34,sK2,X32),k1_zfmisc_1(k2_zfmisc_1(sK0,X34))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f101,f129])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k4_relset_1)).

fof(f2583,plain,
    ( spl4_310
    | ~ spl4_306 ),
    inference(avatar_split_clause,[],[f2548,f2523,f2581])).

fof(f2581,plain,
    ( spl4_310
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f2523,plain,
    ( spl4_306
  <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f2548,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_306 ),
    inference(forward_demodulation,[],[f2529,f2528])).

fof(f2528,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl4_306 ),
    inference(resolution,[],[f2524,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',redefinition_k1_relset_1)).

fof(f2524,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_306 ),
    inference(avatar_component_clause,[],[f2523])).

fof(f2529,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_306 ),
    inference(resolution,[],[f2524,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k1_relset_1)).

fof(f2560,plain,
    ( spl4_308
    | ~ spl4_306 ),
    inference(avatar_split_clause,[],[f2526,f2523,f2558])).

fof(f2558,plain,
    ( spl4_308
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_308])])).

fof(f2526,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl4_306 ),
    inference(resolution,[],[f2524,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',cc1_relset_1)).

fof(f2525,plain,
    ( spl4_306
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_278 ),
    inference(avatar_split_clause,[],[f2352,f1977,f128,f121,f2523])).

fof(f1977,plain,
    ( spl4_278
  <=> k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f2352,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_278 ),
    inference(forward_demodulation,[],[f2334,f1978])).

fof(f1978,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl4_278 ),
    inference(avatar_component_clause,[],[f1977])).

fof(f2334,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f1553,f129])).

fof(f1553,plain,
    ( ! [X28,X26,X27] :
        ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | m1_subset_1(k4_relset_1(sK0,sK0,X27,X28,sK1,X26),k1_zfmisc_1(k2_zfmisc_1(sK0,X28))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f101,f122])).

fof(f2515,plain,
    ( spl4_304
    | ~ spl4_300 ),
    inference(avatar_split_clause,[],[f2480,f2455,f2513])).

fof(f2513,plain,
    ( spl4_304
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_304])])).

fof(f2455,plain,
    ( spl4_300
  <=> m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_300])])).

fof(f2480,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_300 ),
    inference(forward_demodulation,[],[f2461,f2460])).

fof(f2460,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK2)) = k1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl4_300 ),
    inference(resolution,[],[f2456,f89])).

fof(f2456,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_300 ),
    inference(avatar_component_clause,[],[f2455])).

fof(f2461,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_300 ),
    inference(resolution,[],[f2456,f90])).

fof(f2492,plain,
    ( spl4_302
    | ~ spl4_300 ),
    inference(avatar_split_clause,[],[f2458,f2455,f2490])).

fof(f2490,plain,
    ( spl4_302
  <=> v1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).

fof(f2458,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl4_300 ),
    inference(resolution,[],[f2456,f87])).

fof(f2457,plain,
    ( spl4_300
    | ~ spl4_6
    | ~ spl4_276 ),
    inference(avatar_split_clause,[],[f2388,f1969,f128,f2455])).

fof(f1969,plain,
    ( spl4_276
  <=> k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_276])])).

fof(f2388,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6
    | ~ spl4_276 ),
    inference(forward_demodulation,[],[f2370,f1970])).

fof(f1970,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl4_276 ),
    inference(avatar_component_clause,[],[f1969])).

fof(f2370,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6 ),
    inference(resolution,[],[f1555,f129])).

fof(f2447,plain,
    ( spl4_298
    | ~ spl4_294 ),
    inference(avatar_split_clause,[],[f2412,f2358,f2445])).

fof(f2445,plain,
    ( spl4_298
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK1,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_298])])).

fof(f2358,plain,
    ( spl4_294
  <=> m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_294])])).

fof(f2412,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK1,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_294 ),
    inference(forward_demodulation,[],[f2393,f2392])).

fof(f2392,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl4_294 ),
    inference(resolution,[],[f2359,f89])).

fof(f2359,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_294 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f2393,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_294 ),
    inference(resolution,[],[f2359,f90])).

fof(f2424,plain,
    ( spl4_296
    | ~ spl4_294 ),
    inference(avatar_split_clause,[],[f2390,f2358,f2422])).

fof(f2422,plain,
    ( spl4_296
  <=> v1_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_296])])).

fof(f2390,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl4_294 ),
    inference(resolution,[],[f2359,f87])).

fof(f2360,plain,
    ( spl4_294
    | ~ spl4_4
    | ~ spl4_274 ),
    inference(avatar_split_clause,[],[f2351,f1962,f121,f2358])).

fof(f1962,plain,
    ( spl4_274
  <=> k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_274])])).

fof(f2351,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_274 ),
    inference(forward_demodulation,[],[f2333,f1963])).

fof(f1963,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl4_274 ),
    inference(avatar_component_clause,[],[f1962])).

fof(f2333,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f1553,f122])).

fof(f2322,plain,
    ( spl4_292
    | ~ spl4_290 ),
    inference(avatar_split_clause,[],[f2315,f2308,f2320])).

fof(f2320,plain,
    ( spl4_292
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_292])])).

fof(f2308,plain,
    ( spl4_290
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_290])])).

fof(f2315,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_290 ),
    inference(superposition,[],[f80,f2309])).

fof(f2309,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_290 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',existence_m1_subset_1)).

fof(f2310,plain,
    ( spl4_290
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_288 ),
    inference(avatar_split_clause,[],[f2301,f2294,f201,f189,f2308])).

fof(f189,plain,
    ( spl4_20
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f201,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f2294,plain,
    ( spl4_288
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).

fof(f2301,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_288 ),
    inference(forward_demodulation,[],[f2297,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f2297,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_20
    | ~ spl4_288 ),
    inference(resolution,[],[f2295,f195])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_20 ),
    inference(resolution,[],[f190,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t8_boole)).

fof(f190,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f2295,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_288 ),
    inference(avatar_component_clause,[],[f2294])).

fof(f2296,plain,
    ( spl4_286
    | spl4_288
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f817,f808,f2294,f2288])).

fof(f2288,plain,
    ( spl4_286
  <=> ! [X0] : ~ m1_subset_1(X0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_286])])).

fof(f808,plain,
    ( spl4_138
  <=> ! [X6] : ~ r2_hidden(X6,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f817,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
        | ~ m1_subset_1(X0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl4_138 ),
    inference(resolution,[],[f809,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t2_subset)).

fof(f809,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f808])).

fof(f2004,plain,
    ( spl4_88
    | spl4_284
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f942,f128,f2002,f520])).

fof(f520,plain,
    ( spl4_88
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f2002,plain,
    ( spl4_284
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK2,X0))
        | ~ m1_subset_1(sK0,sK3(k10_relat_1(sK2,X0)))
        | v1_xboole_0(sK3(k10_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f942,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK2,X0))
        | v1_xboole_0(sK3(k10_relat_1(sK2,X0)))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK0,sK3(k10_relat_1(sK2,X0))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f937,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f148,f83])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f83,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',antisymmetry_r2_hidden)).

fof(f937,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k10_relat_1(sK2,X0)),sK0)
        | v1_xboole_0(k10_relat_1(sK2,X0)) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f934,f923])).

fof(f923,plain,
    ( ! [X19] : k8_relset_1(sK0,sK0,sK2,X19) = k10_relat_1(sK2,X19)
    | ~ spl4_6 ),
    inference(resolution,[],[f99,f129])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',redefinition_k8_relset_1)).

fof(f934,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k10_relat_1(sK2,X0)),sK0)
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X0)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f821,f923])).

fof(f821,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k8_relset_1(sK0,sK0,sK2,X0)),sK0)
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f601,f80])).

fof(f601,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k8_relset_1(sK0,sK0,sK2,X1))
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f596,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f94,f83])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t4_subset)).

fof(f596,plain,
    ( ! [X1] : m1_subset_1(k8_relset_1(sK0,sK0,sK2,X1),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f96,f129])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k8_relset_1)).

fof(f1994,plain,
    ( ~ spl4_283
    | spl4_17
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f1987,f1984,f175,f1992])).

fof(f175,plain,
    ( spl4_17
  <=> k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1987,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) != sK0
    | ~ spl4_17
    | ~ spl4_280 ),
    inference(superposition,[],[f176,f1985])).

fof(f176,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1986,plain,
    ( spl4_280
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1922,f128,f121,f1984])).

fof(f1922,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f1389,f122])).

fof(f1389,plain,
    ( ! [X30,X31,X29] :
        ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | k4_relset_1(sK0,sK0,X30,X31,sK2,X29) = k5_relat_1(sK2,X29) )
    | ~ spl4_6 ),
    inference(resolution,[],[f100,f129])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',redefinition_k4_relset_1)).

fof(f1979,plain,
    ( spl4_278
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1711,f128,f121,f1977])).

fof(f1711,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f1388,f129])).

fof(f1388,plain,
    ( ! [X28,X26,X27] :
        ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | k4_relset_1(sK0,sK0,X27,X28,sK1,X26) = k5_relat_1(sK1,X26) )
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f122])).

fof(f1972,plain,
    ( spl4_100
    | spl4_98
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(avatar_split_clause,[],[f1900,f1638,f128,f563,f566])).

fof(f566,plain,
    ( spl4_100
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f563,plain,
    ( spl4_98
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f1638,plain,
    ( spl4_260
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f1900,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(forward_demodulation,[],[f1861,f1639])).

fof(f1639,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl4_260 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f1861,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(superposition,[],[f938,f1639])).

fof(f938,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k10_relat_1(sK2,X1))
        | v1_xboole_0(k10_relat_1(sK2,X1))
        | m1_subset_1(X2,sK0) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f935,f923])).

fof(f935,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k10_relat_1(sK2,X1))
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X1))
        | m1_subset_1(X2,sK0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f601,f923])).

fof(f1971,plain,
    ( spl4_276
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1923,f128,f1969])).

fof(f1923,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f1389,f129])).

fof(f1964,plain,
    ( spl4_274
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1710,f121,f1962])).

fof(f1710,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f1388,f122])).

fof(f1957,plain,
    ( spl4_102
    | spl4_98
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(avatar_split_clause,[],[f1903,f1638,f128,f563,f575])).

fof(f575,plain,
    ( spl4_102
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f1903,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | m1_subset_1(sK3(k1_relat_1(sK2)),sK0)
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(forward_demodulation,[],[f1862,f1639])).

fof(f1862,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK0)
    | v1_xboole_0(k10_relat_1(sK2,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_260 ),
    inference(superposition,[],[f937,f1639])).

fof(f1956,plain,
    ( ~ spl4_233
    | spl4_98
    | spl4_211
    | ~ spl4_224 ),
    inference(avatar_split_clause,[],[f1901,f1401,f1334,f563,f1437])).

fof(f1437,plain,
    ( spl4_233
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_233])])).

fof(f1334,plain,
    ( spl4_211
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_211])])).

fof(f1401,plain,
    ( spl4_224
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f1901,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2))
    | ~ spl4_211
    | ~ spl4_224 ),
    inference(subsumption_resolution,[],[f1407,f1335])).

fof(f1335,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_211 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1407,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2))
    | ~ spl4_224 ),
    inference(resolution,[],[f1402,f168])).

fof(f1402,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_224 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1955,plain,
    ( spl4_272
    | spl4_98
    | ~ spl4_0
    | ~ spl4_224 ),
    inference(avatar_split_clause,[],[f1409,f1401,f107,f563,f1953])).

fof(f1953,plain,
    ( spl4_272
  <=> ! [X0] : ~ m1_subset_1(X0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_272])])).

fof(f107,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f1409,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl4_0
    | ~ spl4_224 ),
    inference(resolution,[],[f1405,f83])).

fof(f1405,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK2))
    | ~ spl4_0
    | ~ spl4_224 ),
    inference(resolution,[],[f1402,f167])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f95,f108])).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f107])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t5_subset)).

fof(f1942,plain,
    ( ~ spl4_271
    | ~ spl4_104
    | spl4_115 ),
    inference(avatar_split_clause,[],[f1908,f666,f589,f1940])).

fof(f1940,plain,
    ( spl4_271
  <=> ~ m1_subset_1(sK0,sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_271])])).

fof(f589,plain,
    ( spl4_104
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f666,plain,
    ( spl4_115
  <=> ~ m1_subset_1(sK0,sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f1908,plain,
    ( ~ m1_subset_1(sK0,sK3(k1_xboole_0))
    | ~ spl4_104
    | ~ spl4_115 ),
    inference(superposition,[],[f667,f590])).

fof(f590,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f589])).

fof(f667,plain,
    ( ~ m1_subset_1(sK0,sK3(k1_relat_1(sK2)))
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f666])).

fof(f1935,plain,
    ( ~ spl4_269
    | ~ spl4_104
    | spl4_109 ),
    inference(avatar_split_clause,[],[f1907,f646,f589,f1933])).

fof(f1933,plain,
    ( spl4_269
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_269])])).

fof(f646,plain,
    ( spl4_109
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f1907,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_xboole_0)
    | ~ spl4_104
    | ~ spl4_109 ),
    inference(superposition,[],[f647,f590])).

fof(f647,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2))
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f646])).

fof(f1899,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_99
    | spl4_127
    | ~ spl4_224 ),
    inference(avatar_contradiction_clause,[],[f1898])).

fof(f1898,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_99
    | ~ spl4_127
    | ~ spl4_224 ),
    inference(subsumption_resolution,[],[f1896,f718])).

fof(f718,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl4_127
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f1896,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_99
    | ~ spl4_224 ),
    inference(resolution,[],[f1408,f433])).

fof(f433,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f259,f80])).

fof(f259,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,sK3(k1_zfmisc_1(X4)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X4)))
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f178,f80])).

fof(f1408,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_relat_1(sK2))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_99
    | ~ spl4_224 ),
    inference(subsumption_resolution,[],[f1404,f561])).

fof(f561,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl4_99
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f1404,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_224 ),
    inference(resolution,[],[f1402,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_20
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f220,f202])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_20 ),
    inference(resolution,[],[f194,f83])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl4_20 ),
    inference(resolution,[],[f190,f95])).

fof(f1897,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_99
    | ~ spl4_224 ),
    inference(avatar_contradiction_clause,[],[f1895])).

fof(f1895,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_99
    | ~ spl4_224 ),
    inference(resolution,[],[f1408,f80])).

fof(f1894,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_91
    | ~ spl4_222 ),
    inference(avatar_contradiction_clause,[],[f1892])).

fof(f1892,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_91
    | ~ spl4_222 ),
    inference(resolution,[],[f1383,f80])).

fof(f1383,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_relat_1(sK1))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_91
    | ~ spl4_222 ),
    inference(subsumption_resolution,[],[f1379,f525])).

fof(f525,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl4_91
  <=> ~ v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1379,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_222 ),
    inference(resolution,[],[f1377,f221])).

fof(f1377,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_222 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl4_222
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f1891,plain,
    ( spl4_266
    | spl4_88
    | ~ spl4_0
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f1705,f1697,f107,f520,f1889])).

fof(f1889,plain,
    ( spl4_266
  <=> ! [X0] : ~ m1_subset_1(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f1697,plain,
    ( spl4_264
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_264])])).

fof(f1705,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_0
    | ~ spl4_264 ),
    inference(resolution,[],[f1701,f83])).

fof(f1701,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl4_0
    | ~ spl4_264 ),
    inference(resolution,[],[f1698,f167])).

fof(f1698,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_264 ),
    inference(avatar_component_clause,[],[f1697])).

fof(f1750,plain,
    ( spl4_196
    | ~ spl4_60
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(avatar_split_clause,[],[f1649,f1567,f1517,f378,f1180])).

fof(f1180,plain,
    ( spl4_196
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f1517,plain,
    ( spl4_244
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_244])])).

fof(f1567,plain,
    ( spl4_248
  <=> k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_248])])).

fof(f1649,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_60
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(forward_demodulation,[],[f1534,f1568])).

fof(f1568,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | ~ spl4_248 ),
    inference(avatar_component_clause,[],[f1567])).

fof(f1534,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = sK0
    | ~ spl4_60
    | ~ spl4_244 ),
    inference(forward_demodulation,[],[f1521,f379])).

fof(f1521,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k2_relat_1(sK2)
    | ~ spl4_244 ),
    inference(resolution,[],[f1518,f88])).

fof(f1518,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_244 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1744,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_89
    | ~ spl4_94
    | ~ spl4_264 ),
    inference(avatar_contradiction_clause,[],[f1732])).

fof(f1732,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_94
    | ~ spl4_264 ),
    inference(resolution,[],[f1704,f540])).

fof(f540,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK1)),sK0)
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl4_94
  <=> m1_subset_1(sK3(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1704,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK0)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_264 ),
    inference(subsumption_resolution,[],[f1700,f518])).

fof(f518,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl4_89
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1700,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_264 ),
    inference(resolution,[],[f1698,f221])).

fof(f1743,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_89
    | ~ spl4_102
    | ~ spl4_264 ),
    inference(avatar_contradiction_clause,[],[f1733])).

fof(f1733,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_102
    | ~ spl4_264 ),
    inference(resolution,[],[f1704,f576])).

fof(f576,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK0)
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1742,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_89
    | ~ spl4_128
    | ~ spl4_264 ),
    inference(avatar_contradiction_clause,[],[f1738])).

fof(f1738,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_128
    | ~ spl4_264 ),
    inference(resolution,[],[f1704,f727])).

fof(f727,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2)))),sK0)
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl4_128
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1741,plain,
    ( ~ spl4_20
    | ~ spl4_22
    | spl4_89
    | ~ spl4_264 ),
    inference(avatar_contradiction_clause,[],[f1739])).

fof(f1739,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_264 ),
    inference(resolution,[],[f1704,f80])).

fof(f1699,plain,
    ( spl4_264
    | ~ spl4_60
    | ~ spl4_244 ),
    inference(avatar_split_clause,[],[f1683,f1517,f378,f1697])).

fof(f1683,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_60
    | ~ spl4_244 ),
    inference(forward_demodulation,[],[f1524,f1534])).

fof(f1524,plain,
    ( m1_subset_1(k2_relset_1(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_244 ),
    inference(resolution,[],[f1518,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k2_relset_1)).

fof(f1690,plain,
    ( spl4_262
    | ~ spl4_4
    | ~ spl4_238 ),
    inference(avatar_split_clause,[],[f1464,f1458,f121,f1688])).

fof(f1688,plain,
    ( spl4_262
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_262])])).

fof(f1458,plain,
    ( spl4_238
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_238])])).

fof(f1464,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_238 ),
    inference(superposition,[],[f840,f1459])).

fof(f1459,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl4_238 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f840,plain,
    ( ! [X3] : m1_subset_1(k9_relat_1(sK1,X3),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f738,f834])).

fof(f834,plain,
    ( ! [X18] : k7_relset_1(sK0,sK0,sK1,X18) = k9_relat_1(sK1,X18)
    | ~ spl4_4 ),
    inference(resolution,[],[f98,f122])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',redefinition_k7_relset_1)).

fof(f738,plain,
    ( ! [X8] : m1_subset_1(k7_relset_1(sK0,sK0,sK1,X8),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f122])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k7_relset_1)).

fof(f1682,plain,
    ( ~ spl4_58
    | spl4_197
    | ~ spl4_242
    | ~ spl4_246 ),
    inference(avatar_contradiction_clause,[],[f1681])).

fof(f1681,plain,
    ( $false
    | ~ spl4_58
    | ~ spl4_197
    | ~ spl4_242
    | ~ spl4_246 ),
    inference(subsumption_resolution,[],[f1680,f1178])).

fof(f1178,plain,
    ( k1_xboole_0 != sK0
    | ~ spl4_197 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1177,plain,
    ( spl4_197
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f1680,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_58
    | ~ spl4_242
    | ~ spl4_246 ),
    inference(forward_demodulation,[],[f1505,f1547])).

fof(f1547,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | ~ spl4_246 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f1546,plain,
    ( spl4_246
  <=> k2_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_246])])).

fof(f1505,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK1) = sK0
    | ~ spl4_58
    | ~ spl4_242 ),
    inference(forward_demodulation,[],[f1492,f372])).

fof(f372,plain,
    ( k2_relat_1(sK1) = sK0
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl4_58
  <=> k2_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1492,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k2_relat_1(sK1)
    | ~ spl4_242 ),
    inference(resolution,[],[f1489,f88])).

fof(f1489,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_242 ),
    inference(avatar_component_clause,[],[f1488])).

fof(f1488,plain,
    ( spl4_242
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f1675,plain,
    ( ~ spl4_0
    | ~ spl4_60
    | spl4_89
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(avatar_contradiction_clause,[],[f1674])).

fof(f1674,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_60
    | ~ spl4_89
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(subsumption_resolution,[],[f1673,f108])).

fof(f1673,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_60
    | ~ spl4_89
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(forward_demodulation,[],[f518,f1649])).

fof(f1671,plain,
    ( ~ spl4_60
    | spl4_197
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(avatar_contradiction_clause,[],[f1670])).

fof(f1670,plain,
    ( $false
    | ~ spl4_60
    | ~ spl4_197
    | ~ spl4_244
    | ~ spl4_248 ),
    inference(subsumption_resolution,[],[f1178,f1649])).

fof(f1640,plain,
    ( spl4_260
    | ~ spl4_196
    | ~ spl4_200 ),
    inference(avatar_split_clause,[],[f1316,f1224,f1180,f1638])).

fof(f1224,plain,
    ( spl4_200
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f1316,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl4_196
    | ~ spl4_200 ),
    inference(superposition,[],[f1225,f1181])).

fof(f1181,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1225,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_200 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1628,plain,
    ( spl4_258
    | ~ spl4_196
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f1315,f1213,f1180,f1626])).

fof(f1626,plain,
    ( spl4_258
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_258])])).

fof(f1213,plain,
    ( spl4_198
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f1315,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl4_196
    | ~ spl4_198 ),
    inference(superposition,[],[f1214,f1181])).

fof(f1214,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,sK0)
    | ~ spl4_198 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1597,plain,
    ( ~ spl4_257
    | spl4_73
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1266,f1180,f430,f1595])).

fof(f1595,plain,
    ( spl4_257
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_257])])).

fof(f430,plain,
    ( spl4_73
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1266,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3(sK2))
    | ~ spl4_73
    | ~ spl4_196 ),
    inference(superposition,[],[f431,f1181])).

fof(f431,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK2))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f430])).

fof(f1590,plain,
    ( ~ spl4_255
    | spl4_65
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1265,f1180,f393,f1588])).

fof(f1588,plain,
    ( spl4_255
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_255])])).

fof(f393,plain,
    ( spl4_65
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1265,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3(sK1))
    | ~ spl4_65
    | ~ spl4_196 ),
    inference(superposition,[],[f394,f1181])).

fof(f394,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK1))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f393])).

fof(f1583,plain,
    ( ~ spl4_253
    | spl4_33
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1260,f1180,f245,f1581])).

fof(f1581,plain,
    ( spl4_253
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_253])])).

fof(f245,plain,
    ( spl4_33
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1260,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2)
    | ~ spl4_33
    | ~ spl4_196 ),
    inference(superposition,[],[f246,f1181])).

fof(f246,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f245])).

fof(f1576,plain,
    ( ~ spl4_251
    | spl4_27
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1259,f1180,f226,f1574])).

fof(f1574,plain,
    ( spl4_251
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_251])])).

fof(f226,plain,
    ( spl4_27
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1259,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ spl4_27
    | ~ spl4_196 ),
    inference(superposition,[],[f227,f1181])).

fof(f227,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1569,plain,
    ( spl4_248
    | ~ spl4_10
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1257,f1180,f142,f1567])).

fof(f142,plain,
    ( spl4_10
  <=> k2_relset_1(sK0,sK0,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1257,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | ~ spl4_10
    | ~ spl4_196 ),
    inference(superposition,[],[f143,f1181])).

fof(f143,plain,
    ( k2_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1548,plain,
    ( spl4_246
    | ~ spl4_8
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1256,f1180,f135,f1546])).

fof(f135,plain,
    ( spl4_8
  <=> k2_relset_1(sK0,sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1256,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | ~ spl4_8
    | ~ spl4_196 ),
    inference(superposition,[],[f136,f1181])).

fof(f136,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1519,plain,
    ( spl4_244
    | ~ spl4_6
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1255,f1180,f128,f1517])).

fof(f1255,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_196 ),
    inference(superposition,[],[f129,f1181])).

fof(f1490,plain,
    ( spl4_242
    | ~ spl4_4
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1254,f1180,f121,f1488])).

fof(f1254,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_196 ),
    inference(superposition,[],[f122,f1181])).

fof(f1475,plain,
    ( spl4_240
    | ~ spl4_168
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1312,f1180,f1076,f1473])).

fof(f1473,plain,
    ( spl4_240
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f1076,plain,
    ( spl4_168
  <=> k9_relat_1(sK2,sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f1312,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_168
    | ~ spl4_196 ),
    inference(superposition,[],[f1077,f1181])).

fof(f1077,plain,
    ( k9_relat_1(sK2,sK0) = sK0
    | ~ spl4_168 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1460,plain,
    ( spl4_238
    | ~ spl4_166
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1311,f1180,f1065,f1458])).

fof(f1311,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl4_166
    | ~ spl4_196 ),
    inference(superposition,[],[f1066,f1181])).

fof(f1453,plain,
    ( ~ spl4_237
    | spl4_115
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1283,f1180,f666,f1451])).

fof(f1451,plain,
    ( spl4_237
  <=> ~ m1_subset_1(k1_xboole_0,sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_237])])).

fof(f1283,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK3(k1_relat_1(sK2)))
    | ~ spl4_115
    | ~ spl4_196 ),
    inference(superposition,[],[f667,f1181])).

fof(f1446,plain,
    ( ~ spl4_235
    | spl4_111
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1282,f1180,f653,f1444])).

fof(f1444,plain,
    ( spl4_235
  <=> ~ m1_subset_1(k1_xboole_0,sK3(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_235])])).

fof(f653,plain,
    ( spl4_111
  <=> ~ m1_subset_1(sK0,sK3(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).

fof(f1282,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK3(k1_relat_1(sK1)))
    | ~ spl4_111
    | ~ spl4_196 ),
    inference(superposition,[],[f654,f1181])).

fof(f654,plain,
    ( ~ m1_subset_1(sK0,sK3(k1_relat_1(sK1)))
    | ~ spl4_111 ),
    inference(avatar_component_clause,[],[f653])).

fof(f1439,plain,
    ( ~ spl4_233
    | spl4_109
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1281,f1180,f646,f1437])).

fof(f1281,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2))
    | ~ spl4_109
    | ~ spl4_196 ),
    inference(superposition,[],[f647,f1181])).

fof(f1432,plain,
    ( ~ spl4_231
    | spl4_107
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1280,f1180,f639,f1430])).

fof(f1430,plain,
    ( spl4_231
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_231])])).

fof(f639,plain,
    ( spl4_107
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f1280,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK1))
    | ~ spl4_107
    | ~ spl4_196 ),
    inference(superposition,[],[f640,f1181])).

fof(f640,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1))
    | ~ spl4_107 ),
    inference(avatar_component_clause,[],[f639])).

fof(f1424,plain,
    ( spl4_228
    | ~ spl4_102
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1275,f1180,f575,f1422])).

fof(f1422,plain,
    ( spl4_228
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f1275,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),k1_xboole_0)
    | ~ spl4_102
    | ~ spl4_196 ),
    inference(superposition,[],[f576,f1181])).

fof(f1416,plain,
    ( spl4_226
    | ~ spl4_94
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1274,f1180,f539,f1414])).

fof(f1414,plain,
    ( spl4_226
  <=> m1_subset_1(sK3(k1_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f1274,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl4_94
    | ~ spl4_196 ),
    inference(superposition,[],[f540,f1181])).

fof(f1403,plain,
    ( spl4_224
    | ~ spl4_82
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1271,f1180,f499,f1401])).

fof(f499,plain,
    ( spl4_82
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1271,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_82
    | ~ spl4_196 ),
    inference(superposition,[],[f500,f1181])).

fof(f500,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f499])).

fof(f1378,plain,
    ( spl4_222
    | ~ spl4_80
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1270,f1180,f490,f1376])).

fof(f490,plain,
    ( spl4_80
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1270,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_80
    | ~ spl4_196 ),
    inference(superposition,[],[f491,f1181])).

fof(f491,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f490])).

fof(f1371,plain,
    ( ~ spl4_221
    | spl4_57
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1264,f1180,f356,f1369])).

fof(f1369,plain,
    ( spl4_221
  <=> k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).

fof(f356,plain,
    ( spl4_57
  <=> k2_zfmisc_1(sK0,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1264,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | ~ spl4_57
    | ~ spl4_196 ),
    inference(superposition,[],[f357,f1181])).

fof(f357,plain,
    ( k2_zfmisc_1(sK0,sK0) != k1_xboole_0
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f356])).

fof(f1364,plain,
    ( ~ spl4_219
    | ~ spl4_196
    | spl4_203 ),
    inference(avatar_split_clause,[],[f1317,f1235,f1180,f1362])).

fof(f1362,plain,
    ( spl4_219
  <=> ~ m1_subset_1(k1_xboole_0,sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_219])])).

fof(f1235,plain,
    ( spl4_203
  <=> ~ m1_subset_1(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_203])])).

fof(f1317,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl4_196
    | ~ spl4_203 ),
    inference(superposition,[],[f1236,f1181])).

fof(f1236,plain,
    ( ~ m1_subset_1(sK0,sK3(sK0))
    | ~ spl4_203 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f1357,plain,
    ( ~ spl4_217
    | spl4_157
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1309,f1180,f959,f1355])).

fof(f1355,plain,
    ( spl4_217
  <=> k1_zfmisc_1(k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_217])])).

fof(f959,plain,
    ( spl4_157
  <=> k1_zfmisc_1(sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_157])])).

fof(f1309,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
    | ~ spl4_157
    | ~ spl4_196 ),
    inference(superposition,[],[f960,f1181])).

fof(f960,plain,
    ( k1_zfmisc_1(sK0) != k1_xboole_0
    | ~ spl4_157 ),
    inference(avatar_component_clause,[],[f959])).

fof(f1350,plain,
    ( ~ spl4_215
    | spl4_85
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1272,f1180,f508,f1348])).

fof(f1348,plain,
    ( spl4_215
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_215])])).

fof(f508,plain,
    ( spl4_85
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f1272,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_85
    | ~ spl4_196 ),
    inference(superposition,[],[f509,f1181])).

fof(f509,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK0)
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f508])).

fof(f1343,plain,
    ( ~ spl4_213
    | spl4_51
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1263,f1180,f325,f1341])).

fof(f1341,plain,
    ( spl4_213
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_213])])).

fof(f325,plain,
    ( spl4_51
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1263,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_51
    | ~ spl4_196 ),
    inference(superposition,[],[f326,f1181])).

fof(f326,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1336,plain,
    ( ~ spl4_211
    | spl4_87
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f1273,f1180,f511,f1334])).

fof(f511,plain,
    ( spl4_87
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1273,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_87
    | ~ spl4_196 ),
    inference(superposition,[],[f512,f1181])).

fof(f512,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f511])).

fof(f1252,plain,
    ( spl4_88
    | spl4_208
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f941,f121,f1250,f520])).

fof(f1250,plain,
    ( spl4_208
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK1,X0))
        | ~ m1_subset_1(sK0,sK3(k10_relat_1(sK1,X0)))
        | v1_xboole_0(sK3(k10_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f941,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK1,X0))
        | v1_xboole_0(sK3(k10_relat_1(sK1,X0)))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK0,sK3(k10_relat_1(sK1,X0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f930,f168])).

fof(f930,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k10_relat_1(sK1,X0)),sK0)
        | v1_xboole_0(k10_relat_1(sK1,X0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f927,f922])).

fof(f922,plain,
    ( ! [X18] : k8_relset_1(sK0,sK0,sK1,X18) = k10_relat_1(sK1,X18)
    | ~ spl4_4 ),
    inference(resolution,[],[f99,f122])).

fof(f927,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k10_relat_1(sK1,X0)),sK0)
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK1,X0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f818,f922])).

fof(f818,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k8_relset_1(sK0,sK0,sK1,X0)),sK0)
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK1,X0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f599,f80])).

fof(f599,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k8_relset_1(sK0,sK0,sK1,X1))
        | v1_xboole_0(k8_relset_1(sK0,sK0,sK1,X1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f595,f178])).

fof(f595,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(sK0,sK0,sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f122])).

fof(f1247,plain,
    ( spl4_88
    | spl4_206
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f853,f128,f1245,f520])).

fof(f1245,plain,
    ( spl4_206
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | ~ m1_subset_1(sK0,sK3(k9_relat_1(sK2,X0)))
        | v1_xboole_0(sK3(k9_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f853,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK3(k9_relat_1(sK2,X0)))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK0,sK3(k9_relat_1(sK2,X0))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f848,f168])).

fof(f848,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k9_relat_1(sK2,X0)),sK0)
        | v1_xboole_0(k9_relat_1(sK2,X0)) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f845,f835])).

fof(f835,plain,
    ( ! [X19] : k7_relset_1(sK0,sK0,sK2,X19) = k9_relat_1(sK2,X19)
    | ~ spl4_6 ),
    inference(resolution,[],[f98,f129])).

fof(f845,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k9_relat_1(sK2,X0)),sK0)
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK2,X0)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f827,f835])).

fof(f827,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k7_relset_1(sK0,sK0,sK2,X0)),sK0)
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK2,X0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f744,f80])).

fof(f744,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k7_relset_1(sK0,sK0,sK2,X1))
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK2,X1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f739,f178])).

fof(f739,plain,
    ( ! [X9] : m1_subset_1(k7_relset_1(sK0,sK0,sK2,X9),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f97,f129])).

fof(f1243,plain,
    ( ~ spl4_203
    | spl4_204
    | spl4_89
    | ~ spl4_166
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f1186,f1166,f1065,f517,f1241,f1235])).

fof(f1241,plain,
    ( spl4_204
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f1166,plain,
    ( spl4_194
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK1,X0))
        | ~ m1_subset_1(sK0,sK3(k9_relat_1(sK1,X0)))
        | v1_xboole_0(sK3(k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f1186,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ m1_subset_1(sK0,sK3(sK0))
    | ~ spl4_89
    | ~ spl4_166
    | ~ spl4_194 ),
    inference(forward_demodulation,[],[f1185,f1066])).

fof(f1185,plain,
    ( ~ m1_subset_1(sK0,sK3(sK0))
    | v1_xboole_0(sK3(k9_relat_1(sK1,sK0)))
    | ~ spl4_89
    | ~ spl4_166
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f1184,f518])).

fof(f1184,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK0))
    | v1_xboole_0(sK3(k9_relat_1(sK1,sK0)))
    | ~ spl4_166
    | ~ spl4_194 ),
    inference(forward_demodulation,[],[f1183,f1066])).

fof(f1183,plain,
    ( ~ m1_subset_1(sK0,sK3(sK0))
    | v1_xboole_0(k9_relat_1(sK1,sK0))
    | v1_xboole_0(sK3(k9_relat_1(sK1,sK0)))
    | ~ spl4_166
    | ~ spl4_194 ),
    inference(superposition,[],[f1167,f1066])).

fof(f1167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,sK3(k9_relat_1(sK1,X0)))
        | v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(sK3(k9_relat_1(sK1,X0))) )
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1226,plain,
    ( spl4_200
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f1206,f460,f128,f1224])).

fof(f460,plain,
    ( spl4_76
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1206,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f1205,f461])).

fof(f461,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1205,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1192,f923])).

fof(f1192,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k8_relset_1(sK0,sK0,sK2,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f129])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t38_relset_1)).

fof(f1215,plain,
    ( spl4_198
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f1204,f453,f121,f1213])).

fof(f453,plain,
    ( spl4_74
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1204,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f1203,f454])).

fof(f454,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f453])).

fof(f1203,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k10_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1191,f922])).

fof(f1191,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k8_relset_1(sK0,sK0,sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f122])).

fof(f1182,plain,
    ( spl4_196
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1173,f520,f201,f189,f1180])).

fof(f1173,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f1169,f202])).

fof(f1169,plain,
    ( sK0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_88 ),
    inference(resolution,[],[f521,f195])).

fof(f521,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f520])).

fof(f1168,plain,
    ( spl4_88
    | spl4_194
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f852,f121,f1166,f520])).

fof(f852,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(sK3(k9_relat_1(sK1,X0)))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK0,sK3(k9_relat_1(sK1,X0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f841,f168])).

fof(f841,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k9_relat_1(sK1,X0)),sK0)
        | v1_xboole_0(k9_relat_1(sK1,X0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f838,f834])).

fof(f838,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k9_relat_1(sK1,X0)),sK0)
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK1,X0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f824,f834])).

fof(f824,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k7_relset_1(sK0,sK0,sK1,X0)),sK0)
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK1,X0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f742,f80])).

fof(f742,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k7_relset_1(sK0,sK0,sK1,X1))
        | v1_xboole_0(k7_relset_1(sK0,sK0,sK1,X1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f738,f178])).

fof(f1164,plain,
    ( spl4_188
    | ~ spl4_191
    | spl4_192
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f442,f397,f1162,f1156,f1150])).

fof(f1150,plain,
    ( spl4_188
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f1156,plain,
    ( spl4_191
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).

fof(f1162,plain,
    ( spl4_192
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f397,plain,
    ( spl4_66
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f442,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl4_66 ),
    inference(resolution,[],[f433,f398])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f397])).

fof(f1145,plain,
    ( spl4_182
    | ~ spl4_185
    | spl4_186
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f441,f331,f1143,f1137,f1131])).

fof(f1131,plain,
    ( spl4_182
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f1137,plain,
    ( spl4_185
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_185])])).

fof(f1143,plain,
    ( spl4_186
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f331,plain,
    ( spl4_52
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f441,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK3(k1_zfmisc_1(sK1))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK1))))
    | ~ spl4_52 ),
    inference(resolution,[],[f433,f332])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f331])).

fof(f1124,plain,
    ( spl4_86
    | spl4_180
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f745,f128,f1122,f514])).

fof(f514,plain,
    ( spl4_86
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1122,plain,
    ( spl4_180
  <=> ! [X2] :
        ( v1_xboole_0(k7_relset_1(sK0,sK0,sK2,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k7_relset_1(sK0,sK0,sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f745,plain,
    ( ! [X2] :
        ( v1_xboole_0(k7_relset_1(sK0,sK0,sK2,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k7_relset_1(sK0,sK0,sK2,X2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f739,f168])).

fof(f1118,plain,
    ( spl4_86
    | spl4_178
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f743,f121,f1116,f514])).

fof(f1116,plain,
    ( spl4_178
  <=> ! [X2] :
        ( v1_xboole_0(k7_relset_1(sK0,sK0,sK1,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k7_relset_1(sK0,sK0,sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f743,plain,
    ( ! [X2] :
        ( v1_xboole_0(k7_relset_1(sK0,sK0,sK1,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k7_relset_1(sK0,sK0,sK1,X2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f738,f168])).

fof(f1112,plain,
    ( spl4_86
    | spl4_176
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f602,f128,f1110,f514])).

fof(f1110,plain,
    ( spl4_176
  <=> ! [X2] :
        ( v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k8_relset_1(sK0,sK0,sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f602,plain,
    ( ! [X2] :
        ( v1_xboole_0(k8_relset_1(sK0,sK0,sK2,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k8_relset_1(sK0,sK0,sK2,X2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f596,f168])).

fof(f1106,plain,
    ( spl4_86
    | spl4_174
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f600,f121,f1104,f514])).

fof(f1104,plain,
    ( spl4_174
  <=> ! [X2] :
        ( v1_xboole_0(k8_relset_1(sK0,sK0,sK1,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k8_relset_1(sK0,sK0,sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f600,plain,
    ( ! [X2] :
        ( v1_xboole_0(k8_relset_1(sK0,sK0,sK1,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k8_relset_1(sK0,sK0,sK1,X2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f595,f168])).

fof(f1102,plain,
    ( spl4_172
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1087,f378,f164,f157,f1100])).

fof(f1100,plain,
    ( spl4_172
  <=> k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,sK2))) = k9_relat_1(k5_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f157,plain,
    ( spl4_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f164,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1087,plain,
    ( k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,sK2))) = k9_relat_1(k5_relat_1(sK1,sK2),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(resolution,[],[f1016,f165])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1016,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,X11))) = k9_relat_1(k5_relat_1(sK1,X11),sK0) )
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f1010,f379])).

fof(f1010,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,X11))) = k9_relat_1(k5_relat_1(sK1,X11),k2_relat_1(sK2)) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(resolution,[],[f306,f158])).

fof(f158,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK2,k5_relat_1(X0,X1))) = k9_relat_1(k5_relat_1(X0,X1),k2_relat_1(sK2)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_k5_relat_1)).

fof(f262,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | k2_relat_1(k5_relat_1(sK2,X4)) = k9_relat_1(X4,k2_relat_1(sK2)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f78,f165])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t160_relat_1)).

fof(f1095,plain,
    ( spl4_170
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1086,f378,f164,f157,f1093])).

fof(f1093,plain,
    ( spl4_170
  <=> k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,sK1))) = k9_relat_1(k5_relat_1(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f1086,plain,
    ( k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK1,sK1))) = k9_relat_1(k5_relat_1(sK1,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(resolution,[],[f1016,f158])).

fof(f1078,plain,
    ( spl4_168
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1058,f142,f128,f1076])).

fof(f1058,plain,
    ( k9_relat_1(sK2,sK0) = sK0
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f1057,f143])).

fof(f1057,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1044,f835])).

fof(f1044,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f92,f129])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1067,plain,
    ( spl4_166
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f1056,f135,f121,f1065])).

fof(f1056,plain,
    ( k9_relat_1(sK1,sK0) = sK0
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f1055,f136])).

fof(f1055,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1043,f834])).

fof(f1043,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f122])).

fof(f1038,plain,
    ( spl4_164
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1022,f378,f164,f157,f1036])).

fof(f1036,plain,
    ( spl4_164
  <=> k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK1))) = k9_relat_1(k5_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f1022,plain,
    ( k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK1))) = k9_relat_1(k5_relat_1(sK2,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(resolution,[],[f1017,f158])).

fof(f1017,plain,
    ( ! [X12] :
        ( ~ v1_relat_1(X12)
        | k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,X12))) = k9_relat_1(k5_relat_1(sK2,X12),sK0) )
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f1011,f379])).

fof(f1011,plain,
    ( ! [X12] :
        ( ~ v1_relat_1(X12)
        | k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,X12))) = k9_relat_1(k5_relat_1(sK2,X12),k2_relat_1(sK2)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f306,f165])).

fof(f1031,plain,
    ( spl4_162
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1023,f378,f164,f1029])).

fof(f1029,plain,
    ( spl4_162
  <=> k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))) = k9_relat_1(k5_relat_1(sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f1023,plain,
    ( k2_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))) = k9_relat_1(k5_relat_1(sK2,sK2),sK0)
    | ~ spl4_14
    | ~ spl4_60 ),
    inference(resolution,[],[f1017,f165])).

fof(f1006,plain,
    ( spl4_86
    | spl4_160
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f940,f128,f1004,f514])).

fof(f1004,plain,
    ( spl4_160
  <=> ! [X2] :
        ( v1_xboole_0(k10_relat_1(sK2,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k10_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f940,plain,
    ( ! [X2] :
        ( v1_xboole_0(k10_relat_1(sK2,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k10_relat_1(sK2,X2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f936,f168])).

fof(f936,plain,
    ( ! [X3] : m1_subset_1(k10_relat_1(sK2,X3),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f596,f923])).

fof(f1002,plain,
    ( spl4_158
    | ~ spl4_78
    | ~ spl4_156 ),
    inference(avatar_split_clause,[],[f965,f962,f481,f1000])).

fof(f1000,plain,
    ( spl4_158
  <=> m1_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f481,plain,
    ( spl4_78
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f962,plain,
    ( spl4_156
  <=> k1_zfmisc_1(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f965,plain,
    ( m1_subset_1(sK0,k1_xboole_0)
    | ~ spl4_78
    | ~ spl4_156 ),
    inference(superposition,[],[f482,f963])).

fof(f963,plain,
    ( k1_zfmisc_1(sK0) = k1_xboole_0
    | ~ spl4_156 ),
    inference(avatar_component_clause,[],[f962])).

fof(f482,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f481])).

fof(f964,plain,
    ( spl4_156
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f955,f514,f201,f189,f962])).

fof(f955,plain,
    ( k1_zfmisc_1(sK0) = k1_xboole_0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f951,f202])).

fof(f951,plain,
    ( k1_zfmisc_1(sK0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_86 ),
    inference(resolution,[],[f515,f195])).

fof(f515,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f514])).

fof(f950,plain,
    ( spl4_86
    | spl4_154
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f933,f121,f948,f514])).

fof(f948,plain,
    ( spl4_154
  <=> ! [X2] :
        ( v1_xboole_0(k10_relat_1(sK1,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k10_relat_1(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f933,plain,
    ( ! [X2] :
        ( v1_xboole_0(k10_relat_1(sK1,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k10_relat_1(sK1,X2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f929,f168])).

fof(f929,plain,
    ( ! [X3] : m1_subset_1(k10_relat_1(sK1,X3),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f595,f922])).

fof(f917,plain,
    ( spl4_152
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f902,f371,f164,f157,f915])).

fof(f915,plain,
    ( spl4_152
  <=> k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,sK2))) = k9_relat_1(k5_relat_1(sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f902,plain,
    ( k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,sK2))) = k9_relat_1(k5_relat_1(sK2,sK2),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(resolution,[],[f876,f165])).

fof(f876,plain,
    ( ! [X12] :
        ( ~ v1_relat_1(X12)
        | k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,X12))) = k9_relat_1(k5_relat_1(sK2,X12),sK0) )
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f870,f372])).

fof(f870,plain,
    ( ! [X12] :
        ( ~ v1_relat_1(X12)
        | k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,X12))) = k9_relat_1(k5_relat_1(sK2,X12),k2_relat_1(sK1)) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(resolution,[],[f288,f165])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK1,k5_relat_1(X0,X1))) = k9_relat_1(k5_relat_1(X0,X1),k2_relat_1(sK1)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f261,f84])).

fof(f261,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k2_relat_1(k5_relat_1(sK1,X3)) = k9_relat_1(X3,k2_relat_1(sK1)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f78,f158])).

fof(f910,plain,
    ( spl4_150
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f901,f371,f164,f157,f908])).

fof(f908,plain,
    ( spl4_150
  <=> k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,sK1))) = k9_relat_1(k5_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f901,plain,
    ( k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK2,sK1))) = k9_relat_1(k5_relat_1(sK2,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(resolution,[],[f876,f158])).

fof(f897,plain,
    ( spl4_148
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f882,f371,f164,f157,f895])).

fof(f895,plain,
    ( spl4_148
  <=> k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK2))) = k9_relat_1(k5_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f882,plain,
    ( k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK2))) = k9_relat_1(k5_relat_1(sK1,sK2),sK0)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_58 ),
    inference(resolution,[],[f875,f165])).

fof(f875,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,X11))) = k9_relat_1(k5_relat_1(sK1,X11),sK0) )
    | ~ spl4_12
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f869,f372])).

fof(f869,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(X11)
        | k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,X11))) = k9_relat_1(k5_relat_1(sK1,X11),k2_relat_1(sK1)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f288,f158])).

fof(f890,plain,
    ( spl4_146
    | ~ spl4_12
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f881,f371,f157,f888])).

fof(f888,plain,
    ( spl4_146
  <=> k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK1))) = k9_relat_1(k5_relat_1(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f881,plain,
    ( k2_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK1))) = k9_relat_1(k5_relat_1(sK1,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_58 ),
    inference(resolution,[],[f875,f158])).

fof(f865,plain,
    ( spl4_86
    | spl4_144
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f851,f128,f863,f514])).

fof(f863,plain,
    ( spl4_144
  <=> ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k9_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f851,plain,
    ( ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k9_relat_1(sK2,X2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f847,f168])).

fof(f847,plain,
    ( ! [X3] : m1_subset_1(k9_relat_1(sK2,X3),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f739,f835])).

fof(f861,plain,
    ( spl4_86
    | spl4_142
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f844,f121,f859,f514])).

fof(f859,plain,
    ( spl4_142
  <=> ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK1,X2))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k9_relat_1(sK1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f844,plain,
    ( ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK1,X2))
        | v1_xboole_0(k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k1_zfmisc_1(sK0),k9_relat_1(sK1,X2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f840,f168])).

fof(f816,plain,
    ( spl4_138
    | spl4_140
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f439,f107,f814,f808])).

fof(f814,plain,
    ( spl4_140
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f439,plain,
    ( ! [X6] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X6,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f433,f167])).

fof(f806,plain,
    ( ~ spl4_135
    | spl4_88
    | spl4_136
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f765,f726,f804,f520,f798])).

fof(f798,plain,
    ( spl4_135
  <=> ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f804,plain,
    ( spl4_136
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f765,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2)))))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2)))))
    | ~ spl4_128 ),
    inference(resolution,[],[f727,f168])).

fof(f764,plain,
    ( spl4_132
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f757,f750,f762])).

fof(f762,plain,
    ( spl4_132
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f750,plain,
    ( spl4_130
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f757,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl4_130 ),
    inference(superposition,[],[f80,f751])).

fof(f751,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f750])).

fof(f752,plain,
    ( spl4_130
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_126 ),
    inference(avatar_split_clause,[],[f733,f720,f201,f189,f750])).

fof(f720,plain,
    ( spl4_126
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f733,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_126 ),
    inference(forward_demodulation,[],[f729,f202])).

fof(f729,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl4_20
    | ~ spl4_126 ),
    inference(resolution,[],[f721,f195])).

fof(f721,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl4_126 ),
    inference(avatar_component_clause,[],[f720])).

fof(f728,plain,
    ( spl4_126
    | spl4_128
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f594,f566,f726,f720])).

fof(f594,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK2)))),sK0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl4_100 ),
    inference(resolution,[],[f567,f433])).

fof(f567,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f566])).

fof(f713,plain,
    ( spl4_124
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f706,f699,f711])).

fof(f711,plain,
    ( spl4_124
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f699,plain,
    ( spl4_122
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f706,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK1)))
    | ~ spl4_122 ),
    inference(superposition,[],[f80,f700])).

fof(f700,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK1)))
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f699])).

fof(f701,plain,
    ( spl4_122
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f692,f679,f201,f189,f699])).

fof(f679,plain,
    ( spl4_118
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f692,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_relat_1(sK1)))
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_118 ),
    inference(forward_demodulation,[],[f688,f202])).

fof(f688,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_relat_1(sK1)))
    | ~ spl4_20
    | ~ spl4_118 ),
    inference(resolution,[],[f680,f195])).

fof(f680,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK1))))
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f679])).

fof(f687,plain,
    ( spl4_118
    | spl4_120
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f558,f530,f685,f679])).

fof(f685,plain,
    ( spl4_120
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f530,plain,
    ( spl4_92
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f558,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(k1_relat_1(sK1)))),sK0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_relat_1(sK1))))
    | ~ spl4_92 ),
    inference(resolution,[],[f531,f433])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | m1_subset_1(X0,sK0) )
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f530])).

fof(f674,plain,
    ( ~ spl4_115
    | spl4_88
    | spl4_116
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f592,f575,f672,f520,f666])).

fof(f672,plain,
    ( spl4_116
  <=> v1_xboole_0(sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f592,plain,
    ( v1_xboole_0(sK3(k1_relat_1(sK2)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(k1_relat_1(sK2)))
    | ~ spl4_102 ),
    inference(resolution,[],[f576,f168])).

fof(f661,plain,
    ( ~ spl4_111
    | spl4_88
    | spl4_112
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f556,f539,f659,f520,f653])).

fof(f659,plain,
    ( spl4_112
  <=> v1_xboole_0(sK3(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f556,plain,
    ( v1_xboole_0(sK3(k1_relat_1(sK1)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3(k1_relat_1(sK1)))
    | ~ spl4_94 ),
    inference(resolution,[],[f540,f168])).

fof(f648,plain,
    ( ~ spl4_109
    | spl4_86
    | spl4_98
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f503,f499,f563,f514,f646])).

fof(f503,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2))
    | ~ spl4_82 ),
    inference(resolution,[],[f500,f168])).

fof(f641,plain,
    ( ~ spl4_107
    | spl4_86
    | spl4_90
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f494,f490,f527,f514,f639])).

fof(f527,plain,
    ( spl4_90
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f494,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1))
    | ~ spl4_80 ),
    inference(resolution,[],[f491,f168])).

fof(f591,plain,
    ( spl4_104
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f582,f563,f201,f189,f589])).

fof(f582,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_98 ),
    inference(forward_demodulation,[],[f578,f202])).

fof(f578,plain,
    ( k1_relat_1(sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_98 ),
    inference(resolution,[],[f564,f195])).

fof(f564,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f563])).

fof(f577,plain,
    ( spl4_102
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f569,f566,f575])).

fof(f569,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK0)
    | ~ spl4_100 ),
    inference(resolution,[],[f567,f80])).

fof(f568,plain,
    ( spl4_98
    | spl4_100
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f502,f499,f566,f563])).

fof(f502,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl4_82 ),
    inference(resolution,[],[f500,f178])).

fof(f555,plain,
    ( spl4_96
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f546,f527,f201,f189,f553])).

fof(f553,plain,
    ( spl4_96
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f546,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_90 ),
    inference(forward_demodulation,[],[f542,f202])).

fof(f542,plain,
    ( k1_relat_1(sK1) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_90 ),
    inference(resolution,[],[f528,f195])).

fof(f528,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f527])).

fof(f541,plain,
    ( spl4_94
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f533,f530,f539])).

fof(f533,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK1)),sK0)
    | ~ spl4_92 ),
    inference(resolution,[],[f531,f80])).

fof(f532,plain,
    ( spl4_90
    | spl4_92
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f493,f490,f530,f527])).

fof(f493,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl4_80 ),
    inference(resolution,[],[f491,f178])).

fof(f522,plain,
    ( ~ spl4_85
    | spl4_86
    | spl4_88
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f485,f481,f520,f514,f508])).

fof(f485,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK0)
    | ~ spl4_78 ),
    inference(resolution,[],[f482,f168])).

fof(f501,plain,
    ( spl4_82
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f468,f460,f128,f499])).

fof(f468,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f464,f461])).

fof(f464,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f90,f129])).

fof(f492,plain,
    ( spl4_80
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f467,f453,f121,f490])).

fof(f467,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f463,f454])).

fof(f463,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f90,f122])).

fof(f483,plain,
    ( spl4_78
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f474,f135,f121,f481])).

fof(f474,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f470,f136])).

fof(f470,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f122])).

fof(f462,plain,
    ( spl4_76
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f446,f128,f460])).

fof(f446,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f129])).

fof(f455,plain,
    ( spl4_74
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f445,f121,f453])).

fof(f445,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f122])).

fof(f432,plain,
    ( spl4_70
    | ~ spl4_73
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f419,f397,f430,f424])).

fof(f424,plain,
    ( spl4_70
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f419,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK2))
    | v1_xboole_0(sK3(sK2))
    | ~ spl4_66 ),
    inference(resolution,[],[f398,f80])).

fof(f418,plain,
    ( spl4_68
    | ~ spl4_22
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f411,f359,f201,f416])).

fof(f416,plain,
    ( spl4_68
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f359,plain,
    ( spl4_56
  <=> k2_zfmisc_1(sK0,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f411,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_22
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f409,f202])).

fof(f409,plain,
    ( v1_relat_1(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_56 ),
    inference(superposition,[],[f150,f360])).

fof(f360,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f359])).

fof(f150,plain,(
    ! [X0,X1] : v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f87,f80])).

fof(f399,plain,
    ( spl4_50
    | spl4_66
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f287,f270,f397,f328])).

fof(f328,plain,
    ( spl4_50
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f270,plain,
    ( spl4_38
  <=> ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl4_38 ),
    inference(resolution,[],[f271,f168])).

fof(f271,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f270])).

fof(f395,plain,
    ( spl4_62
    | ~ spl4_65
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f382,f331,f393,f387])).

fof(f387,plain,
    ( spl4_62
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f382,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl4_52 ),
    inference(resolution,[],[f332,f80])).

fof(f380,plain,
    ( spl4_60
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f366,f142,f128,f378])).

fof(f366,plain,
    ( k2_relat_1(sK2) = sK0
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f363,f143])).

fof(f363,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f88,f129])).

fof(f373,plain,
    ( spl4_58
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f365,f135,f121,f371])).

fof(f365,plain,
    ( k2_relat_1(sK1) = sK0
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f362,f136])).

fof(f362,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f88,f122])).

fof(f361,plain,
    ( spl4_56
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f352,f328,f201,f189,f359])).

fof(f352,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_xboole_0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f348,f202])).

fof(f348,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_50 ),
    inference(resolution,[],[f329,f195])).

fof(f329,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f328])).

fof(f347,plain,
    ( spl4_54
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f338,f238,f201,f189,f345])).

fof(f345,plain,
    ( spl4_54
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f238,plain,
    ( spl4_30
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f338,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f334,f202])).

fof(f334,plain,
    ( sK1 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_30 ),
    inference(resolution,[],[f239,f195])).

fof(f239,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f333,plain,
    ( spl4_50
    | spl4_52
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f268,f265,f331,f328])).

fof(f265,plain,
    ( spl4_36
  <=> ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X0) )
    | ~ spl4_36 ),
    inference(resolution,[],[f266,f168])).

fof(f266,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f265])).

fof(f323,plain,
    ( spl4_48
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f307,f164,f157,f321])).

fof(f307,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f158])).

fof(f316,plain,
    ( spl4_46
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f308,f164,f314])).

fof(f314,plain,
    ( spl4_46
  <=> k2_relat_1(k5_relat_1(sK2,sK2)) = k9_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f308,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK2)) = k9_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f165])).

fof(f305,plain,
    ( spl4_44
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f290,f164,f157,f303])).

fof(f303,plain,
    ( spl4_44
  <=> k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f290,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1))
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(resolution,[],[f261,f165])).

fof(f298,plain,
    ( spl4_42
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f289,f157,f296])).

fof(f296,plain,
    ( spl4_42
  <=> k2_relat_1(k5_relat_1(sK1,sK1)) = k9_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f289,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK1)) = k9_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f261,f158])).

fof(f286,plain,
    ( spl4_40
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f277,f251,f201,f189,f284])).

fof(f284,plain,
    ( spl4_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f251,plain,
    ( spl4_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f277,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f273,f202])).

fof(f273,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_34 ),
    inference(resolution,[],[f252,f195])).

fof(f252,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f251])).

fof(f272,plain,
    ( spl4_34
    | spl4_38
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f258,f128,f270,f251])).

fof(f258,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(sK0,sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f178,f129])).

fof(f267,plain,
    ( spl4_30
    | spl4_36
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f257,f121,f265,f238])).

fof(f257,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f178,f122])).

fof(f253,plain,
    ( ~ spl4_33
    | spl4_28
    | spl4_34
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f181,f128,f251,f232,f245])).

fof(f232,plain,
    ( spl4_28
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f181,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f168,f129])).

fof(f240,plain,
    ( ~ spl4_27
    | spl4_28
    | spl4_30
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f180,f121,f238,f232,f226])).

fof(f180,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f168,f122])).

fof(f215,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f207,f201,f213])).

fof(f213,plain,
    ( spl4_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f80,f202])).

fof(f203,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f196,f189,f201])).

fof(f196,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(resolution,[],[f190,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t6_boole)).

fof(f193,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_18 ),
    inference(resolution,[],[f184,f80])).

fof(f184,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_18
  <=> ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f191,plain,
    ( spl4_18
    | spl4_20
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f170,f107,f189,f183])).

fof(f170,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X0,sK3(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f169,f83])).

fof(f169,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f167,f80])).

fof(f177,plain,(
    ~ spl4_17 ),
    inference(avatar_split_clause,[],[f75,f175])).

fof(f75,plain,(
    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    & k2_relset_1(sK0,sK0,sK2) = sK0
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f67,f66])).

fof(f66,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) != sK0
          & k2_relset_1(sK0,sK0,X2) = sK0
          & k2_relset_1(sK0,sK0,sK1) = sK0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,sK2,X1)) != X0
        & k2_relset_1(X0,X0,sK2) = X0
        & k2_relset_1(X0,X0,X1) = X0
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',t73_funct_2)).

fof(f166,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f152,f128,f164])).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f87,f129])).

fof(f159,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f151,f121,f157])).

fof(f151,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f87,f122])).

fof(f144,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f74,f142])).

fof(f74,plain,(
    k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f68])).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f73,f135])).

fof(f73,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f72,f128])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f123,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f71,f121])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f116,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f77,f114])).

fof(f114,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',d2_xboole_0)).

fof(f109,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f102,f107])).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f76,f77])).

fof(f76,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t73_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
