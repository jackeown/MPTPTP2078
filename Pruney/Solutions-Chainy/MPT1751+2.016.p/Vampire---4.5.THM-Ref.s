%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:23 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  942 (6914 expanded)
%              Number of leaves         :  236 (2473 expanded)
%              Depth                    :   12
%              Number of atoms          : 4145 (23972 expanded)
%              Number of equality atoms :   46 ( 365 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2895,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f147,f152,f165,f174,f176,f186,f197,f209,f235,f268,f272,f283,f303,f307,f312,f313,f314,f315,f333,f334,f335,f360,f364,f451,f452,f477,f478,f479,f483,f484,f485,f486,f487,f503,f507,f511,f524,f558,f559,f560,f561,f598,f602,f621,f622,f623,f641,f749,f768,f773,f797,f895,f923,f924,f953,f954,f955,f956,f960,f961,f962,f963,f964,f965,f982,f999,f1060,f1061,f1062,f1063,f1064,f1081,f1139,f1143,f1163,f1164,f1165,f1166,f1184,f1188,f1192,f1196,f1229,f1233,f1404,f1408,f1530,f1534,f1538,f1542,f1547,f1551,f1552,f1553,f1554,f1555,f1562,f1566,f1570,f1575,f1583,f1587,f1591,f1595,f1599,f1603,f1607,f1611,f1615,f1616,f1620,f1624,f1625,f1629,f1633,f1637,f1641,f1743,f1763,f1794,f1795,f1796,f1797,f1899,f1952,f1957,f1962,f1967,f1969,f1970,f1978,f1983,f1993,f1998,f2004,f2006,f2026,f2038,f2063,f2068,f2072,f2073,f2077,f2078,f2083,f2104,f2109,f2115,f2122,f2151,f2172,f2183,f2187,f2206,f2211,f2212,f2213,f2214,f2215,f2245,f2249,f2253,f2257,f2261,f2271,f2277,f2301,f2305,f2309,f2313,f2317,f2330,f2335,f2382,f2386,f2390,f2394,f2398,f2417,f2421,f2425,f2429,f2433,f2455,f2459,f2464,f2465,f2485,f2516,f2520,f2524,f2528,f2532,f2549,f2553,f2557,f2561,f2565,f2655,f2660,f2664,f2672,f2676,f2680,f2681,f2682,f2686,f2690,f2691,f2695,f2700,f2701,f2702,f2707,f2708,f2709,f2714,f2715,f2716,f2717,f2722,f2726,f2727,f2728,f2733,f2737,f2741,f2742,f2743,f2744,f2745,f2749,f2753,f2754,f2755,f2759,f2761,f2787,f2791,f2795,f2799,f2803,f2823,f2827,f2831,f2835,f2839,f2845,f2865,f2885,f2891,f2894])).

fof(f2894,plain,
    ( ~ spl5_20
    | ~ spl5_2
    | spl5_217 ),
    inference(avatar_split_clause,[],[f2893,f2888,f77,f171])).

fof(f171,plain,
    ( spl5_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f77,plain,
    ( spl5_2
  <=> r1_tarski(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2888,plain,
    ( spl5_217
  <=> k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).

fof(f2893,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK2))
    | ~ v1_relat_1(sK3)
    | spl5_217 ),
    inference(trivial_inequality_removal,[],[f2892])).

fof(f2892,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK2))
    | ~ v1_relat_1(sK3)
    | spl5_217 ),
    inference(superposition,[],[f2890,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f2890,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl5_217 ),
    inference(avatar_component_clause,[],[f2888])).

fof(f2891,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_217
    | spl5_214 ),
    inference(avatar_split_clause,[],[f2886,f2842,f2888,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f122,plain,
    ( spl5_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f117,plain,
    ( spl5_10
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f112,plain,
    ( spl5_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f137,plain,
    ( spl5_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f132,plain,
    ( spl5_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f127,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f97,plain,
    ( spl5_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f92,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f87,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f102,plain,
    ( spl5_7
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2842,plain,
    ( spl5_214
  <=> k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) = k9_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f2886,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_214 ),
    inference(superposition,[],[f2844,f1508])).

fof(f1508,plain,(
    ! [X6,X4,X7,X5] :
      ( k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7)
      | ~ m1_pre_topc(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f1505])).

fof(f1505,plain,(
    ! [X6,X4,X7,X5] :
      ( k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7)
      | ~ m1_pre_topc(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_1(X6) ) ),
    inference(superposition,[],[f57,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f2844,plain,
    ( k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4)
    | spl5_214 ),
    inference(avatar_component_clause,[],[f2842])).

fof(f2885,plain,
    ( ~ spl5_198
    | spl5_216
    | ~ spl5_191 ),
    inference(avatar_split_clause,[],[f2881,f2688,f2883,f2730])).

fof(f2730,plain,
    ( spl5_198
  <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f2883,plain,
    ( spl5_216
  <=> ! [X27,X26] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK3)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).

fof(f2688,plain,
    ( spl5_191
  <=> ! [X12] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12)
        | ~ r1_tarski(X12,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f2881,plain,
    ( ! [X26,X27] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27) )
    | ~ spl5_191 ),
    inference(resolution,[],[f2689,f753])).

fof(f753,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(X9,k2_zfmisc_1(X11,X10))
      | ~ r1_tarski(k1_relat_1(X9),X11)
      | ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X10) ) ),
    inference(resolution,[],[f65,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f2689,plain,
    ( ! [X12] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12)
        | ~ r1_tarski(X12,sK3) )
    | ~ spl5_191 ),
    inference(avatar_component_clause,[],[f2688])).

fof(f2865,plain,
    ( ~ spl5_198
    | spl5_215
    | ~ spl5_185 ),
    inference(avatar_split_clause,[],[f2861,f2662,f2863,f2730])).

fof(f2863,plain,
    ( spl5_215
  <=> ! [X27,X26] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f2662,plain,
    ( spl5_185
  <=> ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2)
        | ~ r1_tarski(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f2861,plain,
    ( ! [X26,X27] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27) )
    | ~ spl5_185 ),
    inference(resolution,[],[f2663,f753])).

fof(f2663,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2)
        | ~ r1_tarski(X2,sK4) )
    | ~ spl5_185 ),
    inference(avatar_component_clause,[],[f2662])).

fof(f2845,plain,
    ( ~ spl5_4
    | ~ spl5_214
    | spl5_57 ),
    inference(avatar_split_clause,[],[f2840,f746,f2842,f87])).

fof(f746,plain,
    ( spl5_57
  <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f2840,plain,
    ( k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl5_57 ),
    inference(superposition,[],[f748,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f748,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | spl5_57 ),
    inference(avatar_component_clause,[],[f746])).

fof(f2839,plain,
    ( ~ spl5_116
    | spl5_213
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2818,f1949,f2837,f1954])).

fof(f1954,plain,
    ( spl5_116
  <=> v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f2837,plain,
    ( spl5_213
  <=> ! [X16,X18,X17] :
        ( v4_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f1949,plain,
    ( spl5_115
  <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f2818,plain,
    ( ! [X17,X18,X16] :
        ( v4_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2600,f433])).

fof(f433,plain,(
    ! [X24,X23,X25,X22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X23,k1_relat_1(k7_relat_1(X22,k7_relat_1(X24,X25))))),X24)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X22)
      | ~ v1_relat_1(X24) ) ),
    inference(resolution,[],[f390,f211])).

fof(f211,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k7_relat_1(X4,X5))
      | r1_tarski(X3,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f68,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f390,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,k1_relat_1(k7_relat_1(X7,X8)))),X8)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f212,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f212,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,k1_relat_1(k7_relat_1(X8,X7)))
      | r1_tarski(X6,X7)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f68,f60])).

fof(f2600,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v4_relat_1(X1,u1_struct_0(sK2)) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f66,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2283,plain,
    ( ! [X3] :
        ( r1_tarski(X3,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
        | ~ r1_tarski(X3,k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f1950,f68])).

fof(f1950,plain,
    ( r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | ~ spl5_115 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f2835,plain,
    ( ~ spl5_116
    | spl5_212
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2816,f1949,f2833,f1954])).

fof(f2833,plain,
    ( spl5_212
  <=> ! [X13,X12] :
        ( v4_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f2816,plain,
    ( ! [X12,X13] :
        ( v4_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X12) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2600,f252])).

fof(f252,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,k7_relat_1(X7,X8))),X7)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f211,f60])).

fof(f2831,plain,
    ( ~ spl5_116
    | spl5_211
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2812,f1949,f2829,f1954])).

fof(f2829,plain,
    ( spl5_211
  <=> ! [X5,X4,X6] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f2812,plain,
    ( ! [X6,X4,X5] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2600,f426])).

fof(f426,plain,(
    ! [X24,X23,X25,X22] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24),X25),X22)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24))
      | ~ v1_relat_1(X22) ) ),
    inference(global_subsumption,[],[f181,f420])).

fof(f420,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ v1_relat_1(k7_relat_1(X22,X23))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24))
      | r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24),X25),X22)
      | ~ v1_relat_1(X22) ) ),
    inference(resolution,[],[f251,f211])).

fof(f251,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X3,X4),X5),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(resolution,[],[f211,f59])).

fof(f181,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f156,f59])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f64])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2827,plain,
    ( ~ spl5_116
    | spl5_210
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2811,f1949,f2825,f1954])).

fof(f2825,plain,
    ( spl5_210
  <=> ! [X3,X2] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f2811,plain,
    ( ! [X2,X3] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2600,f251])).

fof(f2823,plain,
    ( ~ spl5_116
    | spl5_209
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2810,f1949,f2821,f1954])).

fof(f2821,plain,
    ( spl5_209
  <=> ! [X1] : v4_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f2810,plain,
    ( ! [X1] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2600,f59])).

fof(f2803,plain,
    ( ~ spl5_116
    | spl5_208
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2782,f1949,f2801,f1954])).

fof(f2801,plain,
    ( spl5_208
  <=> ! [X16,X18,X17] :
        ( v5_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f2782,plain,
    ( ! [X17,X18,X16] :
        ( v5_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2599,f433])).

fof(f2599,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v5_relat_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f67,f64])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2799,plain,
    ( ~ spl5_116
    | spl5_207
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2780,f1949,f2797,f1954])).

fof(f2797,plain,
    ( spl5_207
  <=> ! [X13,X12] :
        ( v5_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f2780,plain,
    ( ! [X12,X13] :
        ( v5_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X12) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2599,f252])).

fof(f2795,plain,
    ( ~ spl5_116
    | spl5_206
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2776,f1949,f2793,f1954])).

fof(f2793,plain,
    ( spl5_206
  <=> ! [X5,X4,X6] :
        ( v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f2776,plain,
    ( ! [X6,X4,X5] :
        ( v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2599,f426])).

fof(f2791,plain,
    ( ~ spl5_116
    | spl5_205
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2775,f1949,f2789,f1954])).

fof(f2789,plain,
    ( spl5_205
  <=> ! [X3,X2] :
        ( v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f2775,plain,
    ( ! [X2,X3] :
        ( v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2599,f251])).

fof(f2787,plain,
    ( ~ spl5_116
    | spl5_204
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2774,f1949,f2785,f1954])).

fof(f2785,plain,
    ( spl5_204
  <=> ! [X1] : v5_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f2774,plain,
    ( ! [X1] :
        ( v5_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2599,f59])).

fof(f2761,plain,(
    spl5_198 ),
    inference(avatar_contradiction_clause,[],[f2760])).

fof(f2760,plain,
    ( $false
    | spl5_198 ),
    inference(resolution,[],[f2732,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f2732,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | spl5_198 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2759,plain,
    ( ~ spl5_182
    | spl5_203
    | ~ spl5_16
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2646,f1949,f149,f2757,f2648])).

fof(f2648,plain,
    ( spl5_182
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f2757,plain,
    ( spl5_203
  <=> ! [X60,X61] :
        ( ~ r1_tarski(k7_relat_1(X60,X61),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X60)
        | ~ v1_relat_1(k7_relat_1(X60,X61))
        | v4_relat_1(k7_relat_1(X60,X61),X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f149,plain,
    ( spl5_16
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f2646,plain,
    ( ! [X61,X60] :
        ( ~ r1_tarski(k7_relat_1(X60,X61),k7_relat_1(sK3,u1_struct_0(sK2)))
        | v4_relat_1(k7_relat_1(X60,X61),X61)
        | ~ v1_relat_1(k7_relat_1(X60,X61))
        | ~ v1_relat_1(X60)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) )
    | ~ spl5_16
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1366])).

fof(f1366,plain,
    ( ! [X21,X22,X20] :
        ( ~ r1_tarski(k7_relat_1(X20,X21),X22)
        | v4_relat_1(k7_relat_1(X20,X21),X21)
        | ~ v1_relat_1(k7_relat_1(X20,X21))
        | ~ v1_relat_1(X20)
        | ~ r1_tarski(X22,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f802,f275])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( v5_relat_1(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f229,f204])).

fof(f229,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK3)
        | ~ r1_tarski(X3,X2) )
    | ~ spl5_16 ),
    inference(resolution,[],[f213,f68])).

fof(f213,plain,
    ( ! [X9] :
        ( r1_tarski(X9,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(X9,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f68,f151])).

fof(f151,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f802,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | v4_relat_1(k7_relat_1(X0,X1),X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f789,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f789,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | v4_relat_1(k7_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f181,f774])).

fof(f774,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | v4_relat_1(k7_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f751,f60])).

fof(f751,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),X5)
      | ~ r1_tarski(k2_relat_1(X3),X4)
      | ~ v1_relat_1(X3)
      | v4_relat_1(X3,X5) ) ),
    inference(resolution,[],[f65,f66])).

fof(f2755,plain,
    ( ~ spl5_184
    | spl5_202
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2641,f1949,f77,f2751,f2657])).

fof(f2657,plain,
    ( spl5_184
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f2751,plain,
    ( spl5_202
  <=> ! [X45,X47] :
        ( ~ r1_tarski(k1_relat_1(X45),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_relat_1(X45),X47)
        | v4_relat_1(X45,u1_struct_0(sK2))
        | ~ v1_relat_1(X45) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f2641,plain,
    ( ! [X50,X51] :
        ( ~ r1_tarski(k1_relat_1(X50),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X50)
        | v4_relat_1(X50,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
        | ~ r1_tarski(k2_relat_1(X50),X51) )
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f780])).

fof(f780,plain,
    ( ! [X26,X24,X25] :
        ( ~ r1_tarski(k1_relat_1(X24),X26)
        | ~ v1_relat_1(X24)
        | v4_relat_1(X24,u1_struct_0(sK2))
        | ~ r1_tarski(X26,sK4)
        | ~ r1_tarski(k2_relat_1(X24),X25) )
    | ~ spl5_2 ),
    inference(resolution,[],[f751,f216])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,u1_struct_0(sK2))
        | ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(X1,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f214,f68])).

fof(f214,plain,
    ( ! [X10] :
        ( r1_tarski(X10,u1_struct_0(sK2))
        | ~ r1_tarski(X10,sK4) )
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f2754,plain,
    ( ~ spl5_184
    | spl5_201
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2640,f1949,f144,f2747,f2657])).

fof(f2747,plain,
    ( spl5_201
  <=> ! [X42,X44] :
        ( ~ r1_tarski(k1_relat_1(X42),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_relat_1(X42),X44)
        | v4_relat_1(X42,u1_struct_0(sK1))
        | ~ v1_relat_1(X42) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f144,plain,
    ( spl5_15
  <=> r1_tarski(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f2640,plain,
    ( ! [X48,X49] :
        ( ~ r1_tarski(k1_relat_1(X48),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X48)
        | v4_relat_1(X48,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
        | ~ r1_tarski(k2_relat_1(X48),X49) )
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f784])).

fof(f784,plain,
    ( ! [X39,X38,X40] :
        ( ~ r1_tarski(k1_relat_1(X38),X40)
        | ~ v1_relat_1(X38)
        | v4_relat_1(X38,u1_struct_0(sK1))
        | ~ r1_tarski(X40,sK4)
        | ~ r1_tarski(k2_relat_1(X38),X39) )
    | ~ spl5_15 ),
    inference(resolution,[],[f751,f219])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,u1_struct_0(sK1))
        | ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(X1,X0) )
    | ~ spl5_15 ),
    inference(resolution,[],[f215,f68])).

fof(f215,plain,
    ( ! [X11] :
        ( r1_tarski(X11,u1_struct_0(sK1))
        | ~ r1_tarski(X11,sK4) )
    | ~ spl5_15 ),
    inference(resolution,[],[f68,f146])).

fof(f146,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f2753,plain,
    ( spl5_185
    | spl5_202
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2639,f1949,f77,f2751,f2662])).

fof(f2639,plain,
    ( ! [X47,X45,X46] :
        ( ~ r1_tarski(k1_relat_1(X45),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X45)
        | v4_relat_1(X45,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X46)
        | ~ r1_tarski(X46,sK4)
        | ~ r1_tarski(k2_relat_1(X45),X47) )
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f779])).

fof(f779,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(k1_relat_1(X20),X22)
        | ~ v1_relat_1(X20)
        | v4_relat_1(X20,u1_struct_0(sK2))
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,sK4)
        | ~ r1_tarski(k2_relat_1(X20),X21) )
    | ~ spl5_2 ),
    inference(resolution,[],[f751,f240])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,u1_struct_0(sK2))
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(X2,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f216,f68])).

fof(f2749,plain,
    ( spl5_185
    | spl5_201
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2638,f1949,f144,f2747,f2662])).

fof(f2638,plain,
    ( ! [X43,X44,X42] :
        ( ~ r1_tarski(k1_relat_1(X42),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X42)
        | v4_relat_1(X42,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X43)
        | ~ r1_tarski(X43,sK4)
        | ~ r1_tarski(k2_relat_1(X42),X44) )
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f783])).

fof(f783,plain,
    ( ! [X37,X35,X36,X34] :
        ( ~ r1_tarski(k1_relat_1(X34),X36)
        | ~ v1_relat_1(X34)
        | v4_relat_1(X34,u1_struct_0(sK1))
        | ~ r1_tarski(X36,X37)
        | ~ r1_tarski(X37,sK4)
        | ~ r1_tarski(k2_relat_1(X34),X35) )
    | ~ spl5_15 ),
    inference(resolution,[],[f751,f245])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,u1_struct_0(sK1))
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(X2,X1) )
    | ~ spl5_15 ),
    inference(resolution,[],[f219,f68])).

fof(f2745,plain,
    ( spl5_189
    | spl5_200
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2635,f1949,f144,f2739,f2678])).

fof(f2678,plain,
    ( spl5_189
  <=> ! [X7,X8] :
        ( ~ r1_tarski(X7,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X8)
        | ~ r1_tarski(X8,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).

fof(f2739,plain,
    ( spl5_200
  <=> ! [X29] :
        ( ~ r1_tarski(k2_relat_1(X29),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X29)
        | v5_relat_1(X29,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f2635,plain,
    ( ! [X39,X37,X38] :
        ( ~ r1_tarski(k2_relat_1(X37),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X38)
        | ~ r1_tarski(X38,X39)
        | ~ r1_tarski(X39,sK4)
        | v5_relat_1(X37,u1_struct_0(sK1))
        | ~ v1_relat_1(X37) )
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f659])).

fof(f659,plain,
    ( ! [X45,X43,X46,X44] :
        ( ~ r1_tarski(k2_relat_1(X46),X44)
        | ~ r1_tarski(X44,X45)
        | ~ r1_tarski(X45,X43)
        | ~ r1_tarski(X43,sK4)
        | v5_relat_1(X46,u1_struct_0(sK1))
        | ~ v1_relat_1(X46) )
    | ~ spl5_15 ),
    inference(resolution,[],[f370,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f370,plain,
    ( ! [X6,X4,X5,X3] :
        ( r1_tarski(X6,u1_struct_0(sK1))
        | ~ r1_tarski(X4,sK4)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X6,X5) )
    | ~ spl5_15 ),
    inference(resolution,[],[f245,f68])).

fof(f2744,plain,
    ( spl5_189
    | spl5_199
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2634,f1949,f77,f2735,f2678])).

fof(f2735,plain,
    ( spl5_199
  <=> ! [X28] :
        ( ~ r1_tarski(k2_relat_1(X28),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X28)
        | v5_relat_1(X28,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f2634,plain,
    ( ! [X35,X36,X34] :
        ( ~ r1_tarski(k2_relat_1(X34),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X35)
        | ~ r1_tarski(X35,X36)
        | ~ r1_tarski(X36,sK4)
        | v5_relat_1(X34,u1_struct_0(sK2))
        | ~ v1_relat_1(X34) )
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f590])).

fof(f590,plain,
    ( ! [X37,X35,X38,X36] :
        ( ~ r1_tarski(k2_relat_1(X38),X36)
        | ~ r1_tarski(X36,X37)
        | ~ r1_tarski(X37,X35)
        | ~ r1_tarski(X35,sK4)
        | v5_relat_1(X38,u1_struct_0(sK2))
        | ~ v1_relat_1(X38) )
    | ~ spl5_2 ),
    inference(resolution,[],[f341,f62])).

fof(f341,plain,
    ( ! [X6,X4,X5,X3] :
        ( r1_tarski(X6,u1_struct_0(sK2))
        | ~ r1_tarski(X4,sK4)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X6,X5) )
    | ~ spl5_2 ),
    inference(resolution,[],[f240,f68])).

fof(f2743,plain,
    ( spl5_185
    | spl5_200
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2633,f1949,f144,f2739,f2662])).

fof(f2633,plain,
    ( ! [X33,X32] :
        ( ~ r1_tarski(k2_relat_1(X32),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X33,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X33)
        | v5_relat_1(X32,u1_struct_0(sK1))
        | ~ v1_relat_1(X32) )
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f373])).

fof(f373,plain,
    ( ! [X14,X15,X13] :
        ( ~ r1_tarski(k2_relat_1(X15),X13)
        | ~ r1_tarski(X14,sK4)
        | ~ r1_tarski(X13,X14)
        | v5_relat_1(X15,u1_struct_0(sK1))
        | ~ v1_relat_1(X15) )
    | ~ spl5_15 ),
    inference(resolution,[],[f245,f62])).

fof(f2742,plain,
    ( spl5_185
    | spl5_199
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2632,f1949,f77,f2735,f2662])).

fof(f2632,plain,
    ( ! [X30,X31] :
        ( ~ r1_tarski(k2_relat_1(X30),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X31,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X31)
        | v5_relat_1(X30,u1_struct_0(sK2))
        | ~ v1_relat_1(X30) )
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f343])).

fof(f343,plain,
    ( ! [X12,X10,X11] :
        ( ~ r1_tarski(k2_relat_1(X12),X10)
        | ~ r1_tarski(X11,sK4)
        | ~ r1_tarski(X10,X11)
        | v5_relat_1(X12,u1_struct_0(sK2))
        | ~ v1_relat_1(X12) )
    | ~ spl5_2 ),
    inference(resolution,[],[f240,f62])).

fof(f2741,plain,
    ( ~ spl5_184
    | spl5_200
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2631,f1949,f144,f2739,f2657])).

fof(f2631,plain,
    ( ! [X29] :
        ( ~ r1_tarski(k2_relat_1(X29),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
        | v5_relat_1(X29,u1_struct_0(sK1))
        | ~ v1_relat_1(X29) )
    | ~ spl5_15
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f247])).

fof(f247,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k2_relat_1(X6),X5)
        | ~ r1_tarski(X5,sK4)
        | v5_relat_1(X6,u1_struct_0(sK1))
        | ~ v1_relat_1(X6) )
    | ~ spl5_15 ),
    inference(resolution,[],[f219,f62])).

fof(f2737,plain,
    ( ~ spl5_184
    | spl5_199
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2630,f1949,f77,f2735,f2657])).

fof(f2630,plain,
    ( ! [X28] :
        ( ~ r1_tarski(k2_relat_1(X28),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
        | v5_relat_1(X28,u1_struct_0(sK2))
        | ~ v1_relat_1(X28) )
    | ~ spl5_2
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f242])).

fof(f242,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k2_relat_1(X6),X5)
        | ~ r1_tarski(X5,sK4)
        | v5_relat_1(X6,u1_struct_0(sK2))
        | ~ v1_relat_1(X6) )
    | ~ spl5_2 ),
    inference(resolution,[],[f216,f62])).

fof(f2733,plain,
    ( ~ spl5_198
    | spl5_197
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2628,f1949,f2724,f2730])).

fof(f2724,plain,
    ( spl5_197
  <=> ! [X18] :
        ( ~ r1_tarski(X18,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v1_relat_1(X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f2628,plain,
    ( ! [X26] :
        ( ~ r1_tarski(X26,k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
        | v1_relat_1(X26) )
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f156])).

fof(f2728,plain,
    ( ~ spl5_182
    | spl5_197
    | ~ spl5_28
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2626,f1949,f281,f2724,f2648])).

fof(f281,plain,
    ( spl5_28
  <=> ! [X7,X8] :
        ( ~ r1_tarski(X7,sK3)
        | v1_relat_1(X8)
        | ~ r1_tarski(X8,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f2626,plain,
    ( ! [X23] :
        ( ~ r1_tarski(X23,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v1_relat_1(X23)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) )
    | ~ spl5_28
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f282])).

fof(f282,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(X8,X7)
        | v1_relat_1(X8)
        | ~ r1_tarski(X7,sK3) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f281])).

fof(f2727,plain,
    ( spl5_191
    | spl5_197
    | ~ spl5_39
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2625,f1949,f449,f2724,f2688])).

fof(f449,plain,
    ( spl5_39
  <=> ! [X7,X8,X6] :
        ( ~ r1_tarski(X6,X7)
        | v1_relat_1(X8)
        | ~ r1_tarski(X8,X6)
        | ~ r1_tarski(X7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f2625,plain,
    ( ! [X21,X22] :
        ( ~ r1_tarski(X21,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v1_relat_1(X21)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X22)
        | ~ r1_tarski(X22,sK3) )
    | ~ spl5_39
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f450])).

fof(f450,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(X8,X6)
        | v1_relat_1(X8)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK3) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f449])).

fof(f2726,plain,
    ( spl5_190
    | spl5_197
    | ~ spl5_65
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2624,f1949,f921,f2724,f2684])).

fof(f2684,plain,
    ( spl5_190
  <=> ! [X11,X10] :
        ( ~ r1_tarski(X10,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X11)
        | ~ r1_tarski(X11,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f921,plain,
    ( spl5_65
  <=> ! [X20,X22,X21,X23] :
        ( ~ r1_tarski(X20,sK3)
        | v1_relat_1(X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f2624,plain,
    ( ! [X19,X20,X18] :
        ( ~ r1_tarski(X18,k7_relat_1(sK3,u1_struct_0(sK2)))
        | v1_relat_1(X18)
        | ~ r1_tarski(X19,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X20)
        | ~ r1_tarski(X20,X19) )
    | ~ spl5_65
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f922])).

fof(f922,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(X23,X21)
        | v1_relat_1(X23)
        | ~ r1_tarski(X20,sK3)
        | ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X20) )
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f921])).

fof(f2722,plain,
    ( ~ spl5_184
    | ~ spl5_196
    | ~ spl5_115
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f2623,f2450,f1949,f2719,f2657])).

fof(f2719,plain,
    ( spl5_196
  <=> r1_tarski(sK3,k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f2450,plain,
    ( spl5_166
  <=> ! [X2] :
        ( ~ r1_tarski(sK3,X2)
        | ~ r1_tarski(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f2623,plain,
    ( ~ r1_tarski(sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_115
    | ~ spl5_166 ),
    inference(resolution,[],[f2283,f2451])).

fof(f2451,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3,X2)
        | ~ r1_tarski(X2,sK4) )
    | ~ spl5_166 ),
    inference(avatar_component_clause,[],[f2450])).

fof(f2717,plain,
    ( ~ spl5_182
    | ~ spl5_195
    | ~ spl5_48
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2622,f1949,f556,f2711,f2648])).

fof(f2711,plain,
    ( spl5_195
  <=> r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).

fof(f556,plain,
    ( spl5_48
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | ~ r1_tarski(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f2622,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)
    | ~ spl5_48
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f557])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | ~ r1_tarski(X0,sK3) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f556])).

fof(f2716,plain,
    ( spl5_191
    | ~ spl5_195
    | ~ spl5_71
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2621,f1949,f1058,f2711,f2688])).

fof(f1058,plain,
    ( spl5_71
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f2621,plain,
    ( ! [X17] :
        ( ~ r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X17,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X17) )
    | ~ spl5_71
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1059])).

fof(f1059,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | ~ r1_tarski(X0,sK3)
        | ~ r1_tarski(X1,X0) )
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f2715,plain,
    ( ~ spl5_184
    | ~ spl5_195
    | ~ spl5_115
    | ~ spl5_127 ),
    inference(avatar_split_clause,[],[f2620,f2070,f1949,f2711,f2657])).

fof(f2070,plain,
    ( spl5_127
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f2620,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_115
    | ~ spl5_127 ),
    inference(resolution,[],[f2283,f2071])).

fof(f2071,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | ~ r1_tarski(X0,sK4) )
    | ~ spl5_127 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f2714,plain,
    ( spl5_185
    | ~ spl5_195
    | ~ spl5_115
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2619,f2075,f1949,f2711,f2662])).

fof(f2075,plain,
    ( spl5_128
  <=> ! [X3,X2] :
        ( ~ r1_tarski(u1_struct_0(sK0),X2)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f2619,plain,
    ( ! [X16] :
        ( ~ r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X16,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X16) )
    | ~ spl5_115
    | ~ spl5_128 ),
    inference(resolution,[],[f2283,f2076])).

fof(f2076,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(u1_struct_0(sK0),X2)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f2075])).

fof(f2709,plain,
    ( ~ spl5_182
    | ~ spl5_194
    | ~ spl5_42
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2618,f1949,f481,f2704,f2648])).

fof(f2704,plain,
    ( spl5_194
  <=> r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f481,plain,
    ( spl5_42
  <=> ! [X10] :
        ( ~ r1_tarski(u1_struct_0(sK1),X10)
        | ~ r1_tarski(X10,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f2618,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)
    | ~ spl5_42
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f482])).

fof(f482,plain,
    ( ! [X10] :
        ( ~ r1_tarski(u1_struct_0(sK1),X10)
        | ~ r1_tarski(X10,sK3) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f481])).

fof(f2708,plain,
    ( spl5_191
    | ~ spl5_194
    | ~ spl5_67
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2617,f1949,f958,f2704,f2688])).

fof(f958,plain,
    ( spl5_67
  <=> ! [X20,X19] :
        ( ~ r1_tarski(X19,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X20)
        | ~ r1_tarski(X20,X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f2617,plain,
    ( ! [X15] :
        ( ~ r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X15,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X15) )
    | ~ spl5_67
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f959])).

fof(f959,plain,
    ( ! [X19,X20] :
        ( ~ r1_tarski(u1_struct_0(sK1),X20)
        | ~ r1_tarski(X19,sK3)
        | ~ r1_tarski(X20,X19) )
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f958])).

fof(f2707,plain,
    ( ~ spl5_184
    | ~ spl5_194
    | ~ spl5_79
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2616,f1949,f1190,f2704,f2657])).

fof(f1190,plain,
    ( spl5_79
  <=> ! [X15] :
        ( ~ r1_tarski(u1_struct_0(sK1),X15)
        | ~ r1_tarski(X15,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f2616,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_79
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1191])).

fof(f1191,plain,
    ( ! [X15] :
        ( ~ r1_tarski(u1_struct_0(sK1),X15)
        | ~ r1_tarski(X15,sK4) )
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f1190])).

fof(f2702,plain,
    ( ~ spl5_182
    | ~ spl5_193
    | ~ spl5_40
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2615,f1949,f472,f2697,f2648])).

fof(f2697,plain,
    ( spl5_193
  <=> r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f472,plain,
    ( spl5_40
  <=> ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),X1)
        | ~ r1_tarski(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f2615,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)
    | ~ spl5_40
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f473])).

fof(f473,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),X1)
        | ~ r1_tarski(X1,sK3) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f472])).

fof(f2701,plain,
    ( spl5_191
    | ~ spl5_193
    | ~ spl5_46
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2614,f1949,f522,f2697,f2688])).

fof(f522,plain,
    ( spl5_46
  <=> ! [X7,X6] :
        ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(u1_struct_0(sK2),X6)
        | ~ r1_tarski(X7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f2614,plain,
    ( ! [X14] :
        ( ~ r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X14)
        | ~ r1_tarski(X14,sK3) )
    | ~ spl5_46
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f523])).

fof(f523,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(u1_struct_0(sK2),X6)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK3) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f522])).

fof(f2700,plain,
    ( ~ spl5_184
    | ~ spl5_193
    | ~ spl5_73
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2613,f1949,f1134,f2697,f2657])).

fof(f1134,plain,
    ( spl5_73
  <=> ! [X83] :
        ( ~ r1_tarski(X83,sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X83) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2613,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_73
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1135])).

fof(f1135,plain,
    ( ! [X83] :
        ( ~ r1_tarski(u1_struct_0(sK2),X83)
        | ~ r1_tarski(X83,sK4) )
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f2695,plain,
    ( spl5_192
    | ~ spl5_187
    | ~ spl5_113
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2612,f1949,f1761,f2669,f2693])).

fof(f2693,plain,
    ( spl5_192
  <=> ! [X13] :
        ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)
        | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X13),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f2669,plain,
    ( spl5_187
  <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f1761,plain,
    ( spl5_113
  <=> ! [X27,X26] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK3)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f2612,plain,
    ( ! [X13] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)
        | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X13),sK3) )
    | ~ spl5_113
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1762])).

fof(f1762,plain,
    ( ! [X26,X27] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27)
        | ~ r1_tarski(k2_zfmisc_1(X26,X27),sK3) )
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f2691,plain,
    ( ~ spl5_182
    | ~ spl5_187
    | ~ spl5_95
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2611,f1949,f1568,f2669,f2648])).

fof(f1568,plain,
    ( spl5_95
  <=> ! [X38] :
        ( ~ r1_tarski(X38,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f2611,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)
    | ~ spl5_95
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1569])).

fof(f1569,plain,
    ( ! [X38] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38)
        | ~ r1_tarski(X38,sK3) )
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f2690,plain,
    ( spl5_191
    | ~ spl5_187
    | ~ spl5_94
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2610,f1949,f1564,f2669,f2688])).

fof(f1564,plain,
    ( spl5_94
  <=> ! [X36,X35] :
        ( ~ r1_tarski(X35,X36)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35)
        | ~ r1_tarski(X36,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f2610,plain,
    ( ! [X12] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12)
        | ~ r1_tarski(X12,sK3) )
    | ~ spl5_94
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1565])).

fof(f1565,plain,
    ( ! [X35,X36] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35)
        | ~ r1_tarski(X35,X36)
        | ~ r1_tarski(X36,sK3) )
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f2686,plain,
    ( spl5_190
    | ~ spl5_187
    | ~ spl5_92
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2609,f1949,f1557,f2669,f2684])).

fof(f1557,plain,
    ( spl5_92
  <=> ! [X32,X31,X33] :
        ( ~ r1_tarski(X31,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32)
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X31) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f2609,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X10,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X11)
        | ~ r1_tarski(X11,X10) )
    | ~ spl5_92
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1558])).

fof(f1558,plain,
    ( ! [X33,X31,X32] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32)
        | ~ r1_tarski(X31,sK3)
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X31) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f2682,plain,
    ( ~ spl5_184
    | ~ spl5_187
    | ~ spl5_89
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2608,f1949,f1540,f2669,f2657])).

fof(f1540,plain,
    ( spl5_89
  <=> ! [X13] :
        ( ~ r1_tarski(X13,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f2608,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_89
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1541])).

fof(f1541,plain,
    ( ! [X13] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)
        | ~ r1_tarski(X13,sK4) )
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f2681,plain,
    ( spl5_185
    | ~ spl5_187
    | ~ spl5_88
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2607,f1949,f1536,f2669,f2662])).

fof(f1536,plain,
    ( spl5_88
  <=> ! [X11,X10] :
        ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10)
        | ~ r1_tarski(X11,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f2607,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X9)
        | ~ r1_tarski(X9,sK4) )
    | ~ spl5_88
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1537])).

fof(f1537,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10)
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,sK4) )
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f1536])).

fof(f2680,plain,
    ( spl5_189
    | ~ spl5_187
    | ~ spl5_87
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2606,f1949,f1532,f2669,f2678])).

fof(f1532,plain,
    ( spl5_87
  <=> ! [X7,X8,X6] :
        ( ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f2606,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X7,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X8)
        | ~ r1_tarski(X8,X7) )
    | ~ spl5_87
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1533])).

fof(f1533,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6) )
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f1532])).

fof(f2676,plain,
    ( spl5_188
    | ~ spl5_187
    | ~ spl5_85
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2605,f1949,f1525,f2669,f2674])).

fof(f2674,plain,
    ( spl5_188
  <=> ! [X5,X4,X6] :
        ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X4)
        | ~ r1_tarski(X6,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1525,plain,
    ( spl5_85
  <=> ! [X1,X3,X2,X4] :
        ( ~ r1_tarski(X1,X2)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X4,X1)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f2605,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X4)
        | ~ r1_tarski(X5,X6) )
    | ~ spl5_85
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f1526])).

fof(f1526,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X4,X1)
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f1525])).

fof(f2672,plain,
    ( spl5_186
    | ~ spl5_187
    | ~ spl5_63
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2604,f1949,f893,f2669,f2666])).

fof(f2666,plain,
    ( spl5_186
  <=> ! [X3] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X3),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f893,plain,
    ( spl5_63
  <=> ! [X13,X12] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12)
        | ~ r1_tarski(k2_zfmisc_1(X12,X13),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f2604,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X3),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X3) )
    | ~ spl5_63
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f894])).

fof(f894,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12)
        | ~ r1_tarski(k2_zfmisc_1(X12,X13),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f893])).

fof(f2664,plain,
    ( spl5_185
    | ~ spl5_183
    | ~ spl5_54
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2603,f1949,f635,f2652,f2662])).

fof(f2652,plain,
    ( spl5_183
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f635,plain,
    ( spl5_54
  <=> ! [X7,X6] :
        ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6)
        | ~ r1_tarski(X7,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f2603,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2)
        | ~ r1_tarski(X2,sK4) )
    | ~ spl5_54
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f636])).

fof(f636,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK4) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f635])).

fof(f2660,plain,
    ( ~ spl5_184
    | ~ spl5_183
    | ~ spl5_53
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2602,f1949,f619,f2652,f2657])).

fof(f619,plain,
    ( spl5_53
  <=> ! [X26] :
        ( ~ r1_tarski(X26,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f2602,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)
    | ~ spl5_53
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f620])).

fof(f620,plain,
    ( ! [X26] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26)
        | ~ r1_tarski(X26,sK4) )
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f619])).

fof(f2655,plain,
    ( ~ spl5_182
    | ~ spl5_183
    | ~ spl5_64
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f2601,f1949,f918,f2652,f2648])).

fof(f918,plain,
    ( spl5_64
  <=> ! [X24] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24)
        | ~ r1_tarski(X24,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2601,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)
    | ~ spl5_64
    | ~ spl5_115 ),
    inference(resolution,[],[f2283,f919])).

fof(f919,plain,
    ( ! [X24] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24)
        | ~ r1_tarski(X24,sK3) )
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f918])).

fof(f2565,plain,
    ( ~ spl5_137
    | spl5_181
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2543,f765,f2563,f2177])).

fof(f2177,plain,
    ( spl5_137
  <=> v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f2563,plain,
    ( spl5_181
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f765,plain,
    ( spl5_60
  <=> r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2543,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_60 ),
    inference(resolution,[],[f2199,f433])).

fof(f2199,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | r1_tarski(X9,u1_struct_0(sK0)) )
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f68])).

fof(f766,plain,
    ( r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f765])).

fof(f2561,plain,
    ( ~ spl5_137
    | spl5_180
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2541,f765,f2559,f2177])).

fof(f2559,plain,
    ( spl5_180
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f2541,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | ~ v1_relat_1(X12) )
    | ~ spl5_60 ),
    inference(resolution,[],[f2199,f252])).

fof(f2557,plain,
    ( ~ spl5_137
    | spl5_179
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2537,f765,f2555,f2177])).

fof(f2555,plain,
    ( spl5_179
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f2537,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5))
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_60 ),
    inference(resolution,[],[f2199,f426])).

fof(f2553,plain,
    ( ~ spl5_137
    | spl5_178
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2536,f765,f2551,f2177])).

fof(f2551,plain,
    ( spl5_178
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f2536,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | ~ v1_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)) )
    | ~ spl5_60 ),
    inference(resolution,[],[f2199,f251])).

fof(f2549,plain,
    ( ~ spl5_137
    | spl5_177
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2535,f765,f2547,f2177])).

fof(f2547,plain,
    ( spl5_177
  <=> ! [X1] : r1_tarski(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f2535,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_60 ),
    inference(resolution,[],[f2199,f59])).

fof(f2532,plain,
    ( ~ spl5_171
    | spl5_176
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2506,f761,f2530,f2510])).

fof(f2510,plain,
    ( spl5_171
  <=> v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f2530,plain,
    ( spl5_176
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f761,plain,
    ( spl5_59
  <=> r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f2506,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_59 ),
    inference(resolution,[],[f2141,f433])).

fof(f2141,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | r1_tarski(X10,u1_struct_0(sK2)) )
    | ~ spl5_59 ),
    inference(resolution,[],[f762,f68])).

fof(f762,plain,
    ( r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f761])).

fof(f2528,plain,
    ( ~ spl5_171
    | spl5_175
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2504,f761,f2526,f2510])).

fof(f2526,plain,
    ( spl5_175
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f2504,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | ~ v1_relat_1(X12) )
    | ~ spl5_59 ),
    inference(resolution,[],[f2141,f252])).

fof(f2524,plain,
    ( ~ spl5_171
    | spl5_174
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2500,f761,f2522,f2510])).

fof(f2522,plain,
    ( spl5_174
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f2500,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5))
        | ~ v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_59 ),
    inference(resolution,[],[f2141,f426])).

fof(f2520,plain,
    ( ~ spl5_171
    | spl5_173
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2499,f761,f2518,f2510])).

fof(f2518,plain,
    ( spl5_173
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f2499,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | ~ v1_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)) )
    | ~ spl5_59 ),
    inference(resolution,[],[f2141,f251])).

fof(f2516,plain,
    ( ~ spl5_171
    | spl5_172
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2498,f761,f2514,f2510])).

fof(f2514,plain,
    ( spl5_172
  <=> ! [X1] : r1_tarski(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f2498,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) )
    | ~ spl5_59 ),
    inference(resolution,[],[f2141,f59])).

fof(f2485,plain,
    ( ~ spl5_20
    | spl5_170
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f2481,f2450,f2483,f171])).

fof(f2483,plain,
    ( spl5_170
  <=> ! [X27,X26] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK4)
        | ~ r1_tarski(k2_relat_1(sK3),X27)
        | ~ r1_tarski(k1_relat_1(sK3),X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f2481,plain,
    ( ! [X26,X27] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK4)
        | ~ r1_tarski(k1_relat_1(sK3),X26)
        | ~ v1_relat_1(sK3)
        | ~ r1_tarski(k2_relat_1(sK3),X27) )
    | ~ spl5_166 ),
    inference(resolution,[],[f2451,f753])).

fof(f2465,plain,
    ( ~ spl5_169
    | spl5_168
    | ~ spl5_2
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2442,f2001,f77,f2457,f2461])).

fof(f2461,plain,
    ( spl5_169
  <=> r1_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f2457,plain,
    ( spl5_168
  <=> ! [X4,X6] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))),X6)
        | v4_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f2001,plain,
    ( spl5_123
  <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f2442,plain,
    ( ! [X10,X9] :
        ( ~ v1_relat_1(X9)
        | ~ v1_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2))))
        | v4_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
        | ~ r1_tarski(sK3,sK4)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2)))),X10) )
    | ~ spl5_2
    | ~ spl5_123 ),
    inference(resolution,[],[f2237,f780])).

fof(f2237,plain,
    ( ! [X11] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X11,k7_relat_1(sK3,u1_struct_0(sK2)))),sK3)
        | ~ v1_relat_1(X11) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f60])).

fof(f2012,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k7_relat_1(sK3,u1_struct_0(sK2)))
        | r1_tarski(X3,sK3) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2002,f68])).

fof(f2002,plain,
    ( r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3)
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f2464,plain,
    ( ~ spl5_169
    | spl5_167
    | ~ spl5_15
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2441,f2001,f144,f2453,f2461])).

fof(f2453,plain,
    ( spl5_167
  <=> ! [X1,X3] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))),X3)
        | v4_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
        | ~ v1_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f2441,plain,
    ( ! [X8,X7] :
        ( ~ v1_relat_1(X7)
        | ~ v1_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2))))
        | v4_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
        | ~ r1_tarski(sK3,sK4)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2)))),X8) )
    | ~ spl5_15
    | ~ spl5_123 ),
    inference(resolution,[],[f2237,f784])).

fof(f2459,plain,
    ( spl5_166
    | spl5_168
    | ~ spl5_2
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2440,f2001,f77,f2457,f2450])).

fof(f2440,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | ~ v1_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2))))
        | v4_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
        | ~ r1_tarski(sK3,X5)
        | ~ r1_tarski(X5,sK4)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))),X6) )
    | ~ spl5_2
    | ~ spl5_123 ),
    inference(resolution,[],[f2237,f779])).

fof(f2455,plain,
    ( spl5_166
    | spl5_167
    | ~ spl5_15
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2439,f2001,f144,f2453,f2450])).

fof(f2439,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2))))
        | v4_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
        | ~ r1_tarski(sK3,X2)
        | ~ r1_tarski(X2,sK4)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))),X3) )
    | ~ spl5_15
    | ~ spl5_123 ),
    inference(resolution,[],[f2237,f783])).

fof(f2433,plain,
    ( ~ spl5_160
    | spl5_165
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f2408,f2106,f2431,f2411])).

fof(f2411,plain,
    ( spl5_160
  <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f2431,plain,
    ( spl5_165
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f2106,plain,
    ( spl5_131
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f2408,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK2))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2131,f433])).

fof(f2131,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | r1_tarski(X10,u1_struct_0(sK2)) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2107,f68])).

fof(f2107,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f2429,plain,
    ( ~ spl5_160
    | spl5_164
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f2406,f2106,f2427,f2411])).

fof(f2427,plain,
    ( spl5_164
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f2406,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | ~ v1_relat_1(X12) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2131,f252])).

fof(f2425,plain,
    ( ~ spl5_160
    | spl5_163
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f2402,f2106,f2423,f2411])).

fof(f2423,plain,
    ( spl5_163
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f2402,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5))
        | ~ v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2131,f426])).

fof(f2421,plain,
    ( ~ spl5_160
    | spl5_162
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f2401,f2106,f2419,f2411])).

fof(f2419,plain,
    ( spl5_162
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f2401,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | ~ v1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2131,f251])).

fof(f2417,plain,
    ( ~ spl5_160
    | spl5_161
    | ~ spl5_131 ),
    inference(avatar_split_clause,[],[f2400,f2106,f2415,f2411])).

fof(f2415,plain,
    ( spl5_161
  <=> ! [X1] : r1_tarski(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f2400,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK2))
        | ~ v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_131 ),
    inference(resolution,[],[f2131,f59])).

fof(f2398,plain,
    ( ~ spl5_154
    | spl5_159
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2373,f1980,f2396,f2376])).

fof(f2376,plain,
    ( spl5_154
  <=> v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f2396,plain,
    ( spl5_159
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1980,plain,
    ( spl5_120
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2373,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK0))
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_120 ),
    inference(resolution,[],[f2050,f433])).

fof(f2050,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | r1_tarski(X9,u1_struct_0(sK0)) )
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f68])).

fof(f1981,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f1980])).

fof(f2394,plain,
    ( ~ spl5_154
    | spl5_158
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2371,f1980,f2392,f2376])).

fof(f2392,plain,
    ( spl5_158
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f2371,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | ~ v1_relat_1(X12) )
    | ~ spl5_120 ),
    inference(resolution,[],[f2050,f252])).

fof(f2390,plain,
    ( ~ spl5_154
    | spl5_157
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2367,f1980,f2388,f2376])).

fof(f2388,plain,
    ( spl5_157
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f2367,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5))
        | ~ v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_120 ),
    inference(resolution,[],[f2050,f426])).

fof(f2386,plain,
    ( ~ spl5_154
    | spl5_156
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2366,f1980,f2384,f2376])).

fof(f2384,plain,
    ( spl5_156
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f2366,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))
        | ~ v1_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)) )
    | ~ spl5_120 ),
    inference(resolution,[],[f2050,f251])).

fof(f2382,plain,
    ( ~ spl5_154
    | spl5_155
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2365,f1980,f2380,f2376])).

fof(f2380,plain,
    ( spl5_155
  <=> ! [X1] : r1_tarski(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f2365,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK0))
        | ~ v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) )
    | ~ spl5_120 ),
    inference(resolution,[],[f2050,f59])).

fof(f2335,plain,
    ( ~ spl5_153
    | ~ spl5_58
    | spl5_152
    | ~ spl5_16
    | ~ spl5_147 ),
    inference(avatar_split_clause,[],[f2325,f2299,f149,f2328,f757,f2332])).

fof(f2332,plain,
    ( spl5_153
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f757,plain,
    ( spl5_58
  <=> v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2328,plain,
    ( spl5_152
  <=> ! [X0] :
        ( v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0),X0)
        | ~ v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f2299,plain,
    ( spl5_147
  <=> ! [X1] : r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f2325,plain,
    ( ! [X11] :
        ( v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X11),X11)
        | ~ v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X11))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
        | ~ r1_tarski(sK3,sK3) )
    | ~ spl5_16
    | ~ spl5_147 ),
    inference(resolution,[],[f2300,f1366])).

fof(f2300,plain,
    ( ! [X1] : r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3)
    | ~ spl5_147 ),
    inference(avatar_component_clause,[],[f2299])).

fof(f2330,plain,
    ( ~ spl5_58
    | spl5_152
    | ~ spl5_16
    | ~ spl5_147 ),
    inference(avatar_split_clause,[],[f2318,f2299,f149,f2328,f757])).

fof(f2318,plain,
    ( ! [X0] :
        ( v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0),X0)
        | ~ v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_16
    | ~ spl5_147 ),
    inference(resolution,[],[f2300,f1367])).

fof(f1367,plain,
    ( ! [X24,X23] :
        ( ~ r1_tarski(k7_relat_1(X23,X24),sK3)
        | v4_relat_1(k7_relat_1(X23,X24),X24)
        | ~ v1_relat_1(k7_relat_1(X23,X24))
        | ~ v1_relat_1(X23) )
    | ~ spl5_16 ),
    inference(resolution,[],[f802,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( v5_relat_1(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f213,f204])).

fof(f2317,plain,
    ( ~ spl5_58
    | spl5_151
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f2295,f1990,f2315,f757])).

fof(f2315,plain,
    ( spl5_151
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X18))))),sK3)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f1990,plain,
    ( spl5_121
  <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f2295,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X18))))),sK3)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_121 ),
    inference(resolution,[],[f2019,f433])).

fof(f2019,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k2_tmap_1(sK1,sK0,sK3,sK2))
        | r1_tarski(X3,sK3) )
    | ~ spl5_121 ),
    inference(resolution,[],[f1991,f68])).

fof(f1991,plain,
    ( r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f1990])).

fof(f2313,plain,
    ( ~ spl5_58
    | spl5_150
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f2293,f1990,f2311,f757])).

fof(f2311,plain,
    ( spl5_150
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X13))),sK3)
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f2293,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X13))),sK3)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
        | ~ v1_relat_1(X12) )
    | ~ spl5_121 ),
    inference(resolution,[],[f2019,f252])).

fof(f2309,plain,
    ( ~ spl5_58
    | spl5_149
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f2289,f1990,f2307,f757])).

fof(f2307,plain,
    ( spl5_149
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5),X6),sK3)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f2289,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5),X6),sK3)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_121 ),
    inference(resolution,[],[f2019,f426])).

fof(f2305,plain,
    ( ~ spl5_58
    | spl5_148
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f2288,f1990,f2303,f757])).

fof(f2303,plain,
    ( spl5_148
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2),X3),sK3)
        | ~ v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f2288,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2),X3),sK3)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2)) )
    | ~ spl5_121 ),
    inference(resolution,[],[f2019,f251])).

fof(f2301,plain,
    ( ~ spl5_58
    | spl5_147
    | ~ spl5_121 ),
    inference(avatar_split_clause,[],[f2287,f1990,f2299,f757])).

fof(f2287,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_121 ),
    inference(resolution,[],[f2019,f59])).

fof(f2277,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | spl5_117
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f2276,f742,f1959,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1959,plain,
    ( spl5_117
  <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f742,plain,
    ( spl5_56
  <=> m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f2276,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_56 ),
    inference(superposition,[],[f743,f1508])).

fof(f743,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f742])).

fof(f2271,plain,
    ( ~ spl5_120
    | ~ spl5_116
    | ~ spl5_131
    | spl5_115 ),
    inference(avatar_split_clause,[],[f2270,f1949,f2106,f1954,f1980])).

fof(f2270,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0))
    | spl5_115 ),
    inference(resolution,[],[f1951,f753])).

fof(f1951,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | spl5_115 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f2261,plain,
    ( ~ spl5_116
    | spl5_146
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2240,f2001,f2259,f1954])).

fof(f2259,plain,
    ( spl5_146
  <=> ! [X16,X18,X17] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),sK3)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f2240,plain,
    ( ! [X17,X18,X16] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),sK3)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f433])).

fof(f2257,plain,
    ( ~ spl5_116
    | spl5_145
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2238,f2001,f2255,f1954])).

fof(f2255,plain,
    ( spl5_145
  <=> ! [X13,X12] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),sK3)
        | ~ v1_relat_1(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f2238,plain,
    ( ! [X12,X13] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(X12) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f252])).

fof(f2253,plain,
    ( ~ spl5_116
    | spl5_144
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2234,f2001,f2251,f1954])).

fof(f2251,plain,
    ( spl5_144
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),sK3)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f2234,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),sK3)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f426])).

fof(f2249,plain,
    ( ~ spl5_116
    | spl5_143
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2233,f2001,f2247,f1954])).

fof(f2247,plain,
    ( spl5_143
  <=> ! [X3,X2] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),sK3)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f2233,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f251])).

fof(f2245,plain,
    ( ~ spl5_116
    | spl5_142
    | ~ spl5_123 ),
    inference(avatar_split_clause,[],[f2232,f2001,f2243,f1954])).

fof(f2243,plain,
    ( spl5_142
  <=> ! [X1] : r1_tarski(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f2232,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_123 ),
    inference(resolution,[],[f2012,f59])).

fof(f2215,plain,
    ( ~ spl5_58
    | spl5_141
    | spl5_128
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2195,f765,f144,f2075,f2208,f757])).

fof(f2208,plain,
    ( spl5_141
  <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f2195,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(u1_struct_0(sK0),X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK4)
        | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f659])).

fof(f2214,plain,
    ( ~ spl5_58
    | spl5_140
    | spl5_128
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2194,f765,f77,f2075,f2203,f757])).

fof(f2203,plain,
    ( spl5_140
  <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f2194,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(u1_struct_0(sK0),X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK4)
        | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f590])).

fof(f2213,plain,
    ( ~ spl5_58
    | spl5_141
    | spl5_127
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2193,f765,f144,f2070,f2208,f757])).

fof(f2193,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4)
        | ~ r1_tarski(u1_struct_0(sK0),X1)
        | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f373])).

fof(f2212,plain,
    ( ~ spl5_58
    | spl5_140
    | spl5_127
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2192,f765,f77,f2070,f2203,f757])).

fof(f2192,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(u1_struct_0(sK0),X0)
        | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f343])).

fof(f2211,plain,
    ( ~ spl5_58
    | spl5_141
    | ~ spl5_125
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2191,f765,f144,f2060,f2208,f757])).

fof(f2060,plain,
    ( spl5_125
  <=> r1_tarski(u1_struct_0(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f2191,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK4)
    | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1))
    | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl5_15
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f247])).

fof(f2206,plain,
    ( ~ spl5_58
    | spl5_140
    | ~ spl5_125
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2190,f765,f77,f2060,f2203,f757])).

fof(f2190,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK4)
    | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))
    | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl5_2
    | ~ spl5_60 ),
    inference(resolution,[],[f766,f242])).

fof(f2187,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | spl5_139
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f2168,f2149,f2185,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f2185,plain,
    ( spl5_139
  <=> ! [X0] : ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f2149,plain,
    ( spl5_134
  <=> ! [X6] : ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f2168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X0)
        | ~ m1_pre_topc(sK2,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_134 ),
    inference(superposition,[],[f2150,f1508])).

fof(f2150,plain,
    ( ! [X6] : ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6)
    | ~ spl5_134 ),
    inference(avatar_component_clause,[],[f2149])).

fof(f2183,plain,
    ( spl5_136
    | ~ spl5_137
    | spl5_138
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f2167,f2149,f2181,f2177,f2174])).

fof(f2174,plain,
    ( spl5_136
  <=> ! [X28] : ~ r1_tarski(k2_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f2181,plain,
    ( spl5_138
  <=> ! [X27] : ~ r1_tarski(k1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f2167,plain,
    ( ! [X28,X27] :
        ( ~ r1_tarski(k1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X27)
        | ~ v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))
        | ~ r1_tarski(k2_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X28) )
    | ~ spl5_134 ),
    inference(resolution,[],[f2150,f753])).

fof(f2172,plain,
    ( ~ spl5_58
    | spl5_135
    | ~ spl5_134 ),
    inference(avatar_split_clause,[],[f2152,f2149,f2170,f757])).

fof(f2170,plain,
    ( spl5_135
  <=> ! [X0] : ~ v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f2152,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) )
    | ~ spl5_134 ),
    inference(resolution,[],[f2150,f61])).

fof(f2151,plain,
    ( spl5_133
    | ~ spl5_58
    | spl5_134
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f2137,f761,f2149,f757,f2145])).

fof(f2145,plain,
    ( spl5_133
  <=> v4_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f2137,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6)
        | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
        | v4_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) )
    | ~ spl5_59 ),
    inference(resolution,[],[f762,f751])).

fof(f2122,plain,
    ( ~ spl5_20
    | spl5_131 ),
    inference(avatar_split_clause,[],[f2116,f2106,f171])).

fof(f2116,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_131 ),
    inference(resolution,[],[f2108,f60])).

fof(f2108,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | spl5_131 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f2115,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_132
    | spl5_130 ),
    inference(avatar_split_clause,[],[f2110,f2101,f2112,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f2112,plain,
    ( spl5_132
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f2101,plain,
    ( spl5_130
  <=> r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f2110,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),sK4)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_130 ),
    inference(superposition,[],[f2103,f1508])).

fof(f2103,plain,
    ( ~ r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4)
    | spl5_130 ),
    inference(avatar_component_clause,[],[f2101])).

fof(f2109,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_131
    | spl5_59 ),
    inference(avatar_split_clause,[],[f2099,f761,f2106,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f2099,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_59 ),
    inference(superposition,[],[f763,f1508])).

fof(f763,plain,
    ( ~ r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2))
    | spl5_59 ),
    inference(avatar_component_clause,[],[f761])).

fof(f2104,plain,
    ( ~ spl5_130
    | ~ spl5_2
    | spl5_59 ),
    inference(avatar_split_clause,[],[f2098,f761,f77,f2101])).

fof(f2098,plain,
    ( ~ r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4)
    | ~ spl5_2
    | spl5_59 ),
    inference(resolution,[],[f763,f214])).

fof(f2083,plain,
    ( ~ spl5_20
    | spl5_129
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2054,f1980,f2080,f171])).

fof(f2080,plain,
    ( spl5_129
  <=> v4_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f2054,plain,
    ( v4_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f789])).

fof(f2078,plain,
    ( ~ spl5_116
    | spl5_126
    | spl5_128
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2046,f1980,f144,f2075,f2065,f1954])).

fof(f2065,plain,
    ( spl5_126
  <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f2046,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(u1_struct_0(sK0),X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK4)
        | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f659])).

fof(f2077,plain,
    ( ~ spl5_116
    | spl5_124
    | spl5_128
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2045,f1980,f77,f2075,f2056,f1954])).

fof(f2056,plain,
    ( spl5_124
  <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f2045,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(u1_struct_0(sK0),X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK4)
        | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f590])).

fof(f2073,plain,
    ( ~ spl5_116
    | spl5_126
    | spl5_127
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2044,f1980,f144,f2070,f2065,f1954])).

fof(f2044,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4)
        | ~ r1_tarski(u1_struct_0(sK0),X1)
        | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f373])).

fof(f2072,plain,
    ( ~ spl5_116
    | spl5_124
    | spl5_127
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2042,f1980,f77,f2070,f2056,f1954])).

fof(f2042,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(u1_struct_0(sK0),X0)
        | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) )
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f343])).

fof(f2068,plain,
    ( ~ spl5_116
    | spl5_126
    | ~ spl5_125
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2041,f1980,f144,f2060,f2065,f1954])).

fof(f2041,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK4)
    | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl5_15
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f247])).

fof(f2063,plain,
    ( ~ spl5_116
    | spl5_124
    | ~ spl5_125
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2040,f1980,f77,f2060,f2056,f1954])).

fof(f2040,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK4)
    | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl5_2
    | ~ spl5_120 ),
    inference(resolution,[],[f1981,f242])).

fof(f2038,plain,
    ( ~ spl5_116
    | ~ spl5_122
    | spl5_120 ),
    inference(avatar_split_clause,[],[f2037,f1980,f1995,f1954])).

fof(f1995,plain,
    ( spl5_122
  <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f2037,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl5_120 ),
    inference(resolution,[],[f1982,f61])).

fof(f1982,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0))
    | spl5_120 ),
    inference(avatar_component_clause,[],[f1980])).

fof(f2026,plain,
    ( ~ spl5_123
    | ~ spl5_16
    | spl5_122 ),
    inference(avatar_split_clause,[],[f2025,f1995,f149,f2001])).

fof(f2025,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3)
    | ~ spl5_16
    | spl5_122 ),
    inference(resolution,[],[f1997,f227])).

fof(f1997,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0))
    | spl5_122 ),
    inference(avatar_component_clause,[],[f1995])).

fof(f2006,plain,
    ( ~ spl5_20
    | spl5_123 ),
    inference(avatar_split_clause,[],[f2005,f2001,f171])).

fof(f2005,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_123 ),
    inference(resolution,[],[f2003,f59])).

fof(f2003,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3)
    | spl5_123 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f2004,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_123
    | spl5_121 ),
    inference(avatar_split_clause,[],[f1999,f1990,f2001,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1999,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_121 ),
    inference(superposition,[],[f1992,f1508])).

fof(f1992,plain,
    ( ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | spl5_121 ),
    inference(avatar_component_clause,[],[f1990])).

fof(f1998,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_122
    | spl5_119 ),
    inference(avatar_split_clause,[],[f1988,f1975,f1995,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1975,plain,
    ( spl5_119
  <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f1988,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_119 ),
    inference(superposition,[],[f1977,f1508])).

fof(f1977,plain,
    ( ~ v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0))
    | spl5_119 ),
    inference(avatar_component_clause,[],[f1975])).

fof(f1993,plain,
    ( ~ spl5_121
    | ~ spl5_16
    | spl5_119 ),
    inference(avatar_split_clause,[],[f1987,f1975,f149,f1990])).

fof(f1987,plain,
    ( ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ spl5_16
    | spl5_119 ),
    inference(resolution,[],[f1977,f227])).

fof(f1983,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_120
    | spl5_60 ),
    inference(avatar_split_clause,[],[f1973,f765,f1980,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1973,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_60 ),
    inference(superposition,[],[f767,f1508])).

fof(f767,plain,
    ( ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_60 ),
    inference(avatar_component_clause,[],[f765])).

fof(f1978,plain,
    ( ~ spl5_58
    | ~ spl5_119
    | spl5_60 ),
    inference(avatar_split_clause,[],[f1972,f765,f1975,f757])).

fof(f1972,plain,
    ( ~ v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_60 ),
    inference(resolution,[],[f767,f61])).

fof(f1970,plain,
    ( ~ spl5_60
    | ~ spl5_58
    | ~ spl5_59
    | spl5_61 ),
    inference(avatar_split_clause,[],[f872,f770,f761,f757,f765])).

fof(f770,plain,
    ( spl5_61
  <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f872,plain,
    ( ~ r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2))
    | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_61 ),
    inference(resolution,[],[f753,f772])).

fof(f772,plain,
    ( ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f770])).

fof(f1969,plain,
    ( ~ spl5_20
    | spl5_116 ),
    inference(avatar_split_clause,[],[f1968,f1954,f171])).

fof(f1968,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_116 ),
    inference(resolution,[],[f1956,f181])).

fof(f1956,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl5_116 ),
    inference(avatar_component_clause,[],[f1954])).

fof(f1967,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_118
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1947,f72,f1964,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1964,plain,
    ( spl5_118
  <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f72,plain,
    ( spl5_1
  <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1947,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(superposition,[],[f74,f1508])).

fof(f74,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f1962,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_117
    | spl5_56 ),
    inference(avatar_split_clause,[],[f1946,f742,f1959,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1946,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_56 ),
    inference(superposition,[],[f744,f1508])).

fof(f744,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl5_56 ),
    inference(avatar_component_clause,[],[f742])).

fof(f1957,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_116
    | spl5_58 ),
    inference(avatar_split_clause,[],[f1945,f757,f1954,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1945,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_58 ),
    inference(superposition,[],[f759,f1508])).

fof(f759,plain,
    ( ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_58 ),
    inference(avatar_component_clause,[],[f757])).

fof(f1952,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_115
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1944,f770,f1949,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).

fof(f1944,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_61 ),
    inference(superposition,[],[f772,f1508])).

fof(f1899,plain,
    ( ~ spl5_20
    | spl5_114
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1889,f149,f1897,f171])).

fof(f1897,plain,
    ( spl5_114
  <=> ! [X73,X71,X72] :
        ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73))
        | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1889,plain,
    ( ! [X72,X71,X73] :
        ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72))
        | ~ v1_relat_1(sK3)
        | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73)) )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f1887])).

fof(f1887,plain,
    ( ! [X72,X71,X73] :
        ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72))
        | ~ v1_relat_1(sK3)
        | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f426,f1367])).

fof(f1797,plain,
    ( ~ spl5_96
    | spl5_78
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1792,f1525,f149,f1186,f1572])).

fof(f1572,plain,
    ( spl5_96
  <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1186,plain,
    ( spl5_78
  <=> ! [X7,X8,X6] :
        ( ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1792,plain,
    ( ! [X66,X67,X65] :
        ( ~ r1_tarski(X65,X66)
        | ~ r1_tarski(X67,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X65)
        | ~ r1_tarski(X66,X67)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3) )
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(resolution,[],[f1526,f213])).

fof(f1796,plain,
    ( spl5_95
    | spl5_78
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1791,f1525,f149,f1186,f1568])).

fof(f1791,plain,
    ( ! [X61,X64,X62,X63] :
        ( ~ r1_tarski(X61,X62)
        | ~ r1_tarski(X63,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X61)
        | ~ r1_tarski(X62,X63)
        | ~ r1_tarski(X64,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X64) )
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(resolution,[],[f1526,f229])).

fof(f1795,plain,
    ( spl5_94
    | spl5_78
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1790,f1525,f149,f1186,f1564])).

fof(f1790,plain,
    ( ! [X59,X57,X60,X58,X56] :
        ( ~ r1_tarski(X56,X57)
        | ~ r1_tarski(X58,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X56)
        | ~ r1_tarski(X57,X58)
        | ~ r1_tarski(X59,X60)
        | ~ r1_tarski(X60,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X59) )
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(resolution,[],[f1526,f277])).

fof(f277,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(X6,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(X4,sK3)
        | ~ r1_tarski(X6,X5) )
    | ~ spl5_16 ),
    inference(resolution,[],[f229,f68])).

fof(f1794,plain,
    ( spl5_92
    | spl5_78
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f1789,f1525,f149,f1186,f1557])).

fof(f1789,plain,
    ( ! [X54,X52,X50,X55,X53,X51] :
        ( ~ r1_tarski(X50,X51)
        | ~ r1_tarski(X52,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X50)
        | ~ r1_tarski(X51,X52)
        | ~ r1_tarski(X53,sK3)
        | ~ r1_tarski(X54,X55)
        | ~ r1_tarski(X55,X53)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X54) )
    | ~ spl5_16
    | ~ spl5_85 ),
    inference(resolution,[],[f1526,f439])).

fof(f439,plain,
    ( ! [X12,X10,X11,X9] :
        ( r1_tarski(X12,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(X10,sK3)
        | ~ r1_tarski(X11,X9)
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X12,X11) )
    | ~ spl5_16 ),
    inference(resolution,[],[f277,f68])).

fof(f1763,plain,
    ( ~ spl5_19
    | spl5_113
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f1758,f918,f1761,f167])).

fof(f167,plain,
    ( spl5_19
  <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1758,plain,
    ( ! [X26,X27] :
        ( ~ r1_tarski(k2_zfmisc_1(X26,X27),sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27) )
    | ~ spl5_64 ),
    inference(resolution,[],[f919,f753])).

fof(f1743,plain,
    ( spl5_64
    | spl5_76
    | ~ spl5_16
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f1737,f616,f149,f1161,f918])).

fof(f1161,plain,
    ( spl5_76
  <=> ! [X49,X51,X50,X52] :
        ( v5_relat_1(X49,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X49),X51)
        | ~ r1_tarski(X50,sK3)
        | ~ r1_tarski(X51,X52)
        | ~ r1_tarski(X52,X50)
        | ~ v1_relat_1(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f616,plain,
    ( spl5_52
  <=> ! [X27,X29,X28] :
        ( v5_relat_1(X27,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X27),X28)
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,sK3)
        | ~ v1_relat_1(X27) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1737,plain,
    ( ! [X47,X45,X43,X46,X44] :
        ( v5_relat_1(X43,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X44)
        | ~ r1_tarski(X44,sK3)
        | ~ v1_relat_1(X43)
        | ~ r1_tarski(X45,sK3)
        | ~ r1_tarski(X46,X47)
        | ~ r1_tarski(X47,X45)
        | ~ r1_tarski(k2_relat_1(X43),X46) )
    | ~ spl5_16
    | ~ spl5_52 ),
    inference(resolution,[],[f617,f439])).

fof(f617,plain,
    ( ! [X28,X29,X27] :
        ( ~ r1_tarski(k2_relat_1(X27),X28)
        | v5_relat_1(X27,u1_struct_0(sK2))
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,sK3)
        | ~ v1_relat_1(X27) )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f616])).

fof(f1641,plain,
    ( spl5_112
    | spl5_53
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f669,f149,f144,f619,f1639])).

fof(f1639,plain,
    ( spl5_112
  <=> ! [X32,X34,X33] :
        ( v5_relat_1(X32,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X32),X33)
        | ~ r1_tarski(X33,X34)
        | ~ r1_tarski(X34,sK3)
        | ~ v1_relat_1(X32) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f669,plain,
    ( ! [X33,X31,X34,X32] :
        ( ~ r1_tarski(X31,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X31)
        | v5_relat_1(X32,u1_struct_0(sK1))
        | ~ v1_relat_1(X32)
        | ~ r1_tarski(X33,X34)
        | ~ r1_tarski(X34,sK3)
        | ~ r1_tarski(k2_relat_1(X32),X33) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f373,f277])).

fof(f1637,plain,
    ( spl5_111
    | spl5_53
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f670,f149,f144,f619,f1635])).

fof(f1635,plain,
    ( spl5_111
  <=> ! [X36,X37] :
        ( v5_relat_1(X36,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X36),X37)
        | ~ r1_tarski(X37,sK3)
        | ~ v1_relat_1(X36) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f670,plain,
    ( ! [X37,X35,X36] :
        ( ~ r1_tarski(X35,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X35)
        | v5_relat_1(X36,u1_struct_0(sK1))
        | ~ v1_relat_1(X36)
        | ~ r1_tarski(X37,sK3)
        | ~ r1_tarski(k2_relat_1(X36),X37) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f373,f229])).

fof(f1633,plain,
    ( spl5_110
    | spl5_53
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f671,f149,f144,f619,f1631])).

fof(f1631,plain,
    ( spl5_110
  <=> ! [X39] :
        ( v5_relat_1(X39,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X39),sK3)
        | ~ v1_relat_1(X39) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f671,plain,
    ( ! [X39,X38] :
        ( ~ r1_tarski(X38,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X38)
        | v5_relat_1(X39,u1_struct_0(sK1))
        | ~ v1_relat_1(X39)
        | ~ r1_tarski(k2_relat_1(X39),sK3) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f373,f213])).

fof(f1629,plain,
    ( spl5_53
    | spl5_109
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f906,f149,f144,f1627,f619])).

fof(f1627,plain,
    ( spl5_109
  <=> ! [X40,X38,X41,X39] :
        ( ~ r1_tarski(X38,sK3)
        | ~ v1_relat_1(X41)
        | v5_relat_1(X41,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X41),X39)
        | ~ r1_tarski(X39,X40)
        | ~ r1_tarski(X40,X38) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f906,plain,
    ( ! [X39,X41,X38,X42,X40] :
        ( ~ r1_tarski(X38,sK3)
        | ~ r1_tarski(X39,X40)
        | ~ r1_tarski(X40,X38)
        | ~ r1_tarski(k2_relat_1(X41),X39)
        | ~ r1_tarski(X42,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X42)
        | v5_relat_1(X41,u1_struct_0(sK1))
        | ~ v1_relat_1(X41) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f439,f373])).

fof(f1625,plain,
    ( spl5_53
    | spl5_76
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f907,f149,f77,f1161,f619])).

fof(f907,plain,
    ( ! [X47,X45,X43,X46,X44] :
        ( ~ r1_tarski(X43,sK3)
        | ~ r1_tarski(X44,X45)
        | ~ r1_tarski(X45,X43)
        | ~ r1_tarski(k2_relat_1(X46),X44)
        | ~ r1_tarski(X47,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X47)
        | v5_relat_1(X46,u1_struct_0(sK2))
        | ~ v1_relat_1(X46) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f439,f343])).

fof(f1624,plain,
    ( spl5_108
    | spl5_53
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1176,f635,f149,f619,f1622])).

fof(f1622,plain,
    ( spl5_108
  <=> ! [X27,X26,X28] :
        ( ~ r1_tarski(X26,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X27)
        | ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X26) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1176,plain,
    ( ! [X28,X26,X27,X25] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X25)
        | ~ r1_tarski(X25,sK4)
        | ~ r1_tarski(X26,sK3)
        | ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X26)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X27) )
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f439])).

fof(f1620,plain,
    ( spl5_107
    | spl5_53
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1177,f635,f149,f619,f1618])).

fof(f1618,plain,
    ( spl5_107
  <=> ! [X31,X30] :
        ( ~ r1_tarski(X30,X31)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30)
        | ~ r1_tarski(X31,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f1177,plain,
    ( ! [X30,X31,X29] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X29)
        | ~ r1_tarski(X29,sK4)
        | ~ r1_tarski(X30,X31)
        | ~ r1_tarski(X31,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30) )
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f277])).

fof(f1616,plain,
    ( spl5_64
    | spl5_53
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1178,f635,f149,f619,f918])).

fof(f1178,plain,
    ( ! [X33,X32] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X32)
        | ~ r1_tarski(X32,sK4)
        | ~ r1_tarski(X33,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X33) )
    | ~ spl5_16
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f229])).

fof(f1615,plain,
    ( spl5_53
    | spl5_106
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1447,f149,f77,f1613,f619])).

fof(f1613,plain,
    ( spl5_106
  <=> ! [X73,X69,X71,X72,X74] :
        ( ~ v1_relat_1(X69)
        | ~ r1_tarski(k1_relat_1(X69),X73)
        | ~ r1_tarski(X72,sK3)
        | ~ r1_tarski(X73,X74)
        | ~ r1_tarski(X74,X72)
        | ~ r1_tarski(k2_relat_1(X69),X71)
        | v4_relat_1(X69,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1447,plain,
    ( ! [X70,X74,X72,X71,X69,X73] :
        ( ~ v1_relat_1(X69)
        | v4_relat_1(X69,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X70)
        | ~ r1_tarski(X70,sK4)
        | ~ r1_tarski(k2_relat_1(X69),X71)
        | ~ r1_tarski(X72,sK3)
        | ~ r1_tarski(X73,X74)
        | ~ r1_tarski(X74,X72)
        | ~ r1_tarski(k1_relat_1(X69),X73) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f779,f439])).

fof(f1611,plain,
    ( spl5_53
    | spl5_105
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1448,f149,f77,f1609,f619])).

fof(f1609,plain,
    ( spl5_105
  <=> ! [X75,X77,X79,X78] :
        ( ~ v1_relat_1(X75)
        | ~ r1_tarski(k1_relat_1(X75),X78)
        | ~ r1_tarski(X78,X79)
        | ~ r1_tarski(X79,sK3)
        | ~ r1_tarski(k2_relat_1(X75),X77)
        | v4_relat_1(X75,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f1448,plain,
    ( ! [X78,X76,X79,X77,X75] :
        ( ~ v1_relat_1(X75)
        | v4_relat_1(X75,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X76)
        | ~ r1_tarski(X76,sK4)
        | ~ r1_tarski(k2_relat_1(X75),X77)
        | ~ r1_tarski(X78,X79)
        | ~ r1_tarski(X79,sK3)
        | ~ r1_tarski(k1_relat_1(X75),X78) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f779,f277])).

fof(f1607,plain,
    ( spl5_53
    | spl5_104
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1449,f149,f77,f1605,f619])).

fof(f1605,plain,
    ( spl5_104
  <=> ! [X82,X83,X80] :
        ( ~ v1_relat_1(X80)
        | ~ r1_tarski(k1_relat_1(X80),X83)
        | ~ r1_tarski(X83,sK3)
        | ~ r1_tarski(k2_relat_1(X80),X82)
        | v4_relat_1(X80,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1449,plain,
    ( ! [X80,X83,X81,X82] :
        ( ~ v1_relat_1(X80)
        | v4_relat_1(X80,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X81)
        | ~ r1_tarski(X81,sK4)
        | ~ r1_tarski(k2_relat_1(X80),X82)
        | ~ r1_tarski(X83,sK3)
        | ~ r1_tarski(k1_relat_1(X80),X83) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f779,f229])).

fof(f1603,plain,
    ( spl5_53
    | spl5_103
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1450,f149,f77,f1601,f619])).

fof(f1601,plain,
    ( spl5_103
  <=> ! [X84,X86] :
        ( ~ v1_relat_1(X84)
        | ~ r1_tarski(k1_relat_1(X84),sK3)
        | ~ r1_tarski(k2_relat_1(X84),X86)
        | v4_relat_1(X84,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f1450,plain,
    ( ! [X85,X86,X84] :
        ( ~ v1_relat_1(X84)
        | v4_relat_1(X84,u1_struct_0(sK2))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X85)
        | ~ r1_tarski(X85,sK4)
        | ~ r1_tarski(k2_relat_1(X84),X86)
        | ~ r1_tarski(k1_relat_1(X84),sK3) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f779,f213])).

fof(f1599,plain,
    ( spl5_53
    | spl5_102
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1466,f149,f144,f1597,f619])).

fof(f1597,plain,
    ( spl5_102
  <=> ! [X73,X69,X71,X72,X74] :
        ( ~ v1_relat_1(X69)
        | ~ r1_tarski(k1_relat_1(X69),X73)
        | ~ r1_tarski(X72,sK3)
        | ~ r1_tarski(X73,X74)
        | ~ r1_tarski(X74,X72)
        | ~ r1_tarski(k2_relat_1(X69),X71)
        | v4_relat_1(X69,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1466,plain,
    ( ! [X70,X74,X72,X71,X69,X73] :
        ( ~ v1_relat_1(X69)
        | v4_relat_1(X69,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X70)
        | ~ r1_tarski(X70,sK4)
        | ~ r1_tarski(k2_relat_1(X69),X71)
        | ~ r1_tarski(X72,sK3)
        | ~ r1_tarski(X73,X74)
        | ~ r1_tarski(X74,X72)
        | ~ r1_tarski(k1_relat_1(X69),X73) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f783,f439])).

fof(f1595,plain,
    ( spl5_53
    | spl5_101
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1467,f149,f144,f1593,f619])).

fof(f1593,plain,
    ( spl5_101
  <=> ! [X75,X77,X79,X78] :
        ( ~ v1_relat_1(X75)
        | ~ r1_tarski(k1_relat_1(X75),X78)
        | ~ r1_tarski(X78,X79)
        | ~ r1_tarski(X79,sK3)
        | ~ r1_tarski(k2_relat_1(X75),X77)
        | v4_relat_1(X75,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f1467,plain,
    ( ! [X78,X76,X79,X77,X75] :
        ( ~ v1_relat_1(X75)
        | v4_relat_1(X75,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X76)
        | ~ r1_tarski(X76,sK4)
        | ~ r1_tarski(k2_relat_1(X75),X77)
        | ~ r1_tarski(X78,X79)
        | ~ r1_tarski(X79,sK3)
        | ~ r1_tarski(k1_relat_1(X75),X78) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f783,f277])).

fof(f1591,plain,
    ( spl5_53
    | spl5_100
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1468,f149,f144,f1589,f619])).

fof(f1589,plain,
    ( spl5_100
  <=> ! [X82,X83,X80] :
        ( ~ v1_relat_1(X80)
        | ~ r1_tarski(k1_relat_1(X80),X83)
        | ~ r1_tarski(X83,sK3)
        | ~ r1_tarski(k2_relat_1(X80),X82)
        | v4_relat_1(X80,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f1468,plain,
    ( ! [X80,X83,X81,X82] :
        ( ~ v1_relat_1(X80)
        | v4_relat_1(X80,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X81)
        | ~ r1_tarski(X81,sK4)
        | ~ r1_tarski(k2_relat_1(X80),X82)
        | ~ r1_tarski(X83,sK3)
        | ~ r1_tarski(k1_relat_1(X80),X83) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f783,f229])).

fof(f1587,plain,
    ( spl5_53
    | spl5_99
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1469,f149,f144,f1585,f619])).

fof(f1585,plain,
    ( spl5_99
  <=> ! [X84,X86] :
        ( ~ v1_relat_1(X84)
        | ~ r1_tarski(k1_relat_1(X84),sK3)
        | ~ r1_tarski(k2_relat_1(X84),X86)
        | v4_relat_1(X84,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f1469,plain,
    ( ! [X85,X86,X84] :
        ( ~ v1_relat_1(X84)
        | v4_relat_1(X84,u1_struct_0(sK1))
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X85)
        | ~ r1_tarski(X85,sK4)
        | ~ r1_tarski(k2_relat_1(X84),X86)
        | ~ r1_tarski(k1_relat_1(X84),sK3) )
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f783,f213])).

fof(f1583,plain,
    ( ~ spl5_97
    | spl5_98
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1523,f893,f1581,f1577])).

fof(f1577,plain,
    ( spl5_97
  <=> v1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1581,plain,
    ( spl5_98
  <=> ! [X40,X42,X41] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42),sK4)
        | ~ r1_tarski(k2_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X41)
        | ~ r1_tarski(k1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X40)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X42) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f1523,plain,
    ( ! [X41,X42,X40] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X42)
        | ~ r1_tarski(k1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X40)
        | ~ v1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ r1_tarski(k2_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X41) )
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f753])).

fof(f1575,plain,
    ( ~ spl5_96
    | spl5_93
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1522,f893,f149,f1560,f1572])).

fof(f1560,plain,
    ( spl5_93
  <=> ! [X30] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X30) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1522,plain,
    ( ! [X39] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X39),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X39)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3) )
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f213])).

fof(f1570,plain,
    ( spl5_95
    | spl5_93
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1521,f893,f149,f1560,f1568])).

fof(f1521,plain,
    ( ! [X37,X38] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X37),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X37)
        | ~ r1_tarski(X38,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38) )
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f229])).

fof(f1566,plain,
    ( spl5_94
    | spl5_93
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1520,f893,f149,f1560,f1564])).

fof(f1520,plain,
    ( ! [X35,X36,X34] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X34),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X34)
        | ~ r1_tarski(X35,X36)
        | ~ r1_tarski(X36,sK3)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35) )
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f277])).

fof(f1562,plain,
    ( spl5_92
    | spl5_93
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1519,f893,f149,f1560,f1557])).

fof(f1519,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X30)
        | ~ r1_tarski(X31,sK3)
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X31)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32) )
    | ~ spl5_16
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f439])).

fof(f1555,plain,
    ( ~ spl5_90
    | spl5_91
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1518,f893,f144,f1549,f1544])).

fof(f1544,plain,
    ( spl5_90
  <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f1549,plain,
    ( spl5_91
  <=> ! [X15] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X15),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f1518,plain,
    ( ! [X29] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X29),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X29)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4) )
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f215])).

fof(f1554,plain,
    ( spl5_89
    | spl5_91
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1517,f893,f144,f1549,f1540])).

fof(f1517,plain,
    ( ! [X28,X27] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X27),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27)
        | ~ r1_tarski(X28,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X28) )
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f219])).

fof(f1553,plain,
    ( spl5_88
    | spl5_91
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1516,f893,f144,f1549,f1536])).

fof(f1516,plain,
    ( ! [X26,X24,X25] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X24),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X24)
        | ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X25) )
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f245])).

fof(f1552,plain,
    ( spl5_87
    | spl5_91
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1515,f893,f144,f1549,f1532])).

fof(f1515,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X20),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X20)
        | ~ r1_tarski(X21,sK4)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X22) )
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f370])).

fof(f1551,plain,
    ( spl5_85
    | spl5_91
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1514,f893,f144,f1549,f1525])).

fof(f1514,plain,
    ( ! [X19,X17,X15,X18,X16] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X15),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X15)
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X19,X16)
        | ~ r1_tarski(X18,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X19) )
    | ~ spl5_15
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f654])).

fof(f654,plain,
    ( ! [X24,X23,X21,X25,X22] :
        ( r1_tarski(X25,u1_struct_0(sK1))
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(X24,X22)
        | ~ r1_tarski(X21,sK4)
        | ~ r1_tarski(X25,X24) )
    | ~ spl5_15 ),
    inference(resolution,[],[f370,f68])).

fof(f1547,plain,
    ( ~ spl5_90
    | spl5_86
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1513,f893,f77,f1528,f1544])).

fof(f1528,plain,
    ( spl5_86
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X0),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1513,plain,
    ( ! [X14] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X14),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X14)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4) )
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f214])).

fof(f1542,plain,
    ( spl5_89
    | spl5_86
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1512,f893,f77,f1528,f1540])).

fof(f1512,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X12),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12)
        | ~ r1_tarski(X13,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) )
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f216])).

fof(f1538,plain,
    ( spl5_88
    | spl5_86
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1511,f893,f77,f1528,f1536])).

fof(f1511,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X9),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X9)
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10) )
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f240])).

fof(f1534,plain,
    ( spl5_87
    | spl5_86
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1510,f893,f77,f1528,f1532])).

fof(f1510,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X5),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X5)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7) )
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f341])).

fof(f1530,plain,
    ( spl5_85
    | spl5_86
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f1509,f893,f77,f1528,f1525])).

fof(f1509,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X0),sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X4,X1)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) )
    | ~ spl5_2
    | ~ spl5_63 ),
    inference(resolution,[],[f894,f586])).

fof(f586,plain,
    ( ! [X21,X19,X22,X20,X18] :
        ( r1_tarski(X22,u1_struct_0(sK2))
        | ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X18)
        | ~ r1_tarski(X21,X19)
        | ~ r1_tarski(X18,sK4)
        | ~ r1_tarski(X22,X21) )
    | ~ spl5_2 ),
    inference(resolution,[],[f341,f68])).

fof(f1408,plain,
    ( ~ spl5_20
    | spl5_84
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1399,f149,f1406,f171])).

fof(f1406,plain,
    ( spl5_84
  <=> ! [X1,X2] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2)
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1399,plain,
    ( ! [X2,X1] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f1394])).

fof(f1394,plain,
    ( ! [X2,X1] :
        ( v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2)
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,X1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f1367,f251])).

fof(f1404,plain,
    ( ~ spl5_20
    | spl5_83
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1400,f149,f1402,f171])).

fof(f1402,plain,
    ( spl5_83
  <=> ! [X0] :
        ( v4_relat_1(k7_relat_1(sK3,X0),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f1400,plain,
    ( ! [X0] :
        ( v4_relat_1(k7_relat_1(sK3,X0),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f1393])).

fof(f1393,plain,
    ( ! [X0] :
        ( v4_relat_1(k7_relat_1(sK3,X0),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f1367,f59])).

fof(f1233,plain,
    ( ~ spl5_19
    | spl5_82
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f1225,f1186,f1231,f167])).

fof(f1231,plain,
    ( spl5_82
  <=> ! [X49,X51,X48,X50] :
        ( ~ r1_tarski(X48,sK4)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X50)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X49)
        | ~ r1_tarski(k2_zfmisc_1(X49,X50),X51)
        | ~ r1_tarski(X51,X48) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f1225,plain,
    ( ! [X50,X48,X51,X49] :
        ( ~ r1_tarski(X48,sK4)
        | ~ r1_tarski(k2_zfmisc_1(X49,X50),X51)
        | ~ r1_tarski(X51,X48)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X49)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X50) )
    | ~ spl5_78 ),
    inference(resolution,[],[f1187,f753])).

fof(f1187,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6) )
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f1229,plain,
    ( spl5_77
    | spl5_81
    | ~ spl5_2
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f1212,f1186,f77,f1227,f1182])).

fof(f1182,plain,
    ( spl5_77
  <=> ! [X1,X3,X2,X4] :
        ( ~ r1_tarski(X1,X2)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X4)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X4,X1)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1227,plain,
    ( spl5_81
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1212,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X5,X2)
        | ~ r1_tarski(X4,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X5) )
    | ~ spl5_2
    | ~ spl5_78 ),
    inference(resolution,[],[f1187,f586])).

fof(f1196,plain,
    ( ~ spl5_19
    | spl5_80
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1180,f635,f1194,f167])).

fof(f1194,plain,
    ( spl5_80
  <=> ! [X36,X35,X37] :
        ( ~ r1_tarski(k2_zfmisc_1(X35,X36),X37)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X36)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35)
        | ~ r1_tarski(X37,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1180,plain,
    ( ! [X37,X35,X36] :
        ( ~ r1_tarski(k2_zfmisc_1(X35,X36),X37)
        | ~ r1_tarski(X37,sK4)
        | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X36) )
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f753])).

fof(f1192,plain,
    ( spl5_78
    | spl5_79
    | ~ spl5_15
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1172,f635,f144,f1190,f1186])).

fof(f1172,plain,
    ( ! [X17,X15,X18,X16] :
        ( ~ r1_tarski(u1_struct_0(sK1),X15)
        | ~ r1_tarski(X15,sK4)
        | ~ r1_tarski(X16,sK4)
        | ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X16)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X17) )
    | ~ spl5_15
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f370])).

fof(f1188,plain,
    ( spl5_78
    | spl5_73
    | ~ spl5_2
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1168,f635,f77,f1134,f1186])).

fof(f1168,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r1_tarski(u1_struct_0(sK2),X5)
        | ~ r1_tarski(X5,sK4)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7) )
    | ~ spl5_2
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f341])).

fof(f1184,plain,
    ( spl5_77
    | spl5_73
    | ~ spl5_2
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1167,f635,f77,f1134,f1182])).

fof(f1167,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),X0)
        | ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X4,X1)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X4) )
    | ~ spl5_2
    | ~ spl5_54 ),
    inference(resolution,[],[f636,f586])).

fof(f1166,plain,
    ( spl5_37
    | spl5_54
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1157,f149,f77,f635,f362])).

fof(f362,plain,
    ( spl5_37
  <=> ! [X13] :
        ( v5_relat_1(X13,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X13),sK3)
        | ~ v1_relat_1(X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1157,plain,
    ( ! [X64,X62,X63] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X62)
        | ~ r1_tarski(X62,X63)
        | ~ r1_tarski(X63,sK4)
        | v5_relat_1(X64,u1_struct_0(sK2))
        | ~ v1_relat_1(X64)
        | ~ r1_tarski(k2_relat_1(X64),sK3) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f590,f213])).

fof(f1165,plain,
    ( spl5_35
    | spl5_54
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1156,f149,f77,f635,f354])).

fof(f354,plain,
    ( spl5_35
  <=> ! [X11,X12] :
        ( v5_relat_1(X11,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X11),X12)
        | ~ r1_tarski(X12,sK3)
        | ~ v1_relat_1(X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1156,plain,
    ( ! [X61,X59,X60,X58] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X58)
        | ~ r1_tarski(X58,X59)
        | ~ r1_tarski(X59,sK4)
        | v5_relat_1(X60,u1_struct_0(sK2))
        | ~ v1_relat_1(X60)
        | ~ r1_tarski(X61,sK3)
        | ~ r1_tarski(k2_relat_1(X60),X61) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f590,f229])).

fof(f1164,plain,
    ( spl5_52
    | spl5_54
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1155,f149,f77,f635,f616])).

fof(f1155,plain,
    ( ! [X57,X54,X56,X55,X53] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X53)
        | ~ r1_tarski(X53,X54)
        | ~ r1_tarski(X54,sK4)
        | v5_relat_1(X55,u1_struct_0(sK2))
        | ~ v1_relat_1(X55)
        | ~ r1_tarski(X56,X57)
        | ~ r1_tarski(X57,sK3)
        | ~ r1_tarski(k2_relat_1(X55),X56) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f590,f277])).

fof(f1163,plain,
    ( spl5_76
    | spl5_54
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1154,f149,f77,f635,f1161])).

fof(f1154,plain,
    ( ! [X47,X52,X50,X48,X51,X49] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X47)
        | ~ r1_tarski(X47,X48)
        | ~ r1_tarski(X48,sK4)
        | v5_relat_1(X49,u1_struct_0(sK2))
        | ~ v1_relat_1(X49)
        | ~ r1_tarski(X50,sK3)
        | ~ r1_tarski(X51,X52)
        | ~ r1_tarski(X52,X50)
        | ~ r1_tarski(k2_relat_1(X49),X51) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f590,f439])).

fof(f1143,plain,
    ( spl5_73
    | spl5_75
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1123,f77,f1141,f1134])).

fof(f1141,plain,
    ( spl5_75
  <=> ! [X84,X86,X85,X87,X88] :
        ( ~ r1_tarski(X84,X85)
        | ~ v1_relat_1(X88)
        | v5_relat_1(X88,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X88),X87)
        | ~ r1_tarski(X86,sK4)
        | ~ r1_tarski(X87,X84)
        | ~ r1_tarski(X85,X86) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1123,plain,
    ( ! [X88,X87,X85,X89,X86,X84] :
        ( ~ r1_tarski(X84,X85)
        | ~ r1_tarski(X85,X86)
        | ~ r1_tarski(X87,X84)
        | ~ r1_tarski(X86,sK4)
        | ~ r1_tarski(k2_relat_1(X88),X87)
        | ~ r1_tarski(X89,sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X89)
        | v5_relat_1(X88,u1_struct_0(sK2))
        | ~ v1_relat_1(X88) )
    | ~ spl5_2 ),
    inference(resolution,[],[f586,f343])).

fof(f1139,plain,
    ( spl5_73
    | spl5_74
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1122,f144,f77,f1137,f1134])).

fof(f1137,plain,
    ( spl5_74
  <=> ! [X82,X79,X81,X78,X80] :
        ( ~ r1_tarski(X78,X79)
        | ~ v1_relat_1(X82)
        | v5_relat_1(X82,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X82),X81)
        | ~ r1_tarski(X80,sK4)
        | ~ r1_tarski(X81,X78)
        | ~ r1_tarski(X79,X80) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1122,plain,
    ( ! [X80,X78,X83,X81,X79,X82] :
        ( ~ r1_tarski(X78,X79)
        | ~ r1_tarski(X79,X80)
        | ~ r1_tarski(X81,X78)
        | ~ r1_tarski(X80,sK4)
        | ~ r1_tarski(k2_relat_1(X82),X81)
        | ~ r1_tarski(X83,sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X83)
        | v5_relat_1(X82,u1_struct_0(sK1))
        | ~ v1_relat_1(X82) )
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(resolution,[],[f586,f373])).

fof(f1081,plain,
    ( spl5_72
    | spl5_64
    | ~ spl5_16
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f1073,f1058,f149,f918,f1079])).

fof(f1079,plain,
    ( spl5_72
  <=> ! [X22,X21,X23] :
        ( ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X22)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f1073,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(X20,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20)
        | ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(u1_struct_0(sK0),X22) )
    | ~ spl5_16
    | ~ spl5_71 ),
    inference(resolution,[],[f1059,f439])).

fof(f1064,plain,
    ( ~ spl5_20
    | spl5_25
    | spl5_71
    | ~ spl5_23
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1045,f921,f206,f1058,f261,f171])).

fof(f261,plain,
    ( spl5_25
  <=> v1_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f206,plain,
    ( spl5_23
  <=> v5_relat_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1045,plain,
    ( ! [X72,X71] :
        ( ~ r1_tarski(X71,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X72)
        | ~ r1_tarski(X72,X71)
        | v1_relat_1(k2_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_23
    | ~ spl5_65 ),
    inference(resolution,[],[f938,f208])).

fof(f208,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f938,plain,
    ( ! [X61,X59,X62,X60] :
        ( ~ v5_relat_1(X59,X61)
        | ~ r1_tarski(X60,sK3)
        | ~ r1_tarski(X61,X62)
        | ~ r1_tarski(X62,X60)
        | v1_relat_1(k2_relat_1(X59))
        | ~ v1_relat_1(X59) )
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f61])).

fof(f1063,plain,
    ( spl5_27
    | spl5_71
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1032,f921,f149,f1058,f270])).

fof(f270,plain,
    ( spl5_27
  <=> ! [X3] :
        ( ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,sK3)
        | v1_relat_1(k2_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1032,plain,
    ( ! [X17,X15,X16] :
        ( ~ r1_tarski(X15,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X16)
        | ~ r1_tarski(X16,X15)
        | v1_relat_1(k2_relat_1(X17))
        | ~ v1_relat_1(X17)
        | ~ r1_tarski(X17,sK3) )
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(resolution,[],[f938,f227])).

fof(f1062,plain,
    ( spl5_33
    | spl5_71
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1031,f921,f149,f1058,f327])).

fof(f327,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( v1_relat_1(k2_relat_1(X0))
        | ~ r1_tarski(X1,sK3)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1031,plain,
    ( ! [X14,X12,X13,X11] :
        ( ~ r1_tarski(X11,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X12)
        | ~ r1_tarski(X12,X11)
        | v1_relat_1(k2_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,sK3) )
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(resolution,[],[f938,f275])).

fof(f1061,plain,
    ( spl5_47
    | spl5_71
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1030,f921,f149,f1058,f553])).

fof(f553,plain,
    ( spl5_47
  <=> ! [X1,X3,X2] :
        ( v1_relat_1(k2_relat_1(X1))
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X2,sK3)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1030,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ r1_tarski(X6,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X7)
        | ~ r1_tarski(X7,X6)
        | v1_relat_1(k2_relat_1(X8))
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X9,sK3)
        | ~ r1_tarski(X8,X10)
        | ~ r1_tarski(X10,X9) )
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(resolution,[],[f938,f436])).

fof(f436,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X1,sK3)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_16 ),
    inference(resolution,[],[f277,f204])).

fof(f1060,plain,
    ( spl5_70
    | spl5_71
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1029,f921,f149,f1058,f1055])).

fof(f1055,plain,
    ( spl5_70
  <=> ! [X3,X5,X2,X4] :
        ( v1_relat_1(k2_relat_1(X2))
        | ~ r1_tarski(X5,sK3)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X3,X4)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f1029,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r1_tarski(X0,sK3)
        | ~ r1_tarski(u1_struct_0(sK0),X1)
        | ~ r1_tarski(X1,X0)
        | v1_relat_1(k2_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X5,sK3) )
    | ~ spl5_16
    | ~ spl5_65 ),
    inference(resolution,[],[f938,f896])).

fof(f896,plain,
    ( ! [X2,X0,X3,X1] :
        ( v5_relat_1(X3,u1_struct_0(sK0))
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X0,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f439,f204])).

fof(f999,plain,
    ( spl5_69
    | spl5_64
    | ~ spl5_16
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f991,f958,f149,f918,f997])).

fof(f997,plain,
    ( spl5_69
  <=> ! [X22,X21,X23] :
        ( ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X22)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f991,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(X20,sK3)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20)
        | ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(u1_struct_0(sK1),X22) )
    | ~ spl5_16
    | ~ spl5_67 ),
    inference(resolution,[],[f959,f439])).

fof(f982,plain,
    ( spl5_68
    | spl5_64
    | ~ spl5_16
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f974,f522,f149,f918,f980])).

fof(f980,plain,
    ( spl5_68
  <=> ! [X22,X21,X23] :
        ( ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X22)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f974,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20)
        | ~ r1_tarski(X20,sK3)
        | ~ r1_tarski(X21,sK3)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(u1_struct_0(sK2),X22) )
    | ~ spl5_16
    | ~ spl5_46 ),
    inference(resolution,[],[f523,f439])).

fof(f965,plain,
    ( spl5_67
    | spl5_18
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f949,f921,f144,f162,f958])).

fof(f162,plain,
    ( spl5_18
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f949,plain,
    ( ! [X105,X106] :
        ( v1_relat_1(sK4)
        | ~ r1_tarski(X105,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X106)
        | ~ r1_tarski(X106,X105) )
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f146])).

fof(f964,plain,
    ( spl5_46
    | spl5_18
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f948,f921,f77,f162,f522])).

fof(f948,plain,
    ( ! [X103,X104] :
        ( v1_relat_1(sK4)
        | ~ r1_tarski(X103,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X104)
        | ~ r1_tarski(X104,X103) )
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f79])).

fof(f963,plain,
    ( spl5_67
    | spl5_31
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f932,f921,f144,f305,f958])).

fof(f305,plain,
    ( spl5_31
  <=> ! [X2] :
        ( v1_relat_1(X2)
        | ~ r1_tarski(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f932,plain,
    ( ! [X35,X33,X34] :
        ( v1_relat_1(X33)
        | ~ r1_tarski(X34,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X35)
        | ~ r1_tarski(X35,X34)
        | ~ r1_tarski(X33,sK4) )
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f215])).

fof(f962,plain,
    ( spl5_67
    | spl5_30
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f931,f921,f144,f301,f958])).

fof(f301,plain,
    ( spl5_30
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f931,plain,
    ( ! [X30,X31,X29,X32] :
        ( v1_relat_1(X29)
        | ~ r1_tarski(X30,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X31)
        | ~ r1_tarski(X31,X30)
        | ~ r1_tarski(X32,sK4)
        | ~ r1_tarski(X29,X32) )
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f219])).

fof(f961,plain,
    ( spl5_67
    | spl5_41
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f930,f921,f144,f475,f958])).

fof(f475,plain,
    ( spl5_41
  <=> ! [X3,X0,X2] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f930,plain,
    ( ! [X28,X26,X24,X27,X25] :
        ( v1_relat_1(X24)
        | ~ r1_tarski(X25,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X26)
        | ~ r1_tarski(X26,X25)
        | ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,sK4)
        | ~ r1_tarski(X24,X27) )
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f245])).

fof(f960,plain,
    ( spl5_67
    | spl5_66
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f929,f921,f144,f951,f958])).

fof(f951,plain,
    ( spl5_66
  <=> ! [X3,X5,X0,X4] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(X0,X4)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f929,plain,
    ( ! [X23,X21,X19,X22,X20,X18] :
        ( v1_relat_1(X18)
        | ~ r1_tarski(X19,sK3)
        | ~ r1_tarski(u1_struct_0(sK1),X20)
        | ~ r1_tarski(X20,X19)
        | ~ r1_tarski(X21,sK4)
        | ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X21)
        | ~ r1_tarski(X18,X22) )
    | ~ spl5_15
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f370])).

fof(f956,plain,
    ( spl5_46
    | spl5_31
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f928,f921,f77,f305,f522])).

fof(f928,plain,
    ( ! [X17,X15,X16] :
        ( v1_relat_1(X15)
        | ~ r1_tarski(X16,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X17)
        | ~ r1_tarski(X17,X16)
        | ~ r1_tarski(X15,sK4) )
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f214])).

fof(f955,plain,
    ( spl5_46
    | spl5_30
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f927,f921,f77,f301,f522])).

fof(f927,plain,
    ( ! [X14,X12,X13,X11] :
        ( v1_relat_1(X11)
        | ~ r1_tarski(X12,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X13)
        | ~ r1_tarski(X13,X12)
        | ~ r1_tarski(X14,sK4)
        | ~ r1_tarski(X11,X14) )
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f216])).

fof(f954,plain,
    ( spl5_46
    | spl5_41
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f926,f921,f77,f475,f522])).

fof(f926,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( v1_relat_1(X6)
        | ~ r1_tarski(X7,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X8)
        | ~ r1_tarski(X8,X7)
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,sK4)
        | ~ r1_tarski(X6,X9) )
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f240])).

fof(f953,plain,
    ( spl5_46
    | spl5_66
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f925,f921,f77,f951,f522])).

fof(f925,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(X1,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(X0,X4) )
    | ~ spl5_2
    | ~ spl5_65 ),
    inference(resolution,[],[f922,f341])).

fof(f924,plain,
    ( ~ spl5_19
    | spl5_65
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f905,f149,f921,f167])).

fof(f905,plain,
    ( ! [X37,X35,X36,X34] :
        ( ~ r1_tarski(X34,sK3)
        | ~ r1_tarski(X35,X36)
        | ~ r1_tarski(X36,X34)
        | ~ r1_tarski(X37,X35)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | v1_relat_1(X37) )
    | ~ spl5_16 ),
    inference(resolution,[],[f439,f156])).

fof(f923,plain,
    ( spl5_64
    | spl5_65
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f902,f449,f149,f921,f918])).

fof(f902,plain,
    ( ! [X24,X23,X21,X22,X20] :
        ( ~ r1_tarski(X20,sK3)
        | ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X20)
        | ~ r1_tarski(X23,X21)
        | v1_relat_1(X23)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24)
        | ~ r1_tarski(X24,sK3) )
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(resolution,[],[f439,f450])).

fof(f895,plain,
    ( ~ spl5_19
    | spl5_63
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f876,f619,f893,f167])).

fof(f876,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)
        | ~ r1_tarski(k2_zfmisc_1(X12,X13),sK4) )
    | ~ spl5_53 ),
    inference(resolution,[],[f753,f620])).

fof(f797,plain,
    ( ~ spl5_18
    | spl5_62
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f791,f77,f795,f162])).

fof(f795,plain,
    ( spl5_62
  <=> ! [X3,X2,X4] :
        ( ~ v1_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))),X4)
        | v4_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f791,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)))
        | v4_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)),u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))),X4)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f781,f252])).

fof(f781,plain,
    ( ! [X28,X27] :
        ( ~ r1_tarski(k1_relat_1(X27),sK4)
        | ~ v1_relat_1(X27)
        | v4_relat_1(X27,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X27),X28) )
    | ~ spl5_2 ),
    inference(resolution,[],[f751,f214])).

fof(f773,plain,
    ( ~ spl5_61
    | spl5_56 ),
    inference(avatar_split_clause,[],[f755,f742,f770])).

fof(f755,plain,
    ( ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | spl5_56 ),
    inference(resolution,[],[f744,f64])).

fof(f768,plain,
    ( ~ spl5_58
    | ~ spl5_59
    | ~ spl5_60
    | spl5_56 ),
    inference(avatar_split_clause,[],[f754,f742,f765,f761,f757])).

fof(f754,plain,
    ( ~ r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2))
    | ~ v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | spl5_56 ),
    inference(resolution,[],[f744,f65])).

fof(f749,plain,
    ( ~ spl5_56
    | ~ spl5_57
    | spl5_1 ),
    inference(avatar_split_clause,[],[f740,f72,f746,f742])).

fof(f740,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl5_1 ),
    inference(superposition,[],[f74,f69])).

fof(f641,plain,
    ( spl5_54
    | ~ spl5_55
    | ~ spl5_15
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f628,f619,f144,f638,f635])).

fof(f638,plain,
    ( spl5_55
  <=> r1_tarski(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f628,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(u1_struct_0(sK1),sK4)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6) )
    | ~ spl5_15
    | ~ spl5_53 ),
    inference(resolution,[],[f620,f245])).

fof(f623,plain,
    ( spl5_37
    | spl5_53
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f613,f149,f77,f619,f362])).

fof(f613,plain,
    ( ! [X33,X34] :
        ( ~ r1_tarski(X33,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X33)
        | v5_relat_1(X34,u1_struct_0(sK2))
        | ~ v1_relat_1(X34)
        | ~ r1_tarski(k2_relat_1(X34),sK3) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f343,f213])).

fof(f622,plain,
    ( spl5_35
    | spl5_53
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f612,f149,f77,f619,f354])).

fof(f612,plain,
    ( ! [X30,X31,X32] :
        ( ~ r1_tarski(X30,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30)
        | v5_relat_1(X31,u1_struct_0(sK2))
        | ~ v1_relat_1(X31)
        | ~ r1_tarski(X32,sK3)
        | ~ r1_tarski(k2_relat_1(X31),X32) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f343,f229])).

fof(f621,plain,
    ( spl5_52
    | spl5_53
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f611,f149,f77,f619,f616])).

fof(f611,plain,
    ( ! [X28,X26,X29,X27] :
        ( ~ r1_tarski(X26,sK4)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26)
        | v5_relat_1(X27,u1_struct_0(sK2))
        | ~ v1_relat_1(X27)
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,sK3)
        | ~ r1_tarski(k2_relat_1(X27),X28) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f343,f277])).

fof(f602,plain,
    ( ~ spl5_49
    | spl5_51
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f589,f77,f600,f592])).

fof(f592,plain,
    ( spl5_49
  <=> r1_tarski(u1_struct_0(sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f600,plain,
    ( spl5_51
  <=> ! [X32,X34,X31,X33] :
        ( ~ r1_tarski(X31,sK4)
        | ~ v1_relat_1(X34)
        | v5_relat_1(X34,u1_struct_0(sK2))
        | ~ r1_tarski(k2_relat_1(X34),X32)
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X31) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f589,plain,
    ( ! [X33,X31,X34,X32] :
        ( ~ r1_tarski(X31,sK4)
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X31)
        | ~ r1_tarski(k2_relat_1(X34),X32)
        | ~ r1_tarski(u1_struct_0(sK2),sK4)
        | v5_relat_1(X34,u1_struct_0(sK2))
        | ~ v1_relat_1(X34) )
    | ~ spl5_2 ),
    inference(resolution,[],[f341,f242])).

fof(f598,plain,
    ( ~ spl5_49
    | spl5_50
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f588,f144,f77,f596,f592])).

fof(f596,plain,
    ( spl5_50
  <=> ! [X27,X29,X28,X30] :
        ( ~ r1_tarski(X27,sK4)
        | ~ v1_relat_1(X30)
        | v5_relat_1(X30,u1_struct_0(sK1))
        | ~ r1_tarski(k2_relat_1(X30),X28)
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X27) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f588,plain,
    ( ! [X30,X28,X29,X27] :
        ( ~ r1_tarski(X27,sK4)
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X27)
        | ~ r1_tarski(k2_relat_1(X30),X28)
        | ~ r1_tarski(u1_struct_0(sK2),sK4)
        | v5_relat_1(X30,u1_struct_0(sK1))
        | ~ v1_relat_1(X30) )
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(resolution,[],[f341,f247])).

fof(f561,plain,
    ( ~ spl5_20
    | spl5_25
    | spl5_48
    | ~ spl5_23
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f546,f449,f206,f556,f261,f171])).

fof(f546,plain,
    ( ! [X29] :
        ( ~ r1_tarski(u1_struct_0(sK0),X29)
        | ~ r1_tarski(X29,sK3)
        | v1_relat_1(k2_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_23
    | ~ spl5_39 ),
    inference(resolution,[],[f462,f208])).

fof(f462,plain,
    ( ! [X28,X29,X27] :
        ( ~ v5_relat_1(X27,X28)
        | ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,sK3)
        | v1_relat_1(k2_relat_1(X27))
        | ~ v1_relat_1(X27) )
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f61])).

fof(f560,plain,
    ( spl5_27
    | spl5_48
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f538,f449,f149,f556,f270])).

fof(f538,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(u1_struct_0(sK0),X7)
        | ~ r1_tarski(X7,sK3)
        | v1_relat_1(k2_relat_1(X8))
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,sK3) )
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(resolution,[],[f462,f227])).

fof(f559,plain,
    ( spl5_33
    | spl5_48
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f537,f449,f149,f556,f327])).

fof(f537,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(u1_struct_0(sK0),X4)
        | ~ r1_tarski(X4,sK3)
        | v1_relat_1(k2_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,sK3) )
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(resolution,[],[f462,f275])).

fof(f558,plain,
    ( spl5_47
    | spl5_48
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f536,f449,f149,f556,f553])).

fof(f536,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | ~ r1_tarski(X0,sK3)
        | v1_relat_1(k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,sK3)
        | ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X3,X2) )
    | ~ spl5_16
    | ~ spl5_39 ),
    inference(resolution,[],[f462,f436])).

fof(f524,plain,
    ( spl5_46
    | ~ spl5_38
    | ~ spl5_16
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f518,f472,f149,f445,f522])).

fof(f445,plain,
    ( spl5_38
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f518,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK3)
        | ~ r1_tarski(u1_struct_0(sK2),X6) )
    | ~ spl5_16
    | ~ spl5_40 ),
    inference(resolution,[],[f473,f277])).

fof(f511,plain,
    ( ~ spl5_18
    | spl5_45
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f498,f301,f509,f162])).

fof(f509,plain,
    ( spl5_45
  <=> ! [X9,X11,X10] :
        ( ~ r1_tarski(X9,k1_relat_1(k7_relat_1(X10,k7_relat_1(sK4,X11))))
        | ~ v1_relat_1(X10)
        | v1_relat_1(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f498,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(X9,k1_relat_1(k7_relat_1(X10,k7_relat_1(sK4,X11))))
        | v1_relat_1(X9)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(X10) )
    | ~ spl5_30 ),
    inference(resolution,[],[f302,f252])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK4)
        | ~ r1_tarski(X0,X1)
        | v1_relat_1(X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f301])).

fof(f507,plain,
    ( ~ spl5_18
    | spl5_44
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f496,f301,f505,f162])).

fof(f505,plain,
    ( spl5_44
  <=> ! [X5,X4,X6] :
        ( ~ r1_tarski(X4,k7_relat_1(k7_relat_1(sK4,X5),X6))
        | ~ v1_relat_1(k7_relat_1(sK4,X5))
        | v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f496,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k7_relat_1(k7_relat_1(sK4,X5),X6))
        | v1_relat_1(X4)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(k7_relat_1(sK4,X5)) )
    | ~ spl5_30 ),
    inference(resolution,[],[f302,f251])).

fof(f503,plain,
    ( ~ spl5_18
    | spl5_43
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f495,f301,f501,f162])).

fof(f501,plain,
    ( spl5_43
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK4,X3))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f495,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k7_relat_1(sK4,X3))
        | v1_relat_1(X2)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_30 ),
    inference(resolution,[],[f302,f59])).

fof(f487,plain,
    ( spl5_42
    | spl5_18
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f470,f449,f144,f162,f481])).

fof(f470,plain,
    ( ! [X50] :
        ( v1_relat_1(sK4)
        | ~ r1_tarski(u1_struct_0(sK1),X50)
        | ~ r1_tarski(X50,sK3) )
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f146])).

fof(f486,plain,
    ( spl5_40
    | spl5_18
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f469,f449,f77,f162,f472])).

fof(f469,plain,
    ( ! [X49] :
        ( v1_relat_1(sK4)
        | ~ r1_tarski(u1_struct_0(sK2),X49)
        | ~ r1_tarski(X49,sK3) )
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f79])).

fof(f485,plain,
    ( spl5_42
    | spl5_31
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f458,f449,f144,f305,f481])).

fof(f458,plain,
    ( ! [X17,X16] :
        ( v1_relat_1(X16)
        | ~ r1_tarski(u1_struct_0(sK1),X17)
        | ~ r1_tarski(X17,sK3)
        | ~ r1_tarski(X16,sK4) )
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f215])).

fof(f484,plain,
    ( spl5_42
    | spl5_30
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f457,f449,f144,f301,f481])).

fof(f457,plain,
    ( ! [X14,X15,X13] :
        ( v1_relat_1(X13)
        | ~ r1_tarski(u1_struct_0(sK1),X14)
        | ~ r1_tarski(X14,sK3)
        | ~ r1_tarski(X15,sK4)
        | ~ r1_tarski(X13,X15) )
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f219])).

fof(f483,plain,
    ( spl5_42
    | spl5_41
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f456,f449,f144,f475,f481])).

fof(f456,plain,
    ( ! [X12,X10,X11,X9] :
        ( v1_relat_1(X9)
        | ~ r1_tarski(u1_struct_0(sK1),X10)
        | ~ r1_tarski(X10,sK3)
        | ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,sK4)
        | ~ r1_tarski(X9,X11) )
    | ~ spl5_15
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f245])).

fof(f479,plain,
    ( spl5_40
    | spl5_31
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f455,f449,f77,f305,f472])).

fof(f455,plain,
    ( ! [X8,X7] :
        ( v1_relat_1(X7)
        | ~ r1_tarski(u1_struct_0(sK2),X8)
        | ~ r1_tarski(X8,sK3)
        | ~ r1_tarski(X7,sK4) )
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f214])).

fof(f478,plain,
    ( spl5_40
    | spl5_30
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f454,f449,f77,f301,f472])).

fof(f454,plain,
    ( ! [X6,X4,X5] :
        ( v1_relat_1(X4)
        | ~ r1_tarski(u1_struct_0(sK2),X5)
        | ~ r1_tarski(X5,sK3)
        | ~ r1_tarski(X6,sK4)
        | ~ r1_tarski(X4,X6) )
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f216])).

fof(f477,plain,
    ( spl5_40
    | spl5_41
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f453,f449,f77,f475,f472])).

fof(f453,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(u1_struct_0(sK2),X1)
        | ~ r1_tarski(X1,sK3)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK4)
        | ~ r1_tarski(X0,X2) )
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(resolution,[],[f450,f240])).

fof(f452,plain,
    ( ~ spl5_19
    | spl5_39
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f440,f149,f449,f167])).

fof(f440,plain,
    ( ! [X14,X15,X13] :
        ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,sK3)
        | ~ r1_tarski(X15,X13)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | v1_relat_1(X15) )
    | ~ spl5_16 ),
    inference(resolution,[],[f277,f156])).

fof(f451,plain,
    ( ~ spl5_38
    | spl5_39
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f438,f281,f149,f449,f445])).

fof(f438,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK3)
        | ~ r1_tarski(X8,X6)
        | v1_relat_1(X8)
        | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3) )
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(resolution,[],[f277,f282])).

fof(f364,plain,
    ( spl5_37
    | ~ spl5_36
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f351,f149,f77,f357,f362])).

fof(f357,plain,
    ( spl5_36
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f351,plain,
    ( ! [X13] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4)
        | v5_relat_1(X13,u1_struct_0(sK2))
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(k2_relat_1(X13),sK3) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f242,f213])).

fof(f360,plain,
    ( spl5_35
    | ~ spl5_36
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f350,f149,f77,f357,f354])).

fof(f350,plain,
    ( ! [X12,X11] :
        ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4)
        | v5_relat_1(X11,u1_struct_0(sK2))
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X12,sK3)
        | ~ r1_tarski(k2_relat_1(X11),X12) )
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f242,f229])).

fof(f335,plain,
    ( ~ spl5_20
    | spl5_25
    | ~ spl5_34
    | ~ spl5_23
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f323,f281,f206,f330,f261,f171])).

fof(f330,plain,
    ( spl5_34
  <=> r1_tarski(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f323,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3)
    | v1_relat_1(k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_23
    | ~ spl5_28 ),
    inference(resolution,[],[f290,f208])).

fof(f290,plain,
    ( ! [X10,X9] :
        ( ~ v5_relat_1(X9,X10)
        | ~ r1_tarski(X10,sK3)
        | v1_relat_1(k2_relat_1(X9))
        | ~ v1_relat_1(X9) )
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f61])).

fof(f334,plain,
    ( spl5_27
    | ~ spl5_34
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f318,f281,f149,f330,f270])).

fof(f318,plain,
    ( ! [X2] :
        ( ~ r1_tarski(u1_struct_0(sK0),sK3)
        | v1_relat_1(k2_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,sK3) )
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(resolution,[],[f290,f227])).

fof(f333,plain,
    ( spl5_33
    | ~ spl5_34
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f317,f281,f149,f330,f327])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),sK3)
        | v1_relat_1(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK3) )
    | ~ spl5_16
    | ~ spl5_28 ),
    inference(resolution,[],[f290,f275])).

fof(f315,plain,
    ( ~ spl5_32
    | spl5_18
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f295,f281,f144,f162,f309])).

fof(f309,plain,
    ( spl5_32
  <=> r1_tarski(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f295,plain,
    ( v1_relat_1(sK4)
    | ~ r1_tarski(u1_struct_0(sK1),sK3)
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f146])).

fof(f314,plain,
    ( ~ spl5_29
    | spl5_18
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f294,f281,f77,f162,f297])).

fof(f297,plain,
    ( spl5_29
  <=> r1_tarski(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f294,plain,
    ( v1_relat_1(sK4)
    | ~ r1_tarski(u1_struct_0(sK2),sK3)
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f79])).

fof(f313,plain,
    ( ~ spl5_32
    | spl5_31
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f287,f281,f144,f305,f309])).

fof(f287,plain,
    ( ! [X5] :
        ( v1_relat_1(X5)
        | ~ r1_tarski(u1_struct_0(sK1),sK3)
        | ~ r1_tarski(X5,sK4) )
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f215])).

fof(f312,plain,
    ( ~ spl5_32
    | spl5_30
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f286,f281,f144,f301,f309])).

fof(f286,plain,
    ( ! [X4,X3] :
        ( v1_relat_1(X3)
        | ~ r1_tarski(u1_struct_0(sK1),sK3)
        | ~ r1_tarski(X4,sK4)
        | ~ r1_tarski(X3,X4) )
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f219])).

fof(f307,plain,
    ( ~ spl5_29
    | spl5_31
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f285,f281,f77,f305,f297])).

fof(f285,plain,
    ( ! [X2] :
        ( v1_relat_1(X2)
        | ~ r1_tarski(u1_struct_0(sK2),sK3)
        | ~ r1_tarski(X2,sK4) )
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f214])).

fof(f303,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f284,f281,f77,f301,f297])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ r1_tarski(u1_struct_0(sK2),sK3)
        | ~ r1_tarski(X1,sK4)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_2
    | ~ spl5_28 ),
    inference(resolution,[],[f282,f216])).

fof(f283,plain,
    ( ~ spl5_19
    | spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f278,f149,f281,f167])).

fof(f278,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(X7,sK3)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | v1_relat_1(X8) )
    | ~ spl5_16 ),
    inference(resolution,[],[f229,f156])).

fof(f272,plain,
    ( ~ spl5_26
    | spl5_27
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f255,f149,f270,f265])).

fof(f265,plain,
    ( spl5_26
  <=> v1_relat_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f255,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | ~ v1_relat_1(u1_struct_0(sK0))
        | v1_relat_1(k2_relat_1(X3))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl5_16 ),
    inference(resolution,[],[f188,f227])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k2_relat_1(X0)) ) ),
    inference(resolution,[],[f61,f156])).

fof(f268,plain,
    ( spl5_25
    | ~ spl5_26
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f253,f206,f171,f265,f261])).

fof(f253,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(u1_struct_0(sK0))
    | v1_relat_1(k2_relat_1(sK3))
    | ~ spl5_23 ),
    inference(resolution,[],[f188,f208])).

fof(f235,plain,
    ( ~ spl5_19
    | spl5_24
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f230,f149,f233,f167])).

fof(f233,plain,
    ( spl5_24
  <=> ! [X4] :
        ( ~ r1_tarski(X4,sK3)
        | v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f230,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK3)
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | v1_relat_1(X4) )
    | ~ spl5_16 ),
    inference(resolution,[],[f213,f156])).

fof(f209,plain,
    ( spl5_23
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f203,f87,f206])).

fof(f203,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f89])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f197,plain,
    ( spl5_22
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f191,f87,f194])).

fof(f194,plain,
    ( spl5_22
  <=> v4_relat_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f191,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f66,f89])).

fof(f186,plain,
    ( spl5_18
    | ~ spl5_21
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f177,f77,f183,f162])).

fof(f183,plain,
    ( spl5_21
  <=> v1_relat_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f177,plain,
    ( ~ v1_relat_1(u1_struct_0(sK2))
    | v1_relat_1(sK4)
    | ~ spl5_2 ),
    inference(resolution,[],[f156,f79])).

fof(f176,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f169,f58])).

fof(f169,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f174,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f155,f87,f171,f167])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f55,f89])).

fof(f165,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f154,f82,f162,f158])).

fof(f158,plain,
    ( spl5_17
  <=> v1_relat_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f82,plain,
    ( spl5_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f154,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(u1_struct_0(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f84])).

fof(f84,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f152,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f142,f87,f149])).

fof(f142,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f89])).

fof(f147,plain,
    ( spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f141,f82,f144])).

fof(f141,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f63,f84])).

fof(f140,plain,(
    ~ spl5_14 ),
    inference(avatar_split_clause,[],[f41,f137])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & r1_tarski(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & r1_tarski(X4,u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                    & r1_tarski(X4,u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                  & r1_tarski(X4,u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                & r1_tarski(X4,u1_struct_0(X2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
              & r1_tarski(X4,u1_struct_0(sK2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
            & r1_tarski(X4,u1_struct_0(sK2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
          & r1_tarski(X4,u1_struct_0(sK2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
        & r1_tarski(X4,u1_struct_0(sK2))
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
      & r1_tarski(sK4,u1_struct_0(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(X4,u1_struct_0(X2))
                         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

fof(f135,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f42,f132])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f130,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f43,f127])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f120,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f45,f117])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f47,f107])).

fof(f107,plain,
    ( spl5_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f97])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f92])).

fof(f50,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f82])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f77])).

fof(f53,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f72])).

fof(f54,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (24243)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (24261)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.49  % (24251)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (24255)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.50  % (24245)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (24248)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (24265)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (24247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (24246)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (24257)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (24242)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (24265)Refutation not found, incomplete strategy% (24265)------------------------------
% 0.22/0.51  % (24265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24265)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24265)Memory used [KB]: 10618
% 0.22/0.51  % (24265)Time elapsed: 0.055 s
% 0.22/0.51  % (24265)------------------------------
% 0.22/0.51  % (24265)------------------------------
% 0.22/0.51  % (24264)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (24249)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (24244)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (24256)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (24252)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (24263)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (24262)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.53  % (24254)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.54  % (24260)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.54  % (24250)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  % (24253)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.54  % (24258)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.55  % (24259)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.56  % (24250)Refutation not found, incomplete strategy% (24250)------------------------------
% 0.22/0.56  % (24250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24250)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24250)Memory used [KB]: 10618
% 0.22/0.56  % (24250)Time elapsed: 0.148 s
% 0.22/0.56  % (24250)------------------------------
% 0.22/0.56  % (24250)------------------------------
% 2.09/0.67  % (24264)Refutation not found, incomplete strategy% (24264)------------------------------
% 2.09/0.67  % (24264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (24264)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.67  
% 2.09/0.67  % (24264)Memory used [KB]: 1663
% 2.09/0.67  % (24264)Time elapsed: 0.232 s
% 2.09/0.67  % (24264)------------------------------
% 2.09/0.67  % (24264)------------------------------
% 2.75/0.74  % (24246)Refutation found. Thanks to Tanya!
% 2.75/0.74  % SZS status Theorem for theBenchmark
% 2.75/0.74  % SZS output start Proof for theBenchmark
% 2.75/0.74  fof(f2895,plain,(
% 2.75/0.74    $false),
% 2.75/0.74    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f147,f152,f165,f174,f176,f186,f197,f209,f235,f268,f272,f283,f303,f307,f312,f313,f314,f315,f333,f334,f335,f360,f364,f451,f452,f477,f478,f479,f483,f484,f485,f486,f487,f503,f507,f511,f524,f558,f559,f560,f561,f598,f602,f621,f622,f623,f641,f749,f768,f773,f797,f895,f923,f924,f953,f954,f955,f956,f960,f961,f962,f963,f964,f965,f982,f999,f1060,f1061,f1062,f1063,f1064,f1081,f1139,f1143,f1163,f1164,f1165,f1166,f1184,f1188,f1192,f1196,f1229,f1233,f1404,f1408,f1530,f1534,f1538,f1542,f1547,f1551,f1552,f1553,f1554,f1555,f1562,f1566,f1570,f1575,f1583,f1587,f1591,f1595,f1599,f1603,f1607,f1611,f1615,f1616,f1620,f1624,f1625,f1629,f1633,f1637,f1641,f1743,f1763,f1794,f1795,f1796,f1797,f1899,f1952,f1957,f1962,f1967,f1969,f1970,f1978,f1983,f1993,f1998,f2004,f2006,f2026,f2038,f2063,f2068,f2072,f2073,f2077,f2078,f2083,f2104,f2109,f2115,f2122,f2151,f2172,f2183,f2187,f2206,f2211,f2212,f2213,f2214,f2215,f2245,f2249,f2253,f2257,f2261,f2271,f2277,f2301,f2305,f2309,f2313,f2317,f2330,f2335,f2382,f2386,f2390,f2394,f2398,f2417,f2421,f2425,f2429,f2433,f2455,f2459,f2464,f2465,f2485,f2516,f2520,f2524,f2528,f2532,f2549,f2553,f2557,f2561,f2565,f2655,f2660,f2664,f2672,f2676,f2680,f2681,f2682,f2686,f2690,f2691,f2695,f2700,f2701,f2702,f2707,f2708,f2709,f2714,f2715,f2716,f2717,f2722,f2726,f2727,f2728,f2733,f2737,f2741,f2742,f2743,f2744,f2745,f2749,f2753,f2754,f2755,f2759,f2761,f2787,f2791,f2795,f2799,f2803,f2823,f2827,f2831,f2835,f2839,f2845,f2865,f2885,f2891,f2894])).
% 2.75/0.74  fof(f2894,plain,(
% 2.75/0.74    ~spl5_20 | ~spl5_2 | spl5_217),
% 2.75/0.74    inference(avatar_split_clause,[],[f2893,f2888,f77,f171])).
% 2.75/0.74  fof(f171,plain,(
% 2.75/0.74    spl5_20 <=> v1_relat_1(sK3)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.75/0.74  fof(f77,plain,(
% 2.75/0.74    spl5_2 <=> r1_tarski(sK4,u1_struct_0(sK2))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.75/0.74  fof(f2888,plain,(
% 2.75/0.74    spl5_217 <=> k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).
% 2.75/0.74  fof(f2893,plain,(
% 2.75/0.74    ~r1_tarski(sK4,u1_struct_0(sK2)) | ~v1_relat_1(sK3) | spl5_217),
% 2.75/0.74    inference(trivial_inequality_removal,[],[f2892])).
% 2.75/0.74  fof(f2892,plain,(
% 2.75/0.74    k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) | ~r1_tarski(sK4,u1_struct_0(sK2)) | ~v1_relat_1(sK3) | spl5_217),
% 2.75/0.74    inference(superposition,[],[f2890,f56])).
% 2.75/0.74  fof(f56,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f19])).
% 2.75/0.74  fof(f19,plain,(
% 2.75/0.74    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.75/0.74    inference(ennf_transformation,[],[f6])).
% 2.75/0.74  fof(f6,axiom,(
% 2.75/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 2.75/0.74  fof(f2890,plain,(
% 2.75/0.74    k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | spl5_217),
% 2.75/0.74    inference(avatar_component_clause,[],[f2888])).
% 2.75/0.74  fof(f2891,plain,(
% 2.75/0.74    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_217 | spl5_214),
% 2.75/0.74    inference(avatar_split_clause,[],[f2886,f2842,f2888,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.74  fof(f122,plain,(
% 2.75/0.74    spl5_11 <=> v2_struct_0(sK1)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.75/0.74  fof(f117,plain,(
% 2.75/0.74    spl5_10 <=> v2_pre_topc(sK1)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.75/0.74  fof(f112,plain,(
% 2.75/0.74    spl5_9 <=> l1_pre_topc(sK1)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.75/0.74  fof(f137,plain,(
% 2.75/0.74    spl5_14 <=> v2_struct_0(sK0)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.75/0.74  fof(f132,plain,(
% 2.75/0.74    spl5_13 <=> v2_pre_topc(sK0)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.75/0.74  fof(f127,plain,(
% 2.75/0.74    spl5_12 <=> l1_pre_topc(sK0)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.75/0.74  fof(f97,plain,(
% 2.75/0.74    spl5_6 <=> v1_funct_1(sK3)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.75/0.74  fof(f92,plain,(
% 2.75/0.74    spl5_5 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.75/0.74  fof(f87,plain,(
% 2.75/0.74    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.75/0.74  fof(f102,plain,(
% 2.75/0.74    spl5_7 <=> m1_pre_topc(sK2,sK1)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.75/0.74  fof(f2842,plain,(
% 2.75/0.74    spl5_214 <=> k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) = k9_relat_1(sK3,sK4)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 2.75/0.74  fof(f2886,plain,(
% 2.75/0.74    k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_214),
% 2.75/0.74    inference(superposition,[],[f2844,f1508])).
% 2.75/0.74  fof(f1508,plain,(
% 2.75/0.74    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.75/0.74    inference(duplicate_literal_removal,[],[f1505])).
% 2.75/0.74  fof(f1505,plain,(
% 2.75/0.74    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_1(X6)) )),
% 2.75/0.74    inference(superposition,[],[f57,f70])).
% 2.75/0.74  fof(f70,plain,(
% 2.75/0.74    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f32])).
% 2.75/0.74  fof(f32,plain,(
% 2.75/0.74    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.75/0.74    inference(flattening,[],[f31])).
% 2.75/0.74  fof(f31,plain,(
% 2.75/0.74    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.75/0.74    inference(ennf_transformation,[],[f12])).
% 2.75/0.74  fof(f12,axiom,(
% 2.75/0.74    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.75/0.74  fof(f57,plain,(
% 2.75/0.74    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f21])).
% 2.75/0.74  fof(f21,plain,(
% 2.75/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.75/0.74    inference(flattening,[],[f20])).
% 2.75/0.74  fof(f20,plain,(
% 2.75/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.75/0.74    inference(ennf_transformation,[],[f13])).
% 2.75/0.74  fof(f13,axiom,(
% 2.75/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.75/0.74  fof(f2844,plain,(
% 2.75/0.74    k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) | spl5_214),
% 2.75/0.74    inference(avatar_component_clause,[],[f2842])).
% 2.75/0.74  fof(f2885,plain,(
% 2.75/0.74    ~spl5_198 | spl5_216 | ~spl5_191),
% 2.75/0.74    inference(avatar_split_clause,[],[f2881,f2688,f2883,f2730])).
% 2.75/0.74  fof(f2730,plain,(
% 2.75/0.74    spl5_198 <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).
% 2.75/0.74  fof(f2883,plain,(
% 2.75/0.74    spl5_216 <=> ! [X27,X26] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK3) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).
% 2.75/0.74  fof(f2688,plain,(
% 2.75/0.74    spl5_191 <=> ! [X12] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12) | ~r1_tarski(X12,sK3))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).
% 2.75/0.74  fof(f2881,plain,(
% 2.75/0.74    ( ! [X26,X27] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27)) ) | ~spl5_191),
% 2.75/0.74    inference(resolution,[],[f2689,f753])).
% 2.75/0.74  fof(f753,plain,(
% 2.75/0.74    ( ! [X10,X11,X9] : (r1_tarski(X9,k2_zfmisc_1(X11,X10)) | ~r1_tarski(k1_relat_1(X9),X11) | ~v1_relat_1(X9) | ~r1_tarski(k2_relat_1(X9),X10)) )),
% 2.75/0.74    inference(resolution,[],[f65,f63])).
% 2.75/0.74  fof(f63,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f40])).
% 2.75/0.74  fof(f40,plain,(
% 2.75/0.74    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.75/0.74    inference(nnf_transformation,[],[f2])).
% 2.75/0.74  fof(f2,axiom,(
% 2.75/0.74    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.75/0.74  fof(f65,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f26])).
% 2.75/0.74  fof(f26,plain,(
% 2.75/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.75/0.74    inference(flattening,[],[f25])).
% 2.75/0.74  fof(f25,plain,(
% 2.75/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.75/0.74    inference(ennf_transformation,[],[f11])).
% 2.75/0.74  fof(f11,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 2.75/0.74  fof(f2689,plain,(
% 2.75/0.74    ( ! [X12] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12) | ~r1_tarski(X12,sK3)) ) | ~spl5_191),
% 2.75/0.74    inference(avatar_component_clause,[],[f2688])).
% 2.75/0.74  fof(f2865,plain,(
% 2.75/0.74    ~spl5_198 | spl5_215 | ~spl5_185),
% 2.75/0.74    inference(avatar_split_clause,[],[f2861,f2662,f2863,f2730])).
% 2.75/0.74  fof(f2863,plain,(
% 2.75/0.74    spl5_215 <=> ! [X27,X26] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).
% 2.75/0.74  fof(f2662,plain,(
% 2.75/0.74    spl5_185 <=> ! [X2] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2) | ~r1_tarski(X2,sK4))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).
% 2.75/0.74  fof(f2861,plain,(
% 2.75/0.74    ( ! [X26,X27] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X26) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))),X27)) ) | ~spl5_185),
% 2.75/0.74    inference(resolution,[],[f2663,f753])).
% 2.75/0.74  fof(f2663,plain,(
% 2.75/0.74    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2) | ~r1_tarski(X2,sK4)) ) | ~spl5_185),
% 2.75/0.74    inference(avatar_component_clause,[],[f2662])).
% 2.75/0.74  fof(f2845,plain,(
% 2.75/0.74    ~spl5_4 | ~spl5_214 | spl5_57),
% 2.75/0.74    inference(avatar_split_clause,[],[f2840,f746,f2842,f87])).
% 2.75/0.74  fof(f746,plain,(
% 2.75/0.74    spl5_57 <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 2.75/0.74  fof(f2840,plain,(
% 2.75/0.74    k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl5_57),
% 2.75/0.74    inference(superposition,[],[f748,f69])).
% 2.75/0.74  fof(f69,plain,(
% 2.75/0.74    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f30])).
% 2.75/0.74  fof(f30,plain,(
% 2.75/0.74    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/0.74    inference(ennf_transformation,[],[f10])).
% 2.75/0.74  fof(f10,axiom,(
% 2.75/0.74    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.75/0.74  fof(f748,plain,(
% 2.75/0.74    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) | spl5_57),
% 2.75/0.74    inference(avatar_component_clause,[],[f746])).
% 2.75/0.74  fof(f2839,plain,(
% 2.75/0.74    ~spl5_116 | spl5_213 | ~spl5_115),
% 2.75/0.74    inference(avatar_split_clause,[],[f2818,f1949,f2837,f1954])).
% 2.75/0.74  fof(f1954,plain,(
% 2.75/0.74    spl5_116 <=> v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).
% 2.75/0.74  fof(f2837,plain,(
% 2.75/0.74    spl5_213 <=> ! [X16,X18,X17] : (v4_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).
% 2.75/0.74  fof(f1949,plain,(
% 2.75/0.74    spl5_115 <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 2.75/0.74  fof(f2818,plain,(
% 2.75/0.74    ( ! [X17,X18,X16] : (v4_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.74    inference(resolution,[],[f2600,f433])).
% 2.75/0.74  fof(f433,plain,(
% 2.75/0.74    ( ! [X24,X23,X25,X22] : (r1_tarski(k1_relat_1(k7_relat_1(X23,k1_relat_1(k7_relat_1(X22,k7_relat_1(X24,X25))))),X24) | ~v1_relat_1(X23) | ~v1_relat_1(X22) | ~v1_relat_1(X24)) )),
% 2.75/0.74    inference(resolution,[],[f390,f211])).
% 2.75/0.74  fof(f211,plain,(
% 2.75/0.74    ( ! [X4,X5,X3] : (~r1_tarski(X3,k7_relat_1(X4,X5)) | r1_tarski(X3,X4) | ~v1_relat_1(X4)) )),
% 2.75/0.74    inference(resolution,[],[f68,f59])).
% 2.75/0.74  fof(f59,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f22])).
% 2.75/0.74  fof(f22,plain,(
% 2.75/0.74    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(ennf_transformation,[],[f8])).
% 2.75/0.74  fof(f8,axiom,(
% 2.75/0.74    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 2.75/0.74  fof(f68,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f29])).
% 2.75/0.74  fof(f29,plain,(
% 2.75/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.75/0.74    inference(flattening,[],[f28])).
% 2.75/0.74  fof(f28,plain,(
% 2.75/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.75/0.74    inference(ennf_transformation,[],[f1])).
% 2.75/0.74  fof(f1,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.75/0.74  fof(f390,plain,(
% 2.75/0.74    ( ! [X6,X8,X7] : (r1_tarski(k1_relat_1(k7_relat_1(X6,k1_relat_1(k7_relat_1(X7,X8)))),X8) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 2.75/0.74    inference(resolution,[],[f212,f60])).
% 2.75/0.74  fof(f60,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f23])).
% 2.75/0.74  fof(f23,plain,(
% 2.75/0.74    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.75/0.74    inference(ennf_transformation,[],[f7])).
% 2.75/0.74  fof(f7,axiom,(
% 2.75/0.74    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.75/0.74  fof(f212,plain,(
% 2.75/0.74    ( ! [X6,X8,X7] : (~r1_tarski(X6,k1_relat_1(k7_relat_1(X8,X7))) | r1_tarski(X6,X7) | ~v1_relat_1(X8)) )),
% 2.75/0.74    inference(resolution,[],[f68,f60])).
% 2.75/0.74  fof(f2600,plain,(
% 2.75/0.74    ( ! [X1] : (~r1_tarski(X1,k7_relat_1(sK3,u1_struct_0(sK2))) | v4_relat_1(X1,u1_struct_0(sK2))) ) | ~spl5_115),
% 2.75/0.74    inference(resolution,[],[f2283,f192])).
% 2.75/0.74  fof(f192,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 2.75/0.74    inference(resolution,[],[f66,f64])).
% 2.75/0.74  fof(f64,plain,(
% 2.75/0.74    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f40])).
% 2.75/0.74  fof(f66,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f27])).
% 2.75/0.74  fof(f27,plain,(
% 2.75/0.74    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/0.74    inference(ennf_transformation,[],[f9])).
% 2.75/0.74  fof(f9,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.75/0.74  fof(f2283,plain,(
% 2.75/0.74    ( ! [X3] : (r1_tarski(X3,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~r1_tarski(X3,k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.74    inference(resolution,[],[f1950,f68])).
% 2.75/0.74  fof(f1950,plain,(
% 2.75/0.74    r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~spl5_115),
% 2.75/0.74    inference(avatar_component_clause,[],[f1949])).
% 2.75/0.74  fof(f2835,plain,(
% 2.75/0.74    ~spl5_116 | spl5_212 | ~spl5_115),
% 2.75/0.74    inference(avatar_split_clause,[],[f2816,f1949,f2833,f1954])).
% 2.75/0.74  fof(f2833,plain,(
% 2.75/0.74    spl5_212 <=> ! [X13,X12] : (v4_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK2)) | ~v1_relat_1(X12))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).
% 2.75/0.74  fof(f2816,plain,(
% 2.75/0.74    ( ! [X12,X13] : (v4_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X12)) ) | ~spl5_115),
% 2.75/0.74    inference(resolution,[],[f2600,f252])).
% 2.75/0.74  fof(f252,plain,(
% 2.75/0.74    ( ! [X6,X8,X7] : (r1_tarski(k1_relat_1(k7_relat_1(X6,k7_relat_1(X7,X8))),X7) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 2.75/0.74    inference(resolution,[],[f211,f60])).
% 2.75/0.74  fof(f2831,plain,(
% 2.75/0.74    ~spl5_116 | spl5_211 | ~spl5_115),
% 2.75/0.74    inference(avatar_split_clause,[],[f2812,f1949,f2829,f1954])).
% 2.75/0.74  fof(f2829,plain,(
% 2.75/0.74    spl5_211 <=> ! [X5,X4,X6] : (v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)))),
% 2.75/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).
% 2.75/0.74  fof(f2812,plain,(
% 2.75/0.74    ( ! [X6,X4,X5] : (v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.74    inference(resolution,[],[f2600,f426])).
% 2.75/0.74  fof(f426,plain,(
% 2.75/0.74    ( ! [X24,X23,X25,X22] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24),X25),X22) | ~v1_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24)) | ~v1_relat_1(X22)) )),
% 2.75/0.74    inference(global_subsumption,[],[f181,f420])).
% 2.75/0.74  fof(f420,plain,(
% 2.75/0.74    ( ! [X24,X23,X25,X22] : (~v1_relat_1(k7_relat_1(X22,X23)) | ~v1_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24)) | r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(X22,X23),X24),X25),X22) | ~v1_relat_1(X22)) )),
% 2.75/0.74    inference(resolution,[],[f251,f211])).
% 2.75/0.74  fof(f251,plain,(
% 2.75/0.74    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(X3,X4),X5),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 2.75/0.74    inference(resolution,[],[f211,f59])).
% 2.75/0.74  fof(f181,plain,(
% 2.75/0.74    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(duplicate_literal_removal,[],[f179])).
% 2.75/0.74  fof(f179,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(resolution,[],[f156,f59])).
% 2.75/0.74  fof(f156,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 2.75/0.74    inference(resolution,[],[f55,f64])).
% 2.75/0.74  fof(f55,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f18])).
% 2.75/0.74  fof(f18,plain,(
% 2.75/0.74    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.75/0.74    inference(ennf_transformation,[],[f3])).
% 2.75/0.74  fof(f3,axiom,(
% 2.75/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.75/0.74  fof(f2827,plain,(
% 2.75/0.74    ~spl5_116 | spl5_210 | ~spl5_115),
% 2.75/0.74    inference(avatar_split_clause,[],[f2811,f1949,f2825,f1954])).
% 2.75/0.75  fof(f2825,plain,(
% 2.75/0.75    spl5_210 <=> ! [X3,X2] : (v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).
% 2.75/0.75  fof(f2811,plain,(
% 2.75/0.75    ( ! [X2,X3] : (v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2600,f251])).
% 2.75/0.75  fof(f2823,plain,(
% 2.75/0.75    ~spl5_116 | spl5_209 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2810,f1949,f2821,f1954])).
% 2.75/0.75  fof(f2821,plain,(
% 2.75/0.75    spl5_209 <=> ! [X1] : v4_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).
% 2.75/0.75  fof(f2810,plain,(
% 2.75/0.75    ( ! [X1] : (v4_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2600,f59])).
% 2.75/0.75  fof(f2803,plain,(
% 2.75/0.75    ~spl5_116 | spl5_208 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2782,f1949,f2801,f1954])).
% 2.75/0.75  fof(f2801,plain,(
% 2.75/0.75    spl5_208 <=> ! [X16,X18,X17] : (v5_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).
% 2.75/0.75  fof(f2782,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (v5_relat_1(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2599,f433])).
% 2.75/0.75  fof(f2599,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(X0,k7_relat_1(sK3,u1_struct_0(sK2))) | v5_relat_1(X0,u1_struct_0(sK0))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2283,f204])).
% 2.75/0.75  fof(f204,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 2.75/0.75    inference(resolution,[],[f67,f64])).
% 2.75/0.75  fof(f67,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f27])).
% 2.75/0.75  fof(f2799,plain,(
% 2.75/0.75    ~spl5_116 | spl5_207 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2780,f1949,f2797,f1954])).
% 2.75/0.75  fof(f2797,plain,(
% 2.75/0.75    spl5_207 <=> ! [X13,X12] : (v5_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK0)) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).
% 2.75/0.75  fof(f2780,plain,(
% 2.75/0.75    ( ! [X12,X13] : (v5_relat_1(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X12)) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2599,f252])).
% 2.75/0.75  fof(f2795,plain,(
% 2.75/0.75    ~spl5_116 | spl5_206 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2776,f1949,f2793,f1954])).
% 2.75/0.75  fof(f2793,plain,(
% 2.75/0.75    spl5_206 <=> ! [X5,X4,X6] : (v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).
% 2.75/0.75  fof(f2776,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2599,f426])).
% 2.75/0.75  fof(f2791,plain,(
% 2.75/0.75    ~spl5_116 | spl5_205 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2775,f1949,f2789,f1954])).
% 2.75/0.75  fof(f2789,plain,(
% 2.75/0.75    spl5_205 <=> ! [X3,X2] : (v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).
% 2.75/0.75  fof(f2775,plain,(
% 2.75/0.75    ( ! [X2,X3] : (v5_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2599,f251])).
% 2.75/0.75  fof(f2787,plain,(
% 2.75/0.75    ~spl5_116 | spl5_204 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2774,f1949,f2785,f1954])).
% 2.75/0.75  fof(f2785,plain,(
% 2.75/0.75    spl5_204 <=> ! [X1] : v5_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).
% 2.75/0.75  fof(f2774,plain,(
% 2.75/0.75    ( ! [X1] : (v5_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2599,f59])).
% 2.75/0.75  fof(f2761,plain,(
% 2.75/0.75    spl5_198),
% 2.75/0.75    inference(avatar_contradiction_clause,[],[f2760])).
% 2.75/0.75  fof(f2760,plain,(
% 2.75/0.75    $false | spl5_198),
% 2.75/0.75    inference(resolution,[],[f2732,f58])).
% 2.75/0.75  fof(f58,plain,(
% 2.75/0.75    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f5])).
% 2.75/0.75  fof(f5,axiom,(
% 2.75/0.75    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.75/0.75  fof(f2732,plain,(
% 2.75/0.75    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | spl5_198),
% 2.75/0.75    inference(avatar_component_clause,[],[f2730])).
% 2.75/0.75  fof(f2759,plain,(
% 2.75/0.75    ~spl5_182 | spl5_203 | ~spl5_16 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2646,f1949,f149,f2757,f2648])).
% 2.75/0.75  fof(f2648,plain,(
% 2.75/0.75    spl5_182 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).
% 2.75/0.75  fof(f2757,plain,(
% 2.75/0.75    spl5_203 <=> ! [X60,X61] : (~r1_tarski(k7_relat_1(X60,X61),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X60) | ~v1_relat_1(k7_relat_1(X60,X61)) | v4_relat_1(k7_relat_1(X60,X61),X61))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).
% 2.75/0.75  fof(f149,plain,(
% 2.75/0.75    spl5_16 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.75/0.75  fof(f2646,plain,(
% 2.75/0.75    ( ! [X61,X60] : (~r1_tarski(k7_relat_1(X60,X61),k7_relat_1(sK3,u1_struct_0(sK2))) | v4_relat_1(k7_relat_1(X60,X61),X61) | ~v1_relat_1(k7_relat_1(X60,X61)) | ~v1_relat_1(X60) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)) ) | (~spl5_16 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1366])).
% 2.75/0.75  fof(f1366,plain,(
% 2.75/0.75    ( ! [X21,X22,X20] : (~r1_tarski(k7_relat_1(X20,X21),X22) | v4_relat_1(k7_relat_1(X20,X21),X21) | ~v1_relat_1(k7_relat_1(X20,X21)) | ~v1_relat_1(X20) | ~r1_tarski(X22,sK3)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f802,f275])).
% 2.75/0.75  fof(f275,plain,(
% 2.75/0.75    ( ! [X0,X1] : (v5_relat_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,sK3)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f229,f204])).
% 2.75/0.75  fof(f229,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(X2,sK3) | ~r1_tarski(X3,X2)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f213,f68])).
% 2.75/0.75  fof(f213,plain,(
% 2.75/0.75    ( ! [X9] : (r1_tarski(X9,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(X9,sK3)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f68,f151])).
% 2.75/0.75  fof(f151,plain,(
% 2.75/0.75    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~spl5_16),
% 2.75/0.75    inference(avatar_component_clause,[],[f149])).
% 2.75/0.75  fof(f802,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~v5_relat_1(k7_relat_1(X0,X1),X2) | ~v1_relat_1(X0) | v4_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(k7_relat_1(X0,X1))) )),
% 2.75/0.75    inference(resolution,[],[f789,f61])).
% 2.75/0.75  fof(f61,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f39])).
% 2.75/0.75  fof(f39,plain,(
% 2.75/0.75    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.75/0.75    inference(nnf_transformation,[],[f24])).
% 2.75/0.75  fof(f24,plain,(
% 2.75/0.75    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.75/0.75    inference(ennf_transformation,[],[f4])).
% 2.75/0.75  fof(f4,axiom,(
% 2.75/0.75    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.75/0.75  fof(f789,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | v4_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 2.75/0.75    inference(global_subsumption,[],[f181,f774])).
% 2.75/0.75  fof(f774,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | v4_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 2.75/0.75    inference(resolution,[],[f751,f60])).
% 2.75/0.75  fof(f751,plain,(
% 2.75/0.75    ( ! [X4,X5,X3] : (~r1_tarski(k1_relat_1(X3),X5) | ~r1_tarski(k2_relat_1(X3),X4) | ~v1_relat_1(X3) | v4_relat_1(X3,X5)) )),
% 2.75/0.75    inference(resolution,[],[f65,f66])).
% 2.75/0.75  fof(f2755,plain,(
% 2.75/0.75    ~spl5_184 | spl5_202 | ~spl5_2 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2641,f1949,f77,f2751,f2657])).
% 2.75/0.75  fof(f2657,plain,(
% 2.75/0.75    spl5_184 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).
% 2.75/0.75  fof(f2751,plain,(
% 2.75/0.75    spl5_202 <=> ! [X45,X47] : (~r1_tarski(k1_relat_1(X45),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_relat_1(X45),X47) | v4_relat_1(X45,u1_struct_0(sK2)) | ~v1_relat_1(X45))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).
% 2.75/0.75  fof(f2641,plain,(
% 2.75/0.75    ( ! [X50,X51] : (~r1_tarski(k1_relat_1(X50),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X50) | v4_relat_1(X50,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | ~r1_tarski(k2_relat_1(X50),X51)) ) | (~spl5_2 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f780])).
% 2.75/0.75  fof(f780,plain,(
% 2.75/0.75    ( ! [X26,X24,X25] : (~r1_tarski(k1_relat_1(X24),X26) | ~v1_relat_1(X24) | v4_relat_1(X24,u1_struct_0(sK2)) | ~r1_tarski(X26,sK4) | ~r1_tarski(k2_relat_1(X24),X25)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f751,f216])).
% 2.75/0.75  fof(f216,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(X1,u1_struct_0(sK2)) | ~r1_tarski(X0,sK4) | ~r1_tarski(X1,X0)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f214,f68])).
% 2.75/0.75  fof(f214,plain,(
% 2.75/0.75    ( ! [X10] : (r1_tarski(X10,u1_struct_0(sK2)) | ~r1_tarski(X10,sK4)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f68,f79])).
% 2.75/0.75  fof(f79,plain,(
% 2.75/0.75    r1_tarski(sK4,u1_struct_0(sK2)) | ~spl5_2),
% 2.75/0.75    inference(avatar_component_clause,[],[f77])).
% 2.75/0.75  fof(f2754,plain,(
% 2.75/0.75    ~spl5_184 | spl5_201 | ~spl5_15 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2640,f1949,f144,f2747,f2657])).
% 2.75/0.75  fof(f2747,plain,(
% 2.75/0.75    spl5_201 <=> ! [X42,X44] : (~r1_tarski(k1_relat_1(X42),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_relat_1(X42),X44) | v4_relat_1(X42,u1_struct_0(sK1)) | ~v1_relat_1(X42))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).
% 2.75/0.75  fof(f144,plain,(
% 2.75/0.75    spl5_15 <=> r1_tarski(sK4,u1_struct_0(sK1))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.75/0.75  fof(f2640,plain,(
% 2.75/0.75    ( ! [X48,X49] : (~r1_tarski(k1_relat_1(X48),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X48) | v4_relat_1(X48,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | ~r1_tarski(k2_relat_1(X48),X49)) ) | (~spl5_15 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f784])).
% 2.75/0.75  fof(f784,plain,(
% 2.75/0.75    ( ! [X39,X38,X40] : (~r1_tarski(k1_relat_1(X38),X40) | ~v1_relat_1(X38) | v4_relat_1(X38,u1_struct_0(sK1)) | ~r1_tarski(X40,sK4) | ~r1_tarski(k2_relat_1(X38),X39)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f751,f219])).
% 2.75/0.75  fof(f219,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_tarski(X1,u1_struct_0(sK1)) | ~r1_tarski(X0,sK4) | ~r1_tarski(X1,X0)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f215,f68])).
% 2.75/0.75  fof(f215,plain,(
% 2.75/0.75    ( ! [X11] : (r1_tarski(X11,u1_struct_0(sK1)) | ~r1_tarski(X11,sK4)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f68,f146])).
% 2.75/0.75  fof(f146,plain,(
% 2.75/0.75    r1_tarski(sK4,u1_struct_0(sK1)) | ~spl5_15),
% 2.75/0.75    inference(avatar_component_clause,[],[f144])).
% 2.75/0.75  fof(f2753,plain,(
% 2.75/0.75    spl5_185 | spl5_202 | ~spl5_2 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2639,f1949,f77,f2751,f2662])).
% 2.75/0.75  fof(f2639,plain,(
% 2.75/0.75    ( ! [X47,X45,X46] : (~r1_tarski(k1_relat_1(X45),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X45) | v4_relat_1(X45,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X46) | ~r1_tarski(X46,sK4) | ~r1_tarski(k2_relat_1(X45),X47)) ) | (~spl5_2 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f779])).
% 2.75/0.75  fof(f779,plain,(
% 2.75/0.75    ( ! [X23,X21,X22,X20] : (~r1_tarski(k1_relat_1(X20),X22) | ~v1_relat_1(X20) | v4_relat_1(X20,u1_struct_0(sK2)) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,sK4) | ~r1_tarski(k2_relat_1(X20),X21)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f751,f240])).
% 2.75/0.75  fof(f240,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (r1_tarski(X2,u1_struct_0(sK2)) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,sK4) | ~r1_tarski(X2,X1)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f216,f68])).
% 2.75/0.75  fof(f2749,plain,(
% 2.75/0.75    spl5_185 | spl5_201 | ~spl5_15 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2638,f1949,f144,f2747,f2662])).
% 2.75/0.75  fof(f2638,plain,(
% 2.75/0.75    ( ! [X43,X44,X42] : (~r1_tarski(k1_relat_1(X42),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X42) | v4_relat_1(X42,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X43) | ~r1_tarski(X43,sK4) | ~r1_tarski(k2_relat_1(X42),X44)) ) | (~spl5_15 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f783])).
% 2.75/0.75  fof(f783,plain,(
% 2.75/0.75    ( ! [X37,X35,X36,X34] : (~r1_tarski(k1_relat_1(X34),X36) | ~v1_relat_1(X34) | v4_relat_1(X34,u1_struct_0(sK1)) | ~r1_tarski(X36,X37) | ~r1_tarski(X37,sK4) | ~r1_tarski(k2_relat_1(X34),X35)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f751,f245])).
% 2.75/0.75  fof(f245,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (r1_tarski(X2,u1_struct_0(sK1)) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,sK4) | ~r1_tarski(X2,X1)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f219,f68])).
% 2.75/0.75  fof(f2745,plain,(
% 2.75/0.75    spl5_189 | spl5_200 | ~spl5_15 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2635,f1949,f144,f2739,f2678])).
% 2.75/0.75  fof(f2678,plain,(
% 2.75/0.75    spl5_189 <=> ! [X7,X8] : (~r1_tarski(X7,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X8) | ~r1_tarski(X8,X7))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).
% 2.75/0.75  fof(f2739,plain,(
% 2.75/0.75    spl5_200 <=> ! [X29] : (~r1_tarski(k2_relat_1(X29),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X29) | v5_relat_1(X29,u1_struct_0(sK1)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).
% 2.75/0.75  fof(f2635,plain,(
% 2.75/0.75    ( ! [X39,X37,X38] : (~r1_tarski(k2_relat_1(X37),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X38) | ~r1_tarski(X38,X39) | ~r1_tarski(X39,sK4) | v5_relat_1(X37,u1_struct_0(sK1)) | ~v1_relat_1(X37)) ) | (~spl5_15 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f659])).
% 2.75/0.75  fof(f659,plain,(
% 2.75/0.75    ( ! [X45,X43,X46,X44] : (~r1_tarski(k2_relat_1(X46),X44) | ~r1_tarski(X44,X45) | ~r1_tarski(X45,X43) | ~r1_tarski(X43,sK4) | v5_relat_1(X46,u1_struct_0(sK1)) | ~v1_relat_1(X46)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f370,f62])).
% 2.75/0.75  fof(f62,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f39])).
% 2.75/0.75  fof(f370,plain,(
% 2.75/0.75    ( ! [X6,X4,X5,X3] : (r1_tarski(X6,u1_struct_0(sK1)) | ~r1_tarski(X4,sK4) | ~r1_tarski(X5,X3) | ~r1_tarski(X3,X4) | ~r1_tarski(X6,X5)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f245,f68])).
% 2.75/0.75  fof(f2744,plain,(
% 2.75/0.75    spl5_189 | spl5_199 | ~spl5_2 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2634,f1949,f77,f2735,f2678])).
% 2.75/0.75  fof(f2735,plain,(
% 2.75/0.75    spl5_199 <=> ! [X28] : (~r1_tarski(k2_relat_1(X28),k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X28) | v5_relat_1(X28,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).
% 2.75/0.75  fof(f2634,plain,(
% 2.75/0.75    ( ! [X35,X36,X34] : (~r1_tarski(k2_relat_1(X34),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X35) | ~r1_tarski(X35,X36) | ~r1_tarski(X36,sK4) | v5_relat_1(X34,u1_struct_0(sK2)) | ~v1_relat_1(X34)) ) | (~spl5_2 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f590])).
% 2.75/0.75  fof(f590,plain,(
% 2.75/0.75    ( ! [X37,X35,X38,X36] : (~r1_tarski(k2_relat_1(X38),X36) | ~r1_tarski(X36,X37) | ~r1_tarski(X37,X35) | ~r1_tarski(X35,sK4) | v5_relat_1(X38,u1_struct_0(sK2)) | ~v1_relat_1(X38)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f341,f62])).
% 2.75/0.75  fof(f341,plain,(
% 2.75/0.75    ( ! [X6,X4,X5,X3] : (r1_tarski(X6,u1_struct_0(sK2)) | ~r1_tarski(X4,sK4) | ~r1_tarski(X5,X3) | ~r1_tarski(X3,X4) | ~r1_tarski(X6,X5)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f240,f68])).
% 2.75/0.75  fof(f2743,plain,(
% 2.75/0.75    spl5_185 | spl5_200 | ~spl5_15 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2633,f1949,f144,f2739,f2662])).
% 2.75/0.75  fof(f2633,plain,(
% 2.75/0.75    ( ! [X33,X32] : (~r1_tarski(k2_relat_1(X32),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X33,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X33) | v5_relat_1(X32,u1_struct_0(sK1)) | ~v1_relat_1(X32)) ) | (~spl5_15 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f373])).
% 2.75/0.75  fof(f373,plain,(
% 2.75/0.75    ( ! [X14,X15,X13] : (~r1_tarski(k2_relat_1(X15),X13) | ~r1_tarski(X14,sK4) | ~r1_tarski(X13,X14) | v5_relat_1(X15,u1_struct_0(sK1)) | ~v1_relat_1(X15)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f245,f62])).
% 2.75/0.75  fof(f2742,plain,(
% 2.75/0.75    spl5_185 | spl5_199 | ~spl5_2 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2632,f1949,f77,f2735,f2662])).
% 2.75/0.75  fof(f2632,plain,(
% 2.75/0.75    ( ! [X30,X31] : (~r1_tarski(k2_relat_1(X30),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X31,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X31) | v5_relat_1(X30,u1_struct_0(sK2)) | ~v1_relat_1(X30)) ) | (~spl5_2 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f343])).
% 2.75/0.75  fof(f343,plain,(
% 2.75/0.75    ( ! [X12,X10,X11] : (~r1_tarski(k2_relat_1(X12),X10) | ~r1_tarski(X11,sK4) | ~r1_tarski(X10,X11) | v5_relat_1(X12,u1_struct_0(sK2)) | ~v1_relat_1(X12)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f240,f62])).
% 2.75/0.75  fof(f2741,plain,(
% 2.75/0.75    ~spl5_184 | spl5_200 | ~spl5_15 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2631,f1949,f144,f2739,f2657])).
% 2.75/0.75  fof(f2631,plain,(
% 2.75/0.75    ( ! [X29] : (~r1_tarski(k2_relat_1(X29),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | v5_relat_1(X29,u1_struct_0(sK1)) | ~v1_relat_1(X29)) ) | (~spl5_15 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f247])).
% 2.75/0.75  fof(f247,plain,(
% 2.75/0.75    ( ! [X6,X5] : (~r1_tarski(k2_relat_1(X6),X5) | ~r1_tarski(X5,sK4) | v5_relat_1(X6,u1_struct_0(sK1)) | ~v1_relat_1(X6)) ) | ~spl5_15),
% 2.75/0.75    inference(resolution,[],[f219,f62])).
% 2.75/0.75  fof(f2737,plain,(
% 2.75/0.75    ~spl5_184 | spl5_199 | ~spl5_2 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2630,f1949,f77,f2735,f2657])).
% 2.75/0.75  fof(f2630,plain,(
% 2.75/0.75    ( ! [X28] : (~r1_tarski(k2_relat_1(X28),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | v5_relat_1(X28,u1_struct_0(sK2)) | ~v1_relat_1(X28)) ) | (~spl5_2 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f242])).
% 2.75/0.75  fof(f242,plain,(
% 2.75/0.75    ( ! [X6,X5] : (~r1_tarski(k2_relat_1(X6),X5) | ~r1_tarski(X5,sK4) | v5_relat_1(X6,u1_struct_0(sK2)) | ~v1_relat_1(X6)) ) | ~spl5_2),
% 2.75/0.75    inference(resolution,[],[f216,f62])).
% 2.75/0.75  fof(f2733,plain,(
% 2.75/0.75    ~spl5_198 | spl5_197 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2628,f1949,f2724,f2730])).
% 2.75/0.75  fof(f2724,plain,(
% 2.75/0.75    spl5_197 <=> ! [X18] : (~r1_tarski(X18,k7_relat_1(sK3,u1_struct_0(sK2))) | v1_relat_1(X18))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).
% 2.75/0.75  fof(f2628,plain,(
% 2.75/0.75    ( ! [X26] : (~r1_tarski(X26,k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | v1_relat_1(X26)) ) | ~spl5_115),
% 2.75/0.75    inference(resolution,[],[f2283,f156])).
% 2.75/0.75  fof(f2728,plain,(
% 2.75/0.75    ~spl5_182 | spl5_197 | ~spl5_28 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2626,f1949,f281,f2724,f2648])).
% 2.75/0.75  fof(f281,plain,(
% 2.75/0.75    spl5_28 <=> ! [X7,X8] : (~r1_tarski(X7,sK3) | v1_relat_1(X8) | ~r1_tarski(X8,X7))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.75/0.75  fof(f2626,plain,(
% 2.75/0.75    ( ! [X23] : (~r1_tarski(X23,k7_relat_1(sK3,u1_struct_0(sK2))) | v1_relat_1(X23) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3)) ) | (~spl5_28 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f282])).
% 2.75/0.75  fof(f282,plain,(
% 2.75/0.75    ( ! [X8,X7] : (~r1_tarski(X8,X7) | v1_relat_1(X8) | ~r1_tarski(X7,sK3)) ) | ~spl5_28),
% 2.75/0.75    inference(avatar_component_clause,[],[f281])).
% 2.75/0.75  fof(f2727,plain,(
% 2.75/0.75    spl5_191 | spl5_197 | ~spl5_39 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2625,f1949,f449,f2724,f2688])).
% 2.75/0.75  fof(f449,plain,(
% 2.75/0.75    spl5_39 <=> ! [X7,X8,X6] : (~r1_tarski(X6,X7) | v1_relat_1(X8) | ~r1_tarski(X8,X6) | ~r1_tarski(X7,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.75/0.75  fof(f2625,plain,(
% 2.75/0.75    ( ! [X21,X22] : (~r1_tarski(X21,k7_relat_1(sK3,u1_struct_0(sK2))) | v1_relat_1(X21) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X22) | ~r1_tarski(X22,sK3)) ) | (~spl5_39 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f450])).
% 2.75/0.75  fof(f450,plain,(
% 2.75/0.75    ( ! [X6,X8,X7] : (~r1_tarski(X8,X6) | v1_relat_1(X8) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK3)) ) | ~spl5_39),
% 2.75/0.75    inference(avatar_component_clause,[],[f449])).
% 2.75/0.75  fof(f2726,plain,(
% 2.75/0.75    spl5_190 | spl5_197 | ~spl5_65 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2624,f1949,f921,f2724,f2684])).
% 2.75/0.75  fof(f2684,plain,(
% 2.75/0.75    spl5_190 <=> ! [X11,X10] : (~r1_tarski(X10,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X11) | ~r1_tarski(X11,X10))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).
% 2.75/0.75  fof(f921,plain,(
% 2.75/0.75    spl5_65 <=> ! [X20,X22,X21,X23] : (~r1_tarski(X20,sK3) | v1_relat_1(X23) | ~r1_tarski(X23,X21) | ~r1_tarski(X21,X22) | ~r1_tarski(X22,X20))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 2.75/0.75  fof(f2624,plain,(
% 2.75/0.75    ( ! [X19,X20,X18] : (~r1_tarski(X18,k7_relat_1(sK3,u1_struct_0(sK2))) | v1_relat_1(X18) | ~r1_tarski(X19,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X20) | ~r1_tarski(X20,X19)) ) | (~spl5_65 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f922])).
% 2.75/0.75  fof(f922,plain,(
% 2.75/0.75    ( ! [X23,X21,X22,X20] : (~r1_tarski(X23,X21) | v1_relat_1(X23) | ~r1_tarski(X20,sK3) | ~r1_tarski(X21,X22) | ~r1_tarski(X22,X20)) ) | ~spl5_65),
% 2.75/0.75    inference(avatar_component_clause,[],[f921])).
% 2.75/0.75  fof(f2722,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_196 | ~spl5_115 | ~spl5_166),
% 2.75/0.75    inference(avatar_split_clause,[],[f2623,f2450,f1949,f2719,f2657])).
% 2.75/0.75  fof(f2719,plain,(
% 2.75/0.75    spl5_196 <=> r1_tarski(sK3,k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).
% 2.75/0.75  fof(f2450,plain,(
% 2.75/0.75    spl5_166 <=> ! [X2] : (~r1_tarski(sK3,X2) | ~r1_tarski(X2,sK4))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).
% 2.75/0.75  fof(f2623,plain,(
% 2.75/0.75    ~r1_tarski(sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_115 | ~spl5_166)),
% 2.75/0.75    inference(resolution,[],[f2283,f2451])).
% 2.75/0.75  fof(f2451,plain,(
% 2.75/0.75    ( ! [X2] : (~r1_tarski(sK3,X2) | ~r1_tarski(X2,sK4)) ) | ~spl5_166),
% 2.75/0.75    inference(avatar_component_clause,[],[f2450])).
% 2.75/0.75  fof(f2717,plain,(
% 2.75/0.75    ~spl5_182 | ~spl5_195 | ~spl5_48 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2622,f1949,f556,f2711,f2648])).
% 2.75/0.75  fof(f2711,plain,(
% 2.75/0.75    spl5_195 <=> r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).
% 2.75/0.75  fof(f556,plain,(
% 2.75/0.75    spl5_48 <=> ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | ~r1_tarski(X0,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 2.75/0.75  fof(f2622,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) | (~spl5_48 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f557])).
% 2.75/0.75  fof(f557,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | ~r1_tarski(X0,sK3)) ) | ~spl5_48),
% 2.75/0.75    inference(avatar_component_clause,[],[f556])).
% 2.75/0.75  fof(f2716,plain,(
% 2.75/0.75    spl5_191 | ~spl5_195 | ~spl5_71 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2621,f1949,f1058,f2711,f2688])).
% 2.75/0.75  fof(f1058,plain,(
% 2.75/0.75    spl5_71 <=> ! [X1,X0] : (~r1_tarski(X0,sK3) | ~r1_tarski(u1_struct_0(sK0),X1) | ~r1_tarski(X1,X0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 2.75/0.75  fof(f2621,plain,(
% 2.75/0.75    ( ! [X17] : (~r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X17,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X17)) ) | (~spl5_71 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1059])).
% 2.75/0.75  fof(f1059,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK0),X1) | ~r1_tarski(X0,sK3) | ~r1_tarski(X1,X0)) ) | ~spl5_71),
% 2.75/0.75    inference(avatar_component_clause,[],[f1058])).
% 2.75/0.75  fof(f2715,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_195 | ~spl5_115 | ~spl5_127),
% 2.75/0.75    inference(avatar_split_clause,[],[f2620,f2070,f1949,f2711,f2657])).
% 2.75/0.75  fof(f2070,plain,(
% 2.75/0.75    spl5_127 <=> ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(u1_struct_0(sK0),X0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).
% 2.75/0.75  fof(f2620,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_115 | ~spl5_127)),
% 2.75/0.75    inference(resolution,[],[f2283,f2071])).
% 2.75/0.75  fof(f2071,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | ~r1_tarski(X0,sK4)) ) | ~spl5_127),
% 2.75/0.75    inference(avatar_component_clause,[],[f2070])).
% 2.75/0.75  fof(f2714,plain,(
% 2.75/0.75    spl5_185 | ~spl5_195 | ~spl5_115 | ~spl5_128),
% 2.75/0.75    inference(avatar_split_clause,[],[f2619,f2075,f1949,f2711,f2662])).
% 2.75/0.75  fof(f2075,plain,(
% 2.75/0.75    spl5_128 <=> ! [X3,X2] : (~r1_tarski(u1_struct_0(sK0),X2) | ~r1_tarski(X3,sK4) | ~r1_tarski(X2,X3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).
% 2.75/0.75  fof(f2619,plain,(
% 2.75/0.75    ( ! [X16] : (~r1_tarski(u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X16,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X16)) ) | (~spl5_115 | ~spl5_128)),
% 2.75/0.75    inference(resolution,[],[f2283,f2076])).
% 2.75/0.75  fof(f2076,plain,(
% 2.75/0.75    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(sK0),X2) | ~r1_tarski(X3,sK4) | ~r1_tarski(X2,X3)) ) | ~spl5_128),
% 2.75/0.75    inference(avatar_component_clause,[],[f2075])).
% 2.75/0.75  fof(f2709,plain,(
% 2.75/0.75    ~spl5_182 | ~spl5_194 | ~spl5_42 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2618,f1949,f481,f2704,f2648])).
% 2.75/0.75  fof(f2704,plain,(
% 2.75/0.75    spl5_194 <=> r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).
% 2.75/0.75  fof(f481,plain,(
% 2.75/0.75    spl5_42 <=> ! [X10] : (~r1_tarski(u1_struct_0(sK1),X10) | ~r1_tarski(X10,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 2.75/0.75  fof(f2618,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) | (~spl5_42 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f482])).
% 2.75/0.75  fof(f482,plain,(
% 2.75/0.75    ( ! [X10] : (~r1_tarski(u1_struct_0(sK1),X10) | ~r1_tarski(X10,sK3)) ) | ~spl5_42),
% 2.75/0.75    inference(avatar_component_clause,[],[f481])).
% 2.75/0.75  fof(f2708,plain,(
% 2.75/0.75    spl5_191 | ~spl5_194 | ~spl5_67 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2617,f1949,f958,f2704,f2688])).
% 2.75/0.75  fof(f958,plain,(
% 2.75/0.75    spl5_67 <=> ! [X20,X19] : (~r1_tarski(X19,sK3) | ~r1_tarski(u1_struct_0(sK1),X20) | ~r1_tarski(X20,X19))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 2.75/0.75  fof(f2617,plain,(
% 2.75/0.75    ( ! [X15] : (~r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X15,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X15)) ) | (~spl5_67 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f959])).
% 2.75/0.75  fof(f959,plain,(
% 2.75/0.75    ( ! [X19,X20] : (~r1_tarski(u1_struct_0(sK1),X20) | ~r1_tarski(X19,sK3) | ~r1_tarski(X20,X19)) ) | ~spl5_67),
% 2.75/0.75    inference(avatar_component_clause,[],[f958])).
% 2.75/0.75  fof(f2707,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_194 | ~spl5_79 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2616,f1949,f1190,f2704,f2657])).
% 2.75/0.75  fof(f1190,plain,(
% 2.75/0.75    spl5_79 <=> ! [X15] : (~r1_tarski(u1_struct_0(sK1),X15) | ~r1_tarski(X15,sK4))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 2.75/0.75  fof(f2616,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_79 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1191])).
% 2.75/0.75  fof(f1191,plain,(
% 2.75/0.75    ( ! [X15] : (~r1_tarski(u1_struct_0(sK1),X15) | ~r1_tarski(X15,sK4)) ) | ~spl5_79),
% 2.75/0.75    inference(avatar_component_clause,[],[f1190])).
% 2.75/0.75  fof(f2702,plain,(
% 2.75/0.75    ~spl5_182 | ~spl5_193 | ~spl5_40 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2615,f1949,f472,f2697,f2648])).
% 2.75/0.75  fof(f2697,plain,(
% 2.75/0.75    spl5_193 <=> r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).
% 2.75/0.75  fof(f472,plain,(
% 2.75/0.75    spl5_40 <=> ! [X1] : (~r1_tarski(u1_struct_0(sK2),X1) | ~r1_tarski(X1,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.75/0.75  fof(f2615,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) | (~spl5_40 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f473])).
% 2.75/0.75  fof(f473,plain,(
% 2.75/0.75    ( ! [X1] : (~r1_tarski(u1_struct_0(sK2),X1) | ~r1_tarski(X1,sK3)) ) | ~spl5_40),
% 2.75/0.75    inference(avatar_component_clause,[],[f472])).
% 2.75/0.75  fof(f2701,plain,(
% 2.75/0.75    spl5_191 | ~spl5_193 | ~spl5_46 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2614,f1949,f522,f2697,f2688])).
% 2.75/0.75  fof(f522,plain,(
% 2.75/0.75    spl5_46 <=> ! [X7,X6] : (~r1_tarski(X6,X7) | ~r1_tarski(u1_struct_0(sK2),X6) | ~r1_tarski(X7,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.75/0.75  fof(f2614,plain,(
% 2.75/0.75    ( ! [X14] : (~r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X14) | ~r1_tarski(X14,sK3)) ) | (~spl5_46 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f523])).
% 2.75/0.75  fof(f523,plain,(
% 2.75/0.75    ( ! [X6,X7] : (~r1_tarski(u1_struct_0(sK2),X6) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK3)) ) | ~spl5_46),
% 2.75/0.75    inference(avatar_component_clause,[],[f522])).
% 2.75/0.75  fof(f2700,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_193 | ~spl5_73 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2613,f1949,f1134,f2697,f2657])).
% 2.75/0.75  fof(f1134,plain,(
% 2.75/0.75    spl5_73 <=> ! [X83] : (~r1_tarski(X83,sK4) | ~r1_tarski(u1_struct_0(sK2),X83))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 2.75/0.75  fof(f2613,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_73 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1135])).
% 2.75/0.75  fof(f1135,plain,(
% 2.75/0.75    ( ! [X83] : (~r1_tarski(u1_struct_0(sK2),X83) | ~r1_tarski(X83,sK4)) ) | ~spl5_73),
% 2.75/0.75    inference(avatar_component_clause,[],[f1134])).
% 2.75/0.75  fof(f2695,plain,(
% 2.75/0.75    spl5_192 | ~spl5_187 | ~spl5_113 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2612,f1949,f1761,f2669,f2693])).
% 2.75/0.75  fof(f2693,plain,(
% 2.75/0.75    spl5_192 <=> ! [X13] : (~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) | ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X13),sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).
% 2.75/0.75  fof(f2669,plain,(
% 2.75/0.75    spl5_187 <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).
% 2.75/0.75  fof(f1761,plain,(
% 2.75/0.75    spl5_113 <=> ! [X27,X26] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK3) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 2.75/0.75  fof(f2612,plain,(
% 2.75/0.75    ( ! [X13] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) | ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X13),sK3)) ) | (~spl5_113 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1762])).
% 2.75/0.75  fof(f1762,plain,(
% 2.75/0.75    ( ! [X26,X27] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27) | ~r1_tarski(k2_zfmisc_1(X26,X27),sK3)) ) | ~spl5_113),
% 2.75/0.75    inference(avatar_component_clause,[],[f1761])).
% 2.75/0.75  fof(f2691,plain,(
% 2.75/0.75    ~spl5_182 | ~spl5_187 | ~spl5_95 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2611,f1949,f1568,f2669,f2648])).
% 2.75/0.75  fof(f1568,plain,(
% 2.75/0.75    spl5_95 <=> ! [X38] : (~r1_tarski(X38,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 2.75/0.75  fof(f2611,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) | (~spl5_95 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1569])).
% 2.75/0.75  fof(f1569,plain,(
% 2.75/0.75    ( ! [X38] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38) | ~r1_tarski(X38,sK3)) ) | ~spl5_95),
% 2.75/0.75    inference(avatar_component_clause,[],[f1568])).
% 2.75/0.75  fof(f2690,plain,(
% 2.75/0.75    spl5_191 | ~spl5_187 | ~spl5_94 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2610,f1949,f1564,f2669,f2688])).
% 2.75/0.75  fof(f1564,plain,(
% 2.75/0.75    spl5_94 <=> ! [X36,X35] : (~r1_tarski(X35,X36) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35) | ~r1_tarski(X36,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 2.75/0.75  fof(f2610,plain,(
% 2.75/0.75    ( ! [X12] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X12) | ~r1_tarski(X12,sK3)) ) | (~spl5_94 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1565])).
% 2.75/0.75  fof(f1565,plain,(
% 2.75/0.75    ( ! [X35,X36] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35) | ~r1_tarski(X35,X36) | ~r1_tarski(X36,sK3)) ) | ~spl5_94),
% 2.75/0.75    inference(avatar_component_clause,[],[f1564])).
% 2.75/0.75  fof(f2686,plain,(
% 2.75/0.75    spl5_190 | ~spl5_187 | ~spl5_92 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2609,f1949,f1557,f2669,f2684])).
% 2.75/0.75  fof(f1557,plain,(
% 2.75/0.75    spl5_92 <=> ! [X32,X31,X33] : (~r1_tarski(X31,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32) | ~r1_tarski(X32,X33) | ~r1_tarski(X33,X31))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 2.75/0.75  fof(f2609,plain,(
% 2.75/0.75    ( ! [X10,X11] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X10,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X11) | ~r1_tarski(X11,X10)) ) | (~spl5_92 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1558])).
% 2.75/0.75  fof(f1558,plain,(
% 2.75/0.75    ( ! [X33,X31,X32] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32) | ~r1_tarski(X31,sK3) | ~r1_tarski(X32,X33) | ~r1_tarski(X33,X31)) ) | ~spl5_92),
% 2.75/0.75    inference(avatar_component_clause,[],[f1557])).
% 2.75/0.75  fof(f2682,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_187 | ~spl5_89 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2608,f1949,f1540,f2669,f2657])).
% 2.75/0.75  fof(f1540,plain,(
% 2.75/0.75    spl5_89 <=> ! [X13] : (~r1_tarski(X13,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 2.75/0.75  fof(f2608,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_89 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1541])).
% 2.75/0.75  fof(f1541,plain,(
% 2.75/0.75    ( ! [X13] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) | ~r1_tarski(X13,sK4)) ) | ~spl5_89),
% 2.75/0.75    inference(avatar_component_clause,[],[f1540])).
% 2.75/0.75  fof(f2681,plain,(
% 2.75/0.75    spl5_185 | ~spl5_187 | ~spl5_88 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2607,f1949,f1536,f2669,f2662])).
% 2.75/0.75  fof(f1536,plain,(
% 2.75/0.75    spl5_88 <=> ! [X11,X10] : (~r1_tarski(X10,X11) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10) | ~r1_tarski(X11,sK4))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 2.75/0.75  fof(f2607,plain,(
% 2.75/0.75    ( ! [X9] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X9) | ~r1_tarski(X9,sK4)) ) | (~spl5_88 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1537])).
% 2.75/0.75  fof(f1537,plain,(
% 2.75/0.75    ( ! [X10,X11] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10) | ~r1_tarski(X10,X11) | ~r1_tarski(X11,sK4)) ) | ~spl5_88),
% 2.75/0.75    inference(avatar_component_clause,[],[f1536])).
% 2.75/0.75  fof(f2680,plain,(
% 2.75/0.75    spl5_189 | ~spl5_187 | ~spl5_87 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2606,f1949,f1532,f2669,f2678])).
% 2.75/0.75  fof(f1532,plain,(
% 2.75/0.75    spl5_87 <=> ! [X7,X8,X6] : (~r1_tarski(X6,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 2.75/0.75  fof(f2606,plain,(
% 2.75/0.75    ( ! [X8,X7] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X7,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X8) | ~r1_tarski(X8,X7)) ) | (~spl5_87 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1533])).
% 2.75/0.75  fof(f1533,plain,(
% 2.75/0.75    ( ! [X6,X8,X7] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7) | ~r1_tarski(X6,sK4) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6)) ) | ~spl5_87),
% 2.75/0.75    inference(avatar_component_clause,[],[f1532])).
% 2.75/0.75  fof(f2676,plain,(
% 2.75/0.75    spl5_188 | ~spl5_187 | ~spl5_85 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2605,f1949,f1525,f2669,f2674])).
% 2.75/0.75  fof(f2674,plain,(
% 2.75/0.75    spl5_188 <=> ! [X5,X4,X6] : (~r1_tarski(X4,X5) | ~r1_tarski(X5,X6) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X4) | ~r1_tarski(X6,sK4))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).
% 2.75/0.75  fof(f1525,plain,(
% 2.75/0.75    spl5_85 <=> ! [X1,X3,X2,X4] : (~r1_tarski(X1,X2) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) | ~r1_tarski(X3,sK4) | ~r1_tarski(X4,X1) | ~r1_tarski(X2,X3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 2.75/0.75  fof(f2605,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(X4,X5) | ~r1_tarski(X6,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X4) | ~r1_tarski(X5,X6)) ) | (~spl5_85 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f1526])).
% 2.75/0.75  fof(f1526,plain,(
% 2.75/0.75    ( ! [X4,X2,X3,X1] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) | ~r1_tarski(X1,X2) | ~r1_tarski(X3,sK4) | ~r1_tarski(X4,X1) | ~r1_tarski(X2,X3)) ) | ~spl5_85),
% 2.75/0.75    inference(avatar_component_clause,[],[f1525])).
% 2.75/0.75  fof(f2672,plain,(
% 2.75/0.75    spl5_186 | ~spl5_187 | ~spl5_63 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2604,f1949,f893,f2669,f2666])).
% 2.75/0.75  fof(f2666,plain,(
% 2.75/0.75    spl5_186 <=> ! [X3] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X3),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).
% 2.75/0.75  fof(f893,plain,(
% 2.75/0.75    spl5_63 <=> ! [X13,X12] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12) | ~r1_tarski(k2_zfmisc_1(X12,X13),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 2.75/0.75  fof(f2604,plain,(
% 2.75/0.75    ( ! [X3] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X3),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X3)) ) | (~spl5_63 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f894])).
% 2.75/0.75  fof(f894,plain,(
% 2.75/0.75    ( ! [X12,X13] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12) | ~r1_tarski(k2_zfmisc_1(X12,X13),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)) ) | ~spl5_63),
% 2.75/0.75    inference(avatar_component_clause,[],[f893])).
% 2.75/0.75  fof(f2664,plain,(
% 2.75/0.75    spl5_185 | ~spl5_183 | ~spl5_54 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2603,f1949,f635,f2652,f2662])).
% 2.75/0.75  fof(f2652,plain,(
% 2.75/0.75    spl5_183 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).
% 2.75/0.75  fof(f635,plain,(
% 2.75/0.75    spl5_54 <=> ! [X7,X6] : (~r1_tarski(X6,X7) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6) | ~r1_tarski(X7,sK4))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 2.75/0.75  fof(f2603,plain,(
% 2.75/0.75    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),X2) | ~r1_tarski(X2,sK4)) ) | (~spl5_54 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f636])).
% 2.75/0.75  fof(f636,plain,(
% 2.75/0.75    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK4)) ) | ~spl5_54),
% 2.75/0.75    inference(avatar_component_clause,[],[f635])).
% 2.75/0.75  fof(f2660,plain,(
% 2.75/0.75    ~spl5_184 | ~spl5_183 | ~spl5_53 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2602,f1949,f619,f2652,f2657])).
% 2.75/0.75  fof(f619,plain,(
% 2.75/0.75    spl5_53 <=> ! [X26] : (~r1_tarski(X26,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 2.75/0.75  fof(f2602,plain,(
% 2.75/0.75    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK4) | (~spl5_53 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f620])).
% 2.75/0.75  fof(f620,plain,(
% 2.75/0.75    ( ! [X26] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26) | ~r1_tarski(X26,sK4)) ) | ~spl5_53),
% 2.75/0.75    inference(avatar_component_clause,[],[f619])).
% 2.75/0.75  fof(f2655,plain,(
% 2.75/0.75    ~spl5_182 | ~spl5_183 | ~spl5_64 | ~spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2601,f1949,f918,f2652,f2648])).
% 2.75/0.75  fof(f918,plain,(
% 2.75/0.75    spl5_64 <=> ! [X24] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24) | ~r1_tarski(X24,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 2.75/0.75  fof(f2601,plain,(
% 2.75/0.75    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)),sK3) | (~spl5_64 | ~spl5_115)),
% 2.75/0.75    inference(resolution,[],[f2283,f919])).
% 2.75/0.75  fof(f919,plain,(
% 2.75/0.75    ( ! [X24] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24) | ~r1_tarski(X24,sK3)) ) | ~spl5_64),
% 2.75/0.75    inference(avatar_component_clause,[],[f918])).
% 2.75/0.75  fof(f2565,plain,(
% 2.75/0.75    ~spl5_137 | spl5_181 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2543,f765,f2563,f2177])).
% 2.75/0.75  fof(f2177,plain,(
% 2.75/0.75    spl5_137 <=> v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).
% 2.75/0.75  fof(f2563,plain,(
% 2.75/0.75    spl5_181 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).
% 2.75/0.75  fof(f765,plain,(
% 2.75/0.75    spl5_60 <=> r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 2.75/0.75  fof(f2543,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f2199,f433])).
% 2.75/0.75  fof(f2199,plain,(
% 2.75/0.75    ( ! [X9] : (~r1_tarski(X9,k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | r1_tarski(X9,u1_struct_0(sK0))) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f766,f68])).
% 2.75/0.75  fof(f766,plain,(
% 2.75/0.75    r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0)) | ~spl5_60),
% 2.75/0.75    inference(avatar_component_clause,[],[f765])).
% 2.75/0.75  fof(f2561,plain,(
% 2.75/0.75    ~spl5_137 | spl5_180 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2541,f765,f2559,f2177])).
% 2.75/0.75  fof(f2559,plain,(
% 2.75/0.75    spl5_180 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK0)) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).
% 2.75/0.75  fof(f2541,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | ~v1_relat_1(X12)) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f2199,f252])).
% 2.75/0.75  fof(f2557,plain,(
% 2.75/0.75    ~spl5_137 | spl5_179 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2537,f765,f2555,f2177])).
% 2.75/0.75  fof(f2555,plain,(
% 2.75/0.75    spl5_179 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).
% 2.75/0.75  fof(f2537,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f2199,f426])).
% 2.75/0.75  fof(f2553,plain,(
% 2.75/0.75    ~spl5_137 | spl5_178 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2536,f765,f2551,f2177])).
% 2.75/0.75  fof(f2551,plain,(
% 2.75/0.75    spl5_178 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).
% 2.75/0.75  fof(f2536,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | ~v1_relat_1(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2))) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f2199,f251])).
% 2.75/0.75  fof(f2549,plain,(
% 2.75/0.75    ~spl5_137 | spl5_177 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2535,f765,f2547,f2177])).
% 2.75/0.75  fof(f2547,plain,(
% 2.75/0.75    spl5_177 <=> ! [X1] : r1_tarski(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).
% 2.75/0.75  fof(f2535,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_60),
% 2.75/0.75    inference(resolution,[],[f2199,f59])).
% 2.75/0.75  fof(f2532,plain,(
% 2.75/0.75    ~spl5_171 | spl5_176 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2506,f761,f2530,f2510])).
% 2.75/0.75  fof(f2510,plain,(
% 2.75/0.75    spl5_171 <=> v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).
% 2.75/0.75  fof(f2530,plain,(
% 2.75/0.75    spl5_176 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).
% 2.75/0.75  fof(f761,plain,(
% 2.75/0.75    spl5_59 <=> r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 2.75/0.75  fof(f2506,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f2141,f433])).
% 2.75/0.75  fof(f2141,plain,(
% 2.75/0.75    ( ! [X10] : (~r1_tarski(X10,k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | r1_tarski(X10,u1_struct_0(sK2))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f762,f68])).
% 2.75/0.75  fof(f762,plain,(
% 2.75/0.75    r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2)) | ~spl5_59),
% 2.75/0.75    inference(avatar_component_clause,[],[f761])).
% 2.75/0.75  fof(f2528,plain,(
% 2.75/0.75    ~spl5_171 | spl5_175 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2504,f761,f2526,f2510])).
% 2.75/0.75  fof(f2526,plain,(
% 2.75/0.75    spl5_175 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK2)) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).
% 2.75/0.75  fof(f2504,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X13))),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | ~v1_relat_1(X12)) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f2141,f252])).
% 2.75/0.75  fof(f2524,plain,(
% 2.75/0.75    ~spl5_171 | spl5_174 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2500,f761,f2522,f2510])).
% 2.75/0.75  fof(f2522,plain,(
% 2.75/0.75    spl5_174 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).
% 2.75/0.75  fof(f2500,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X4),X5)) | ~v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f2141,f426])).
% 2.75/0.75  fof(f2520,plain,(
% 2.75/0.75    ~spl5_171 | spl5_173 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2499,f761,f2518,f2510])).
% 2.75/0.75  fof(f2518,plain,(
% 2.75/0.75    spl5_173 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).
% 2.75/0.75  fof(f2499,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | ~v1_relat_1(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X2))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f2141,f251])).
% 2.75/0.75  fof(f2516,plain,(
% 2.75/0.75    ~spl5_171 | spl5_172 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2498,f761,f2514,f2510])).
% 2.75/0.75  fof(f2514,plain,(
% 2.75/0.75    spl5_172 <=> ! [X1] : r1_tarski(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).
% 2.75/0.75  fof(f2498,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X1),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f2141,f59])).
% 2.75/0.75  fof(f2485,plain,(
% 2.75/0.75    ~spl5_20 | spl5_170 | ~spl5_166),
% 2.75/0.75    inference(avatar_split_clause,[],[f2481,f2450,f2483,f171])).
% 2.75/0.75  fof(f2483,plain,(
% 2.75/0.75    spl5_170 <=> ! [X27,X26] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK4) | ~r1_tarski(k2_relat_1(sK3),X27) | ~r1_tarski(k1_relat_1(sK3),X26))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).
% 2.75/0.75  fof(f2481,plain,(
% 2.75/0.75    ( ! [X26,X27] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK4) | ~r1_tarski(k1_relat_1(sK3),X26) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X27)) ) | ~spl5_166),
% 2.75/0.75    inference(resolution,[],[f2451,f753])).
% 2.75/0.75  fof(f2465,plain,(
% 2.75/0.75    ~spl5_169 | spl5_168 | ~spl5_2 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2442,f2001,f77,f2457,f2461])).
% 2.75/0.75  fof(f2461,plain,(
% 2.75/0.75    spl5_169 <=> r1_tarski(sK3,sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).
% 2.75/0.75  fof(f2457,plain,(
% 2.75/0.75    spl5_168 <=> ! [X4,X6] : (~v1_relat_1(X4) | ~r1_tarski(k2_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))),X6) | v4_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).
% 2.75/0.75  fof(f2001,plain,(
% 2.75/0.75    spl5_123 <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 2.75/0.75  fof(f2442,plain,(
% 2.75/0.75    ( ! [X10,X9] : (~v1_relat_1(X9) | ~v1_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2)))) | v4_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~r1_tarski(sK3,sK4) | ~r1_tarski(k2_relat_1(k7_relat_1(X9,k7_relat_1(sK3,u1_struct_0(sK2)))),X10)) ) | (~spl5_2 | ~spl5_123)),
% 2.75/0.75    inference(resolution,[],[f2237,f780])).
% 2.75/0.75  fof(f2237,plain,(
% 2.75/0.75    ( ! [X11] : (r1_tarski(k1_relat_1(k7_relat_1(X11,k7_relat_1(sK3,u1_struct_0(sK2)))),sK3) | ~v1_relat_1(X11)) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f60])).
% 2.75/0.75  fof(f2012,plain,(
% 2.75/0.75    ( ! [X3] : (~r1_tarski(X3,k7_relat_1(sK3,u1_struct_0(sK2))) | r1_tarski(X3,sK3)) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2002,f68])).
% 2.75/0.75  fof(f2002,plain,(
% 2.75/0.75    r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3) | ~spl5_123),
% 2.75/0.75    inference(avatar_component_clause,[],[f2001])).
% 2.75/0.75  fof(f2464,plain,(
% 2.75/0.75    ~spl5_169 | spl5_167 | ~spl5_15 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2441,f2001,f144,f2453,f2461])).
% 2.75/0.75  fof(f2453,plain,(
% 2.75/0.75    spl5_167 <=> ! [X1,X3] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))),X3) | v4_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~v1_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).
% 2.75/0.75  fof(f2441,plain,(
% 2.75/0.75    ( ! [X8,X7] : (~v1_relat_1(X7) | ~v1_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2)))) | v4_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~r1_tarski(sK3,sK4) | ~r1_tarski(k2_relat_1(k7_relat_1(X7,k7_relat_1(sK3,u1_struct_0(sK2)))),X8)) ) | (~spl5_15 | ~spl5_123)),
% 2.75/0.75    inference(resolution,[],[f2237,f784])).
% 2.75/0.75  fof(f2459,plain,(
% 2.75/0.75    spl5_166 | spl5_168 | ~spl5_2 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2440,f2001,f77,f2457,f2450])).
% 2.75/0.75  fof(f2440,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))) | v4_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~r1_tarski(sK3,X5) | ~r1_tarski(X5,sK4) | ~r1_tarski(k2_relat_1(k7_relat_1(X4,k7_relat_1(sK3,u1_struct_0(sK2)))),X6)) ) | (~spl5_2 | ~spl5_123)),
% 2.75/0.75    inference(resolution,[],[f2237,f779])).
% 2.75/0.75  fof(f2455,plain,(
% 2.75/0.75    spl5_166 | spl5_167 | ~spl5_15 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2439,f2001,f144,f2453,f2450])).
% 2.75/0.75  fof(f2439,plain,(
% 2.75/0.75    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))) | v4_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~r1_tarski(sK3,X2) | ~r1_tarski(X2,sK4) | ~r1_tarski(k2_relat_1(k7_relat_1(X1,k7_relat_1(sK3,u1_struct_0(sK2)))),X3)) ) | (~spl5_15 | ~spl5_123)),
% 2.75/0.75    inference(resolution,[],[f2237,f783])).
% 2.75/0.75  fof(f2433,plain,(
% 2.75/0.75    ~spl5_160 | spl5_165 | ~spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2408,f2106,f2431,f2411])).
% 2.75/0.75  fof(f2411,plain,(
% 2.75/0.75    spl5_160 <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).
% 2.75/0.75  fof(f2431,plain,(
% 2.75/0.75    spl5_165 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).
% 2.75/0.75  fof(f2106,plain,(
% 2.75/0.75    spl5_131 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).
% 2.75/0.75  fof(f2408,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK2)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2131,f433])).
% 2.75/0.75  fof(f2131,plain,(
% 2.75/0.75    ( ! [X10] : (~r1_tarski(X10,k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | r1_tarski(X10,u1_struct_0(sK2))) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2107,f68])).
% 2.75/0.75  fof(f2107,plain,(
% 2.75/0.75    r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~spl5_131),
% 2.75/0.75    inference(avatar_component_clause,[],[f2106])).
% 2.75/0.75  fof(f2429,plain,(
% 2.75/0.75    ~spl5_160 | spl5_164 | ~spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2406,f2106,f2427,f2411])).
% 2.75/0.75  fof(f2427,plain,(
% 2.75/0.75    spl5_164 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK2)) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).
% 2.75/0.75  fof(f2406,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | ~v1_relat_1(X12)) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2131,f252])).
% 2.75/0.75  fof(f2425,plain,(
% 2.75/0.75    ~spl5_160 | spl5_163 | ~spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2402,f2106,f2423,f2411])).
% 2.75/0.75  fof(f2423,plain,(
% 2.75/0.75    spl5_163 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).
% 2.75/0.75  fof(f2402,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)) | ~v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2131,f426])).
% 2.75/0.75  fof(f2421,plain,(
% 2.75/0.75    ~spl5_160 | spl5_162 | ~spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2401,f2106,f2419,f2411])).
% 2.75/0.75  fof(f2419,plain,(
% 2.75/0.75    spl5_162 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).
% 2.75/0.75  fof(f2401,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | ~v1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2))) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2131,f251])).
% 2.75/0.75  fof(f2417,plain,(
% 2.75/0.75    ~spl5_160 | spl5_161 | ~spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2400,f2106,f2415,f2411])).
% 2.75/0.75  fof(f2415,plain,(
% 2.75/0.75    spl5_161 <=> ! [X1] : r1_tarski(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).
% 2.75/0.75  fof(f2400,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK2)) | ~v1_relat_1(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_131),
% 2.75/0.75    inference(resolution,[],[f2131,f59])).
% 2.75/0.75  fof(f2398,plain,(
% 2.75/0.75    ~spl5_154 | spl5_159 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2373,f1980,f2396,f2376])).
% 2.75/0.75  fof(f2376,plain,(
% 2.75/0.75    spl5_154 <=> v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).
% 2.75/0.75  fof(f2396,plain,(
% 2.75/0.75    spl5_159 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).
% 2.75/0.75  fof(f1980,plain,(
% 2.75/0.75    spl5_120 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 2.75/0.75  fof(f2373,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X18))))),u1_struct_0(sK0)) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f2050,f433])).
% 2.75/0.75  fof(f2050,plain,(
% 2.75/0.75    ( ! [X9] : (~r1_tarski(X9,k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | r1_tarski(X9,u1_struct_0(sK0))) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f1981,f68])).
% 2.75/0.75  fof(f1981,plain,(
% 2.75/0.75    r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0)) | ~spl5_120),
% 2.75/0.75    inference(avatar_component_clause,[],[f1980])).
% 2.75/0.75  fof(f2394,plain,(
% 2.75/0.75    ~spl5_154 | spl5_158 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2371,f1980,f2392,f2376])).
% 2.75/0.75  fof(f2392,plain,(
% 2.75/0.75    spl5_158 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK0)) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).
% 2.75/0.75  fof(f2371,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X13))),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | ~v1_relat_1(X12)) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f2050,f252])).
% 2.75/0.75  fof(f2390,plain,(
% 2.75/0.75    ~spl5_154 | spl5_157 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2367,f1980,f2388,f2376])).
% 2.75/0.75  fof(f2388,plain,(
% 2.75/0.75    spl5_157 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).
% 2.75/0.75  fof(f2367,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5),X6),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X4),X5)) | ~v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f2050,f426])).
% 2.75/0.75  fof(f2386,plain,(
% 2.75/0.75    ~spl5_154 | spl5_156 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2366,f1980,f2384,f2376])).
% 2.75/0.75  fof(f2384,plain,(
% 2.75/0.75    spl5_156 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).
% 2.75/0.75  fof(f2366,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2),X3),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) | ~v1_relat_1(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X2))) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f2050,f251])).
% 2.75/0.75  fof(f2382,plain,(
% 2.75/0.75    ~spl5_154 | spl5_155 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2365,f1980,f2380,f2376])).
% 2.75/0.75  fof(f2380,plain,(
% 2.75/0.75    spl5_155 <=> ! [X1] : r1_tarski(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).
% 2.75/0.75  fof(f2365,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X1),u1_struct_0(sK0)) | ~v1_relat_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))))) ) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f2050,f59])).
% 2.75/0.75  fof(f2335,plain,(
% 2.75/0.75    ~spl5_153 | ~spl5_58 | spl5_152 | ~spl5_16 | ~spl5_147),
% 2.75/0.75    inference(avatar_split_clause,[],[f2325,f2299,f149,f2328,f757,f2332])).
% 2.75/0.75  fof(f2332,plain,(
% 2.75/0.75    spl5_153 <=> r1_tarski(sK3,sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).
% 2.75/0.75  fof(f757,plain,(
% 2.75/0.75    spl5_58 <=> v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 2.75/0.75  fof(f2328,plain,(
% 2.75/0.75    spl5_152 <=> ! [X0] : (v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0),X0) | ~v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).
% 2.75/0.75  fof(f2299,plain,(
% 2.75/0.75    spl5_147 <=> ! [X1] : r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).
% 2.75/0.75  fof(f2325,plain,(
% 2.75/0.75    ( ! [X11] : (v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X11),X11) | ~v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X11)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~r1_tarski(sK3,sK3)) ) | (~spl5_16 | ~spl5_147)),
% 2.75/0.75    inference(resolution,[],[f2300,f1366])).
% 2.75/0.75  fof(f2300,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3)) ) | ~spl5_147),
% 2.75/0.75    inference(avatar_component_clause,[],[f2299])).
% 2.75/0.75  fof(f2330,plain,(
% 2.75/0.75    ~spl5_58 | spl5_152 | ~spl5_16 | ~spl5_147),
% 2.75/0.75    inference(avatar_split_clause,[],[f2318,f2299,f149,f2328,f757])).
% 2.75/0.75  fof(f2318,plain,(
% 2.75/0.75    ( ! [X0] : (v4_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0),X0) | ~v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | (~spl5_16 | ~spl5_147)),
% 2.75/0.75    inference(resolution,[],[f2300,f1367])).
% 2.75/0.75  fof(f1367,plain,(
% 2.75/0.75    ( ! [X24,X23] : (~r1_tarski(k7_relat_1(X23,X24),sK3) | v4_relat_1(k7_relat_1(X23,X24),X24) | ~v1_relat_1(k7_relat_1(X23,X24)) | ~v1_relat_1(X23)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f802,f227])).
% 2.75/0.75  fof(f227,plain,(
% 2.75/0.75    ( ! [X0] : (v5_relat_1(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK3)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f213,f204])).
% 2.75/0.75  fof(f2317,plain,(
% 2.75/0.75    ~spl5_58 | spl5_151 | ~spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f2295,f1990,f2315,f757])).
% 2.75/0.75  fof(f2315,plain,(
% 2.75/0.75    spl5_151 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X18))))),sK3) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).
% 2.75/0.75  fof(f1990,plain,(
% 2.75/0.75    spl5_121 <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 2.75/0.75  fof(f2295,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X18))))),sK3) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f2019,f433])).
% 2.75/0.75  fof(f2019,plain,(
% 2.75/0.75    ( ! [X3] : (~r1_tarski(X3,k2_tmap_1(sK1,sK0,sK3,sK2)) | r1_tarski(X3,sK3)) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f1991,f68])).
% 2.75/0.75  fof(f1991,plain,(
% 2.75/0.75    r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~spl5_121),
% 2.75/0.75    inference(avatar_component_clause,[],[f1990])).
% 2.75/0.75  fof(f2313,plain,(
% 2.75/0.75    ~spl5_58 | spl5_150 | ~spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f2293,f1990,f2311,f757])).
% 2.75/0.75  fof(f2311,plain,(
% 2.75/0.75    spl5_150 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X13))),sK3) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).
% 2.75/0.75  fof(f2293,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X13))),sK3) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~v1_relat_1(X12)) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f2019,f252])).
% 2.75/0.75  fof(f2309,plain,(
% 2.75/0.75    ~spl5_58 | spl5_149 | ~spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f2289,f1990,f2307,f757])).
% 2.75/0.75  fof(f2307,plain,(
% 2.75/0.75    spl5_149 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5),X6),sK3) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).
% 2.75/0.75  fof(f2289,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5),X6),sK3) | ~v1_relat_1(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X4),X5)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f2019,f426])).
% 2.75/0.75  fof(f2305,plain,(
% 2.75/0.75    ~spl5_58 | spl5_148 | ~spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f2288,f1990,f2303,f757])).
% 2.75/0.75  fof(f2303,plain,(
% 2.75/0.75    spl5_148 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2),X3),sK3) | ~v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).
% 2.75/0.75  fof(f2288,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2),X3),sK3) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~v1_relat_1(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X2))) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f2019,f251])).
% 2.75/0.75  fof(f2301,plain,(
% 2.75/0.75    ~spl5_58 | spl5_147 | ~spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f2287,f1990,f2299,f757])).
% 2.75/0.75  fof(f2287,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X1),sK3) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | ~spl5_121),
% 2.75/0.75    inference(resolution,[],[f2019,f59])).
% 2.75/0.75  fof(f2277,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | spl5_117 | ~spl5_56),
% 2.75/0.75    inference(avatar_split_clause,[],[f2276,f742,f1959,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1959,plain,(
% 2.75/0.75    spl5_117 <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).
% 2.75/0.75  fof(f742,plain,(
% 2.75/0.75    spl5_56 <=> m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 2.75/0.75  fof(f2276,plain,(
% 2.75/0.75    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_56),
% 2.75/0.75    inference(superposition,[],[f743,f1508])).
% 2.75/0.75  fof(f743,plain,(
% 2.75/0.75    m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl5_56),
% 2.75/0.75    inference(avatar_component_clause,[],[f742])).
% 2.75/0.75  fof(f2271,plain,(
% 2.75/0.75    ~spl5_120 | ~spl5_116 | ~spl5_131 | spl5_115),
% 2.75/0.75    inference(avatar_split_clause,[],[f2270,f1949,f2106,f1954,f1980])).
% 2.75/0.75  fof(f2270,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0)) | spl5_115),
% 2.75/0.75    inference(resolution,[],[f1951,f753])).
% 2.75/0.75  fof(f1951,plain,(
% 2.75/0.75    ~r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | spl5_115),
% 2.75/0.75    inference(avatar_component_clause,[],[f1949])).
% 2.75/0.75  fof(f2261,plain,(
% 2.75/0.75    ~spl5_116 | spl5_146 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2240,f2001,f2259,f1954])).
% 2.75/0.75  fof(f2259,plain,(
% 2.75/0.75    spl5_146 <=> ! [X16,X18,X17] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),sK3) | ~v1_relat_1(X17) | ~v1_relat_1(X16))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 2.75/0.75  fof(f2240,plain,(
% 2.75/0.75    ( ! [X17,X18,X16] : (r1_tarski(k1_relat_1(k7_relat_1(X16,k1_relat_1(k7_relat_1(X17,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X18))))),sK3) | ~v1_relat_1(X16) | ~v1_relat_1(X17) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f433])).
% 2.75/0.75  fof(f2257,plain,(
% 2.75/0.75    ~spl5_116 | spl5_145 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2238,f2001,f2255,f1954])).
% 2.75/0.75  fof(f2255,plain,(
% 2.75/0.75    spl5_145 <=> ! [X13,X12] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),sK3) | ~v1_relat_1(X12))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).
% 2.75/0.75  fof(f2238,plain,(
% 2.75/0.75    ( ! [X12,X13] : (r1_tarski(k1_relat_1(k7_relat_1(X12,k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X13))),sK3) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(X12)) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f252])).
% 2.75/0.75  fof(f2253,plain,(
% 2.75/0.75    ~spl5_116 | spl5_144 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2234,f2001,f2251,f1954])).
% 2.75/0.75  fof(f2251,plain,(
% 2.75/0.75    spl5_144 <=> ! [X5,X4,X6] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),sK3) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).
% 2.75/0.75  fof(f2234,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5),X6),sK3) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X4),X5)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f426])).
% 2.75/0.75  fof(f2249,plain,(
% 2.75/0.75    ~spl5_116 | spl5_143 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2233,f2001,f2247,f1954])).
% 2.75/0.75  fof(f2247,plain,(
% 2.75/0.75    spl5_143 <=> ! [X3,X2] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),sK3) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).
% 2.75/0.75  fof(f2233,plain,(
% 2.75/0.75    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2),X3),sK3) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2))) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f251])).
% 2.75/0.75  fof(f2245,plain,(
% 2.75/0.75    ~spl5_116 | spl5_142 | ~spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2232,f2001,f2243,f1954])).
% 2.75/0.75  fof(f2243,plain,(
% 2.75/0.75    spl5_142 <=> ! [X1] : r1_tarski(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 2.75/0.75  fof(f2232,plain,(
% 2.75/0.75    ( ! [X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1),sK3) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | ~spl5_123),
% 2.75/0.75    inference(resolution,[],[f2012,f59])).
% 2.75/0.75  fof(f2215,plain,(
% 2.75/0.75    ~spl5_58 | spl5_141 | spl5_128 | ~spl5_15 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2195,f765,f144,f2075,f2208,f757])).
% 2.75/0.75  fof(f2208,plain,(
% 2.75/0.75    spl5_141 <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).
% 2.75/0.75  fof(f2195,plain,(
% 2.75/0.75    ( ! [X4,X5] : (~r1_tarski(u1_struct_0(sK0),X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK4) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | (~spl5_15 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f659])).
% 2.75/0.75  fof(f2214,plain,(
% 2.75/0.75    ~spl5_58 | spl5_140 | spl5_128 | ~spl5_2 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2194,f765,f77,f2075,f2203,f757])).
% 2.75/0.75  fof(f2203,plain,(
% 2.75/0.75    spl5_140 <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).
% 2.75/0.75  fof(f2194,plain,(
% 2.75/0.75    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(sK0),X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,sK4) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | (~spl5_2 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f590])).
% 2.75/0.75  fof(f2213,plain,(
% 2.75/0.75    ~spl5_58 | spl5_141 | spl5_127 | ~spl5_15 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2193,f765,f144,f2070,f2208,f757])).
% 2.75/0.75  fof(f2193,plain,(
% 2.75/0.75    ( ! [X1] : (~r1_tarski(X1,sK4) | ~r1_tarski(u1_struct_0(sK0),X1) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | (~spl5_15 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f373])).
% 2.75/0.75  fof(f2212,plain,(
% 2.75/0.75    ~spl5_58 | spl5_140 | spl5_127 | ~spl5_2 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2192,f765,f77,f2070,f2203,f757])).
% 2.75/0.75  fof(f2192,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(u1_struct_0(sK0),X0) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | (~spl5_2 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f343])).
% 2.75/0.75  fof(f2211,plain,(
% 2.75/0.75    ~spl5_58 | spl5_141 | ~spl5_125 | ~spl5_15 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2191,f765,f144,f2060,f2208,f757])).
% 2.75/0.75  fof(f2060,plain,(
% 2.75/0.75    spl5_125 <=> r1_tarski(u1_struct_0(sK0),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).
% 2.75/0.75  fof(f2191,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),sK4) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | (~spl5_15 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f247])).
% 2.75/0.75  fof(f2206,plain,(
% 2.75/0.75    ~spl5_58 | spl5_140 | ~spl5_125 | ~spl5_2 | ~spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f2190,f765,f77,f2060,f2203,f757])).
% 2.75/0.75  fof(f2190,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),sK4) | v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | (~spl5_2 | ~spl5_60)),
% 2.75/0.75    inference(resolution,[],[f766,f242])).
% 2.75/0.75  fof(f2187,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | spl5_139 | ~spl5_134),
% 2.75/0.75    inference(avatar_split_clause,[],[f2168,f2149,f2185,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f2185,plain,(
% 2.75/0.75    spl5_139 <=> ! [X0] : ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).
% 2.75/0.75  fof(f2149,plain,(
% 2.75/0.75    spl5_134 <=> ! [X6] : ~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).
% 2.75/0.75  fof(f2168,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),X0) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_134),
% 2.75/0.75    inference(superposition,[],[f2150,f1508])).
% 2.75/0.75  fof(f2150,plain,(
% 2.75/0.75    ( ! [X6] : (~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6)) ) | ~spl5_134),
% 2.75/0.75    inference(avatar_component_clause,[],[f2149])).
% 2.75/0.75  fof(f2183,plain,(
% 2.75/0.75    spl5_136 | ~spl5_137 | spl5_138 | ~spl5_134),
% 2.75/0.75    inference(avatar_split_clause,[],[f2167,f2149,f2181,f2177,f2174])).
% 2.75/0.75  fof(f2174,plain,(
% 2.75/0.75    spl5_136 <=> ! [X28] : ~r1_tarski(k2_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X28)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).
% 2.75/0.75  fof(f2181,plain,(
% 2.75/0.75    spl5_138 <=> ! [X27] : ~r1_tarski(k1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X27)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).
% 2.75/0.75  fof(f2167,plain,(
% 2.75/0.75    ( ! [X28,X27] : (~r1_tarski(k1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X27) | ~v1_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) | ~r1_tarski(k2_relat_1(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))),X28)) ) | ~spl5_134),
% 2.75/0.75    inference(resolution,[],[f2150,f753])).
% 2.75/0.75  fof(f2172,plain,(
% 2.75/0.75    ~spl5_58 | spl5_135 | ~spl5_134),
% 2.75/0.75    inference(avatar_split_clause,[],[f2152,f2149,f2170,f757])).
% 2.75/0.75  fof(f2170,plain,(
% 2.75/0.75    spl5_135 <=> ! [X0] : ~v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).
% 2.75/0.75  fof(f2152,plain,(
% 2.75/0.75    ( ! [X0] : (~v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),X0) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2))) ) | ~spl5_134),
% 2.75/0.75    inference(resolution,[],[f2150,f61])).
% 2.75/0.75  fof(f2151,plain,(
% 2.75/0.75    spl5_133 | ~spl5_58 | spl5_134 | ~spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2137,f761,f2149,f757,f2145])).
% 2.75/0.75  fof(f2145,plain,(
% 2.75/0.75    spl5_133 <=> v4_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).
% 2.75/0.75  fof(f2137,plain,(
% 2.75/0.75    ( ! [X6] : (~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),X6) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | v4_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2))) ) | ~spl5_59),
% 2.75/0.75    inference(resolution,[],[f762,f751])).
% 2.75/0.75  fof(f2122,plain,(
% 2.75/0.75    ~spl5_20 | spl5_131),
% 2.75/0.75    inference(avatar_split_clause,[],[f2116,f2106,f171])).
% 2.75/0.75  fof(f2116,plain,(
% 2.75/0.75    ~v1_relat_1(sK3) | spl5_131),
% 2.75/0.75    inference(resolution,[],[f2108,f60])).
% 2.75/0.75  fof(f2108,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | spl5_131),
% 2.75/0.75    inference(avatar_component_clause,[],[f2106])).
% 2.75/0.75  fof(f2115,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_132 | spl5_130),
% 2.75/0.75    inference(avatar_split_clause,[],[f2110,f2101,f2112,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f2112,plain,(
% 2.75/0.75    spl5_132 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).
% 2.75/0.75  fof(f2101,plain,(
% 2.75/0.75    spl5_130 <=> r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).
% 2.75/0.75  fof(f2110,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),sK4) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_130),
% 2.75/0.75    inference(superposition,[],[f2103,f1508])).
% 2.75/0.75  fof(f2103,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4) | spl5_130),
% 2.75/0.75    inference(avatar_component_clause,[],[f2101])).
% 2.75/0.75  fof(f2109,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_131 | spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2099,f761,f2106,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f2099,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_59),
% 2.75/0.75    inference(superposition,[],[f763,f1508])).
% 2.75/0.75  fof(f763,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2)) | spl5_59),
% 2.75/0.75    inference(avatar_component_clause,[],[f761])).
% 2.75/0.75  fof(f2104,plain,(
% 2.75/0.75    ~spl5_130 | ~spl5_2 | spl5_59),
% 2.75/0.75    inference(avatar_split_clause,[],[f2098,f761,f77,f2101])).
% 2.75/0.75  fof(f2098,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),sK4) | (~spl5_2 | spl5_59)),
% 2.75/0.75    inference(resolution,[],[f763,f214])).
% 2.75/0.75  fof(f2083,plain,(
% 2.75/0.75    ~spl5_20 | spl5_129 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2054,f1980,f2080,f171])).
% 2.75/0.75  fof(f2080,plain,(
% 2.75/0.75    spl5_129 <=> v4_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).
% 2.75/0.75  fof(f2054,plain,(
% 2.75/0.75    v4_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | ~v1_relat_1(sK3) | ~spl5_120),
% 2.75/0.75    inference(resolution,[],[f1981,f789])).
% 2.75/0.75  fof(f2078,plain,(
% 2.75/0.75    ~spl5_116 | spl5_126 | spl5_128 | ~spl5_15 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2046,f1980,f144,f2075,f2065,f1954])).
% 2.75/0.75  fof(f2065,plain,(
% 2.75/0.75    spl5_126 <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).
% 2.75/0.75  fof(f2046,plain,(
% 2.75/0.75    ( ! [X4,X5] : (~r1_tarski(u1_struct_0(sK0),X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK4) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | (~spl5_15 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f659])).
% 2.75/0.75  fof(f2077,plain,(
% 2.75/0.75    ~spl5_116 | spl5_124 | spl5_128 | ~spl5_2 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2045,f1980,f77,f2075,f2056,f1954])).
% 2.75/0.75  fof(f2056,plain,(
% 2.75/0.75    spl5_124 <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 2.75/0.75  fof(f2045,plain,(
% 2.75/0.75    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(sK0),X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,sK4) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | (~spl5_2 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f590])).
% 2.75/0.75  fof(f2073,plain,(
% 2.75/0.75    ~spl5_116 | spl5_126 | spl5_127 | ~spl5_15 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2044,f1980,f144,f2070,f2065,f1954])).
% 2.75/0.75  fof(f2044,plain,(
% 2.75/0.75    ( ! [X1] : (~r1_tarski(X1,sK4) | ~r1_tarski(u1_struct_0(sK0),X1) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | (~spl5_15 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f373])).
% 2.75/0.75  fof(f2072,plain,(
% 2.75/0.75    ~spl5_116 | spl5_124 | spl5_127 | ~spl5_2 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2042,f1980,f77,f2070,f2056,f1954])).
% 2.75/0.75  fof(f2042,plain,(
% 2.75/0.75    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(u1_struct_0(sK0),X0) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))) ) | (~spl5_2 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f343])).
% 2.75/0.75  fof(f2068,plain,(
% 2.75/0.75    ~spl5_116 | spl5_126 | ~spl5_125 | ~spl5_15 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2041,f1980,f144,f2060,f2065,f1954])).
% 2.75/0.75  fof(f2041,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),sK4) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK1)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | (~spl5_15 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f247])).
% 2.75/0.75  fof(f2063,plain,(
% 2.75/0.75    ~spl5_116 | spl5_124 | ~spl5_125 | ~spl5_2 | ~spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2040,f1980,f77,f2060,f2056,f1954])).
% 2.75/0.75  fof(f2040,plain,(
% 2.75/0.75    ~r1_tarski(u1_struct_0(sK0),sK4) | v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | (~spl5_2 | ~spl5_120)),
% 2.75/0.75    inference(resolution,[],[f1981,f242])).
% 2.75/0.75  fof(f2038,plain,(
% 2.75/0.75    ~spl5_116 | ~spl5_122 | spl5_120),
% 2.75/0.75    inference(avatar_split_clause,[],[f2037,f1980,f1995,f1954])).
% 2.75/0.75  fof(f1995,plain,(
% 2.75/0.75    spl5_122 <=> v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 2.75/0.75  fof(f2037,plain,(
% 2.75/0.75    ~v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | spl5_120),
% 2.75/0.75    inference(resolution,[],[f1982,f61])).
% 2.75/0.75  fof(f1982,plain,(
% 2.75/0.75    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0)) | spl5_120),
% 2.75/0.75    inference(avatar_component_clause,[],[f1980])).
% 2.75/0.75  fof(f2026,plain,(
% 2.75/0.75    ~spl5_123 | ~spl5_16 | spl5_122),
% 2.75/0.75    inference(avatar_split_clause,[],[f2025,f1995,f149,f2001])).
% 2.75/0.75  fof(f2025,plain,(
% 2.75/0.75    ~r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3) | (~spl5_16 | spl5_122)),
% 2.75/0.75    inference(resolution,[],[f1997,f227])).
% 2.75/0.75  fof(f1997,plain,(
% 2.75/0.75    ~v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0)) | spl5_122),
% 2.75/0.75    inference(avatar_component_clause,[],[f1995])).
% 2.75/0.75  fof(f2006,plain,(
% 2.75/0.75    ~spl5_20 | spl5_123),
% 2.75/0.75    inference(avatar_split_clause,[],[f2005,f2001,f171])).
% 2.75/0.75  fof(f2005,plain,(
% 2.75/0.75    ~v1_relat_1(sK3) | spl5_123),
% 2.75/0.75    inference(resolution,[],[f2003,f59])).
% 2.75/0.75  fof(f2003,plain,(
% 2.75/0.75    ~r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3) | spl5_123),
% 2.75/0.75    inference(avatar_component_clause,[],[f2001])).
% 2.75/0.75  fof(f2004,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_123 | spl5_121),
% 2.75/0.75    inference(avatar_split_clause,[],[f1999,f1990,f2001,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1999,plain,(
% 2.75/0.75    ~r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),sK3) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_121),
% 2.75/0.75    inference(superposition,[],[f1992,f1508])).
% 2.75/0.75  fof(f1992,plain,(
% 2.75/0.75    ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | spl5_121),
% 2.75/0.75    inference(avatar_component_clause,[],[f1990])).
% 2.75/0.75  fof(f1998,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_122 | spl5_119),
% 2.75/0.75    inference(avatar_split_clause,[],[f1988,f1975,f1995,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1975,plain,(
% 2.75/0.75    spl5_119 <=> v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 2.75/0.75  fof(f1988,plain,(
% 2.75/0.75    ~v5_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_119),
% 2.75/0.75    inference(superposition,[],[f1977,f1508])).
% 2.75/0.75  fof(f1977,plain,(
% 2.75/0.75    ~v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0)) | spl5_119),
% 2.75/0.75    inference(avatar_component_clause,[],[f1975])).
% 2.75/0.75  fof(f1993,plain,(
% 2.75/0.75    ~spl5_121 | ~spl5_16 | spl5_119),
% 2.75/0.75    inference(avatar_split_clause,[],[f1987,f1975,f149,f1990])).
% 2.75/0.75  fof(f1987,plain,(
% 2.75/0.75    ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | (~spl5_16 | spl5_119)),
% 2.75/0.75    inference(resolution,[],[f1977,f227])).
% 2.75/0.75  fof(f1983,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_120 | spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f1973,f765,f1980,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1973,plain,(
% 2.75/0.75    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_60),
% 2.75/0.75    inference(superposition,[],[f767,f1508])).
% 2.75/0.75  fof(f767,plain,(
% 2.75/0.75    ~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0)) | spl5_60),
% 2.75/0.75    inference(avatar_component_clause,[],[f765])).
% 2.75/0.75  fof(f1978,plain,(
% 2.75/0.75    ~spl5_58 | ~spl5_119 | spl5_60),
% 2.75/0.75    inference(avatar_split_clause,[],[f1972,f765,f1975,f757])).
% 2.75/0.75  fof(f1972,plain,(
% 2.75/0.75    ~v5_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK0)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | spl5_60),
% 2.75/0.75    inference(resolution,[],[f767,f61])).
% 2.75/0.75  fof(f1970,plain,(
% 2.75/0.75    ~spl5_60 | ~spl5_58 | ~spl5_59 | spl5_61),
% 2.75/0.75    inference(avatar_split_clause,[],[f872,f770,f761,f757,f765])).
% 2.75/0.75  fof(f770,plain,(
% 2.75/0.75    spl5_61 <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.75/0.75  fof(f872,plain,(
% 2.75/0.75    ~r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | ~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0)) | spl5_61),
% 2.75/0.75    inference(resolution,[],[f753,f772])).
% 2.75/0.75  fof(f772,plain,(
% 2.75/0.75    ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | spl5_61),
% 2.75/0.75    inference(avatar_component_clause,[],[f770])).
% 2.75/0.75  fof(f1969,plain,(
% 2.75/0.75    ~spl5_20 | spl5_116),
% 2.75/0.75    inference(avatar_split_clause,[],[f1968,f1954,f171])).
% 2.75/0.75  fof(f1968,plain,(
% 2.75/0.75    ~v1_relat_1(sK3) | spl5_116),
% 2.75/0.75    inference(resolution,[],[f1956,f181])).
% 2.75/0.75  fof(f1956,plain,(
% 2.75/0.75    ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | spl5_116),
% 2.75/0.75    inference(avatar_component_clause,[],[f1954])).
% 2.75/0.75  fof(f1967,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_118 | spl5_1),
% 2.75/0.75    inference(avatar_split_clause,[],[f1947,f72,f1964,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1964,plain,(
% 2.75/0.75    spl5_118 <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 2.75/0.75  fof(f72,plain,(
% 2.75/0.75    spl5_1 <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.75/0.75  fof(f1947,plain,(
% 2.75/0.75    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 2.75/0.75    inference(superposition,[],[f74,f1508])).
% 2.75/0.75  fof(f74,plain,(
% 2.75/0.75    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) | spl5_1),
% 2.75/0.75    inference(avatar_component_clause,[],[f72])).
% 2.75/0.75  fof(f1962,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_117 | spl5_56),
% 2.75/0.75    inference(avatar_split_clause,[],[f1946,f742,f1959,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1946,plain,(
% 2.75/0.75    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_56),
% 2.75/0.75    inference(superposition,[],[f744,f1508])).
% 2.75/0.75  fof(f744,plain,(
% 2.75/0.75    ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | spl5_56),
% 2.75/0.75    inference(avatar_component_clause,[],[f742])).
% 2.75/0.75  fof(f1957,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_116 | spl5_58),
% 2.75/0.75    inference(avatar_split_clause,[],[f1945,f757,f1954,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1945,plain,(
% 2.75/0.75    ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_58),
% 2.75/0.75    inference(superposition,[],[f759,f1508])).
% 2.75/0.75  fof(f759,plain,(
% 2.75/0.75    ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | spl5_58),
% 2.75/0.75    inference(avatar_component_clause,[],[f757])).
% 2.75/0.75  fof(f1952,plain,(
% 2.75/0.75    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_14 | ~spl5_13 | ~spl5_12 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_7 | ~spl5_115 | spl5_61),
% 2.75/0.75    inference(avatar_split_clause,[],[f1944,f770,f1949,f102,f87,f92,f97,f127,f132,f137,f112,f117,f122])).
% 2.75/0.75  fof(f1944,plain,(
% 2.75/0.75    ~r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~m1_pre_topc(sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_61),
% 2.75/0.75    inference(superposition,[],[f772,f1508])).
% 2.75/0.75  fof(f1899,plain,(
% 2.75/0.75    ~spl5_20 | spl5_114 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1889,f149,f1897,f171])).
% 2.75/0.75  fof(f1897,plain,(
% 2.75/0.75    spl5_114 <=> ! [X73,X71,X72] : (~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72)) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73)) | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 2.75/0.75  fof(f1889,plain,(
% 2.75/0.75    ( ! [X72,X71,X73] : (~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72)) | ~v1_relat_1(sK3) | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73))) ) | ~spl5_16),
% 2.75/0.75    inference(duplicate_literal_removal,[],[f1887])).
% 2.75/0.75  fof(f1887,plain,(
% 2.75/0.75    ( ! [X72,X71,X73] : (~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72)) | ~v1_relat_1(sK3) | v4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73),X73) | ~v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72),X73)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X71),X72))) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f426,f1367])).
% 2.75/0.75  fof(f1797,plain,(
% 2.75/0.75    ~spl5_96 | spl5_78 | ~spl5_16 | ~spl5_85),
% 2.75/0.75    inference(avatar_split_clause,[],[f1792,f1525,f149,f1186,f1572])).
% 2.75/0.75  fof(f1572,plain,(
% 2.75/0.75    spl5_96 <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 2.75/0.75  fof(f1186,plain,(
% 2.75/0.75    spl5_78 <=> ! [X7,X8,X6] : (~r1_tarski(X6,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 2.75/0.75  fof(f1792,plain,(
% 2.75/0.75    ( ! [X66,X67,X65] : (~r1_tarski(X65,X66) | ~r1_tarski(X67,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X65) | ~r1_tarski(X66,X67) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3)) ) | (~spl5_16 | ~spl5_85)),
% 2.75/0.75    inference(resolution,[],[f1526,f213])).
% 2.75/0.75  fof(f1796,plain,(
% 2.75/0.75    spl5_95 | spl5_78 | ~spl5_16 | ~spl5_85),
% 2.75/0.75    inference(avatar_split_clause,[],[f1791,f1525,f149,f1186,f1568])).
% 2.75/0.75  fof(f1791,plain,(
% 2.75/0.75    ( ! [X61,X64,X62,X63] : (~r1_tarski(X61,X62) | ~r1_tarski(X63,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X61) | ~r1_tarski(X62,X63) | ~r1_tarski(X64,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X64)) ) | (~spl5_16 | ~spl5_85)),
% 2.75/0.75    inference(resolution,[],[f1526,f229])).
% 2.75/0.75  fof(f1795,plain,(
% 2.75/0.75    spl5_94 | spl5_78 | ~spl5_16 | ~spl5_85),
% 2.75/0.75    inference(avatar_split_clause,[],[f1790,f1525,f149,f1186,f1564])).
% 2.75/0.75  fof(f1790,plain,(
% 2.75/0.75    ( ! [X59,X57,X60,X58,X56] : (~r1_tarski(X56,X57) | ~r1_tarski(X58,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X56) | ~r1_tarski(X57,X58) | ~r1_tarski(X59,X60) | ~r1_tarski(X60,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X59)) ) | (~spl5_16 | ~spl5_85)),
% 2.75/0.75    inference(resolution,[],[f1526,f277])).
% 2.75/0.75  fof(f277,plain,(
% 2.75/0.75    ( ! [X6,X4,X5] : (r1_tarski(X6,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(X5,X4) | ~r1_tarski(X4,sK3) | ~r1_tarski(X6,X5)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f229,f68])).
% 2.75/0.75  fof(f1794,plain,(
% 2.75/0.75    spl5_92 | spl5_78 | ~spl5_16 | ~spl5_85),
% 2.75/0.75    inference(avatar_split_clause,[],[f1789,f1525,f149,f1186,f1557])).
% 2.75/0.75  fof(f1789,plain,(
% 2.75/0.75    ( ! [X54,X52,X50,X55,X53,X51] : (~r1_tarski(X50,X51) | ~r1_tarski(X52,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X50) | ~r1_tarski(X51,X52) | ~r1_tarski(X53,sK3) | ~r1_tarski(X54,X55) | ~r1_tarski(X55,X53) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X54)) ) | (~spl5_16 | ~spl5_85)),
% 2.75/0.75    inference(resolution,[],[f1526,f439])).
% 2.75/0.75  fof(f439,plain,(
% 2.75/0.75    ( ! [X12,X10,X11,X9] : (r1_tarski(X12,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(X10,sK3) | ~r1_tarski(X11,X9) | ~r1_tarski(X9,X10) | ~r1_tarski(X12,X11)) ) | ~spl5_16),
% 2.75/0.75    inference(resolution,[],[f277,f68])).
% 2.75/0.75  fof(f1763,plain,(
% 2.75/0.75    ~spl5_19 | spl5_113 | ~spl5_64),
% 2.75/0.75    inference(avatar_split_clause,[],[f1758,f918,f1761,f167])).
% 2.75/0.75  fof(f167,plain,(
% 2.75/0.75    spl5_19 <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.75/0.75  fof(f1758,plain,(
% 2.75/0.75    ( ! [X26,X27] : (~r1_tarski(k2_zfmisc_1(X26,X27),sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X26) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27)) ) | ~spl5_64),
% 2.75/0.75    inference(resolution,[],[f919,f753])).
% 2.75/0.75  fof(f1743,plain,(
% 2.75/0.75    spl5_64 | spl5_76 | ~spl5_16 | ~spl5_52),
% 2.75/0.75    inference(avatar_split_clause,[],[f1737,f616,f149,f1161,f918])).
% 2.75/0.75  fof(f1161,plain,(
% 2.75/0.75    spl5_76 <=> ! [X49,X51,X50,X52] : (v5_relat_1(X49,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X49),X51) | ~r1_tarski(X50,sK3) | ~r1_tarski(X51,X52) | ~r1_tarski(X52,X50) | ~v1_relat_1(X49))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 2.75/0.75  fof(f616,plain,(
% 2.75/0.75    spl5_52 <=> ! [X27,X29,X28] : (v5_relat_1(X27,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X27),X28) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,sK3) | ~v1_relat_1(X27))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.75/0.75  fof(f1737,plain,(
% 2.75/0.75    ( ! [X47,X45,X43,X46,X44] : (v5_relat_1(X43,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X44) | ~r1_tarski(X44,sK3) | ~v1_relat_1(X43) | ~r1_tarski(X45,sK3) | ~r1_tarski(X46,X47) | ~r1_tarski(X47,X45) | ~r1_tarski(k2_relat_1(X43),X46)) ) | (~spl5_16 | ~spl5_52)),
% 2.75/0.75    inference(resolution,[],[f617,f439])).
% 2.75/0.75  fof(f617,plain,(
% 2.75/0.75    ( ! [X28,X29,X27] : (~r1_tarski(k2_relat_1(X27),X28) | v5_relat_1(X27,u1_struct_0(sK2)) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,sK3) | ~v1_relat_1(X27)) ) | ~spl5_52),
% 2.75/0.75    inference(avatar_component_clause,[],[f616])).
% 2.75/0.75  fof(f1641,plain,(
% 2.75/0.75    spl5_112 | spl5_53 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f669,f149,f144,f619,f1639])).
% 2.75/0.75  fof(f1639,plain,(
% 2.75/0.75    spl5_112 <=> ! [X32,X34,X33] : (v5_relat_1(X32,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X32),X33) | ~r1_tarski(X33,X34) | ~r1_tarski(X34,sK3) | ~v1_relat_1(X32))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 2.75/0.75  fof(f669,plain,(
% 2.75/0.75    ( ! [X33,X31,X34,X32] : (~r1_tarski(X31,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X31) | v5_relat_1(X32,u1_struct_0(sK1)) | ~v1_relat_1(X32) | ~r1_tarski(X33,X34) | ~r1_tarski(X34,sK3) | ~r1_tarski(k2_relat_1(X32),X33)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f373,f277])).
% 2.75/0.75  fof(f1637,plain,(
% 2.75/0.75    spl5_111 | spl5_53 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f670,f149,f144,f619,f1635])).
% 2.75/0.75  fof(f1635,plain,(
% 2.75/0.75    spl5_111 <=> ! [X36,X37] : (v5_relat_1(X36,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X36),X37) | ~r1_tarski(X37,sK3) | ~v1_relat_1(X36))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 2.75/0.75  fof(f670,plain,(
% 2.75/0.75    ( ! [X37,X35,X36] : (~r1_tarski(X35,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X35) | v5_relat_1(X36,u1_struct_0(sK1)) | ~v1_relat_1(X36) | ~r1_tarski(X37,sK3) | ~r1_tarski(k2_relat_1(X36),X37)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f373,f229])).
% 2.75/0.75  fof(f1633,plain,(
% 2.75/0.75    spl5_110 | spl5_53 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f671,f149,f144,f619,f1631])).
% 2.75/0.75  fof(f1631,plain,(
% 2.75/0.75    spl5_110 <=> ! [X39] : (v5_relat_1(X39,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X39),sK3) | ~v1_relat_1(X39))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 2.75/0.75  fof(f671,plain,(
% 2.75/0.75    ( ! [X39,X38] : (~r1_tarski(X38,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X38) | v5_relat_1(X39,u1_struct_0(sK1)) | ~v1_relat_1(X39) | ~r1_tarski(k2_relat_1(X39),sK3)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f373,f213])).
% 2.75/0.75  fof(f1629,plain,(
% 2.75/0.75    spl5_53 | spl5_109 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f906,f149,f144,f1627,f619])).
% 2.75/0.75  fof(f1627,plain,(
% 2.75/0.75    spl5_109 <=> ! [X40,X38,X41,X39] : (~r1_tarski(X38,sK3) | ~v1_relat_1(X41) | v5_relat_1(X41,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X41),X39) | ~r1_tarski(X39,X40) | ~r1_tarski(X40,X38))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 2.75/0.75  fof(f906,plain,(
% 2.75/0.75    ( ! [X39,X41,X38,X42,X40] : (~r1_tarski(X38,sK3) | ~r1_tarski(X39,X40) | ~r1_tarski(X40,X38) | ~r1_tarski(k2_relat_1(X41),X39) | ~r1_tarski(X42,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X42) | v5_relat_1(X41,u1_struct_0(sK1)) | ~v1_relat_1(X41)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f439,f373])).
% 2.75/0.75  fof(f1625,plain,(
% 2.75/0.75    spl5_53 | spl5_76 | ~spl5_2 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f907,f149,f77,f1161,f619])).
% 2.75/0.75  fof(f907,plain,(
% 2.75/0.75    ( ! [X47,X45,X43,X46,X44] : (~r1_tarski(X43,sK3) | ~r1_tarski(X44,X45) | ~r1_tarski(X45,X43) | ~r1_tarski(k2_relat_1(X46),X44) | ~r1_tarski(X47,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X47) | v5_relat_1(X46,u1_struct_0(sK2)) | ~v1_relat_1(X46)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f439,f343])).
% 2.75/0.75  fof(f1624,plain,(
% 2.75/0.75    spl5_108 | spl5_53 | ~spl5_16 | ~spl5_54),
% 2.75/0.75    inference(avatar_split_clause,[],[f1176,f635,f149,f619,f1622])).
% 2.75/0.75  fof(f1622,plain,(
% 2.75/0.75    spl5_108 <=> ! [X27,X26,X28] : (~r1_tarski(X26,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X27) | ~r1_tarski(X27,X28) | ~r1_tarski(X28,X26))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 2.75/0.75  fof(f1176,plain,(
% 2.75/0.75    ( ! [X28,X26,X27,X25] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X25) | ~r1_tarski(X25,sK4) | ~r1_tarski(X26,sK3) | ~r1_tarski(X27,X28) | ~r1_tarski(X28,X26) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X27)) ) | (~spl5_16 | ~spl5_54)),
% 2.75/0.75    inference(resolution,[],[f636,f439])).
% 2.75/0.75  fof(f1620,plain,(
% 2.75/0.75    spl5_107 | spl5_53 | ~spl5_16 | ~spl5_54),
% 2.75/0.75    inference(avatar_split_clause,[],[f1177,f635,f149,f619,f1618])).
% 2.75/0.75  fof(f1618,plain,(
% 2.75/0.75    spl5_107 <=> ! [X31,X30] : (~r1_tarski(X30,X31) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30) | ~r1_tarski(X31,sK3))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 2.75/0.75  fof(f1177,plain,(
% 2.75/0.75    ( ! [X30,X31,X29] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X29) | ~r1_tarski(X29,sK4) | ~r1_tarski(X30,X31) | ~r1_tarski(X31,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30)) ) | (~spl5_16 | ~spl5_54)),
% 2.75/0.75    inference(resolution,[],[f636,f277])).
% 2.75/0.75  fof(f1616,plain,(
% 2.75/0.75    spl5_64 | spl5_53 | ~spl5_16 | ~spl5_54),
% 2.75/0.75    inference(avatar_split_clause,[],[f1178,f635,f149,f619,f918])).
% 2.75/0.75  fof(f1178,plain,(
% 2.75/0.75    ( ! [X33,X32] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X32) | ~r1_tarski(X32,sK4) | ~r1_tarski(X33,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X33)) ) | (~spl5_16 | ~spl5_54)),
% 2.75/0.75    inference(resolution,[],[f636,f229])).
% 2.75/0.75  fof(f1615,plain,(
% 2.75/0.75    spl5_53 | spl5_106 | ~spl5_2 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1447,f149,f77,f1613,f619])).
% 2.75/0.75  fof(f1613,plain,(
% 2.75/0.75    spl5_106 <=> ! [X73,X69,X71,X72,X74] : (~v1_relat_1(X69) | ~r1_tarski(k1_relat_1(X69),X73) | ~r1_tarski(X72,sK3) | ~r1_tarski(X73,X74) | ~r1_tarski(X74,X72) | ~r1_tarski(k2_relat_1(X69),X71) | v4_relat_1(X69,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 2.75/0.75  fof(f1447,plain,(
% 2.75/0.75    ( ! [X70,X74,X72,X71,X69,X73] : (~v1_relat_1(X69) | v4_relat_1(X69,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X70) | ~r1_tarski(X70,sK4) | ~r1_tarski(k2_relat_1(X69),X71) | ~r1_tarski(X72,sK3) | ~r1_tarski(X73,X74) | ~r1_tarski(X74,X72) | ~r1_tarski(k1_relat_1(X69),X73)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f779,f439])).
% 2.75/0.75  fof(f1611,plain,(
% 2.75/0.75    spl5_53 | spl5_105 | ~spl5_2 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1448,f149,f77,f1609,f619])).
% 2.75/0.75  fof(f1609,plain,(
% 2.75/0.75    spl5_105 <=> ! [X75,X77,X79,X78] : (~v1_relat_1(X75) | ~r1_tarski(k1_relat_1(X75),X78) | ~r1_tarski(X78,X79) | ~r1_tarski(X79,sK3) | ~r1_tarski(k2_relat_1(X75),X77) | v4_relat_1(X75,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 2.75/0.75  fof(f1448,plain,(
% 2.75/0.75    ( ! [X78,X76,X79,X77,X75] : (~v1_relat_1(X75) | v4_relat_1(X75,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X76) | ~r1_tarski(X76,sK4) | ~r1_tarski(k2_relat_1(X75),X77) | ~r1_tarski(X78,X79) | ~r1_tarski(X79,sK3) | ~r1_tarski(k1_relat_1(X75),X78)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f779,f277])).
% 2.75/0.75  fof(f1607,plain,(
% 2.75/0.75    spl5_53 | spl5_104 | ~spl5_2 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1449,f149,f77,f1605,f619])).
% 2.75/0.75  fof(f1605,plain,(
% 2.75/0.75    spl5_104 <=> ! [X82,X83,X80] : (~v1_relat_1(X80) | ~r1_tarski(k1_relat_1(X80),X83) | ~r1_tarski(X83,sK3) | ~r1_tarski(k2_relat_1(X80),X82) | v4_relat_1(X80,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 2.75/0.75  fof(f1449,plain,(
% 2.75/0.75    ( ! [X80,X83,X81,X82] : (~v1_relat_1(X80) | v4_relat_1(X80,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X81) | ~r1_tarski(X81,sK4) | ~r1_tarski(k2_relat_1(X80),X82) | ~r1_tarski(X83,sK3) | ~r1_tarski(k1_relat_1(X80),X83)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f779,f229])).
% 2.75/0.75  fof(f1603,plain,(
% 2.75/0.75    spl5_53 | spl5_103 | ~spl5_2 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1450,f149,f77,f1601,f619])).
% 2.75/0.75  fof(f1601,plain,(
% 2.75/0.75    spl5_103 <=> ! [X84,X86] : (~v1_relat_1(X84) | ~r1_tarski(k1_relat_1(X84),sK3) | ~r1_tarski(k2_relat_1(X84),X86) | v4_relat_1(X84,u1_struct_0(sK2)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 2.75/0.75  fof(f1450,plain,(
% 2.75/0.75    ( ! [X85,X86,X84] : (~v1_relat_1(X84) | v4_relat_1(X84,u1_struct_0(sK2)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X85) | ~r1_tarski(X85,sK4) | ~r1_tarski(k2_relat_1(X84),X86) | ~r1_tarski(k1_relat_1(X84),sK3)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f779,f213])).
% 2.75/0.75  fof(f1599,plain,(
% 2.75/0.75    spl5_53 | spl5_102 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1466,f149,f144,f1597,f619])).
% 2.75/0.75  fof(f1597,plain,(
% 2.75/0.75    spl5_102 <=> ! [X73,X69,X71,X72,X74] : (~v1_relat_1(X69) | ~r1_tarski(k1_relat_1(X69),X73) | ~r1_tarski(X72,sK3) | ~r1_tarski(X73,X74) | ~r1_tarski(X74,X72) | ~r1_tarski(k2_relat_1(X69),X71) | v4_relat_1(X69,u1_struct_0(sK1)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 2.75/0.75  fof(f1466,plain,(
% 2.75/0.75    ( ! [X70,X74,X72,X71,X69,X73] : (~v1_relat_1(X69) | v4_relat_1(X69,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X70) | ~r1_tarski(X70,sK4) | ~r1_tarski(k2_relat_1(X69),X71) | ~r1_tarski(X72,sK3) | ~r1_tarski(X73,X74) | ~r1_tarski(X74,X72) | ~r1_tarski(k1_relat_1(X69),X73)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f783,f439])).
% 2.75/0.75  fof(f1595,plain,(
% 2.75/0.75    spl5_53 | spl5_101 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1467,f149,f144,f1593,f619])).
% 2.75/0.75  fof(f1593,plain,(
% 2.75/0.75    spl5_101 <=> ! [X75,X77,X79,X78] : (~v1_relat_1(X75) | ~r1_tarski(k1_relat_1(X75),X78) | ~r1_tarski(X78,X79) | ~r1_tarski(X79,sK3) | ~r1_tarski(k2_relat_1(X75),X77) | v4_relat_1(X75,u1_struct_0(sK1)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 2.75/0.75  fof(f1467,plain,(
% 2.75/0.75    ( ! [X78,X76,X79,X77,X75] : (~v1_relat_1(X75) | v4_relat_1(X75,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X76) | ~r1_tarski(X76,sK4) | ~r1_tarski(k2_relat_1(X75),X77) | ~r1_tarski(X78,X79) | ~r1_tarski(X79,sK3) | ~r1_tarski(k1_relat_1(X75),X78)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f783,f277])).
% 2.75/0.75  fof(f1591,plain,(
% 2.75/0.75    spl5_53 | spl5_100 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1468,f149,f144,f1589,f619])).
% 2.75/0.75  fof(f1589,plain,(
% 2.75/0.75    spl5_100 <=> ! [X82,X83,X80] : (~v1_relat_1(X80) | ~r1_tarski(k1_relat_1(X80),X83) | ~r1_tarski(X83,sK3) | ~r1_tarski(k2_relat_1(X80),X82) | v4_relat_1(X80,u1_struct_0(sK1)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 2.75/0.75  fof(f1468,plain,(
% 2.75/0.75    ( ! [X80,X83,X81,X82] : (~v1_relat_1(X80) | v4_relat_1(X80,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X81) | ~r1_tarski(X81,sK4) | ~r1_tarski(k2_relat_1(X80),X82) | ~r1_tarski(X83,sK3) | ~r1_tarski(k1_relat_1(X80),X83)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f783,f229])).
% 2.75/0.75  fof(f1587,plain,(
% 2.75/0.75    spl5_53 | spl5_99 | ~spl5_15 | ~spl5_16),
% 2.75/0.75    inference(avatar_split_clause,[],[f1469,f149,f144,f1585,f619])).
% 2.75/0.75  fof(f1585,plain,(
% 2.75/0.75    spl5_99 <=> ! [X84,X86] : (~v1_relat_1(X84) | ~r1_tarski(k1_relat_1(X84),sK3) | ~r1_tarski(k2_relat_1(X84),X86) | v4_relat_1(X84,u1_struct_0(sK1)))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 2.75/0.75  fof(f1469,plain,(
% 2.75/0.75    ( ! [X85,X86,X84] : (~v1_relat_1(X84) | v4_relat_1(X84,u1_struct_0(sK1)) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X85) | ~r1_tarski(X85,sK4) | ~r1_tarski(k2_relat_1(X84),X86) | ~r1_tarski(k1_relat_1(X84),sK3)) ) | (~spl5_15 | ~spl5_16)),
% 2.75/0.75    inference(resolution,[],[f783,f213])).
% 2.75/0.75  fof(f1583,plain,(
% 2.75/0.75    ~spl5_97 | spl5_98 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1523,f893,f1581,f1577])).
% 2.75/0.75  fof(f1577,plain,(
% 2.75/0.75    spl5_97 <=> v1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 2.75/0.75  fof(f1581,plain,(
% 2.75/0.75    spl5_98 <=> ! [X40,X42,X41] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42),sK4) | ~r1_tarski(k2_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X41) | ~r1_tarski(k1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X40) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X42))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 2.75/0.75  fof(f1523,plain,(
% 2.75/0.75    ( ! [X41,X42,X40] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X42) | ~r1_tarski(k1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X40) | ~v1_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(k2_relat_1(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),X41)) ) | ~spl5_63),
% 2.75/0.75    inference(resolution,[],[f894,f753])).
% 2.75/0.75  fof(f1575,plain,(
% 2.75/0.75    ~spl5_96 | spl5_93 | ~spl5_16 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1522,f893,f149,f1560,f1572])).
% 2.75/0.75  fof(f1560,plain,(
% 2.75/0.75    spl5_93 <=> ! [X30] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X30))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 2.75/0.75  fof(f1522,plain,(
% 2.75/0.75    ( ! [X39] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X39),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X39) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3)) ) | (~spl5_16 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f213])).
% 2.75/0.75  fof(f1570,plain,(
% 2.75/0.75    spl5_95 | spl5_93 | ~spl5_16 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1521,f893,f149,f1560,f1568])).
% 2.75/0.75  fof(f1521,plain,(
% 2.75/0.75    ( ! [X37,X38] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X37),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X37) | ~r1_tarski(X38,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X38)) ) | (~spl5_16 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f229])).
% 2.75/0.75  fof(f1566,plain,(
% 2.75/0.75    spl5_94 | spl5_93 | ~spl5_16 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1520,f893,f149,f1560,f1564])).
% 2.75/0.75  fof(f1520,plain,(
% 2.75/0.75    ( ! [X35,X36,X34] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X34),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X34) | ~r1_tarski(X35,X36) | ~r1_tarski(X36,sK3) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35)) ) | (~spl5_16 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f277])).
% 2.75/0.75  fof(f1562,plain,(
% 2.75/0.75    spl5_92 | spl5_93 | ~spl5_16 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1519,f893,f149,f1560,f1557])).
% 2.75/0.75  fof(f1519,plain,(
% 2.75/0.75    ( ! [X30,X33,X31,X32] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X30) | ~r1_tarski(X31,sK3) | ~r1_tarski(X32,X33) | ~r1_tarski(X33,X31) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X32)) ) | (~spl5_16 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f439])).
% 2.75/0.75  fof(f1555,plain,(
% 2.75/0.75    ~spl5_90 | spl5_91 | ~spl5_15 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1518,f893,f144,f1549,f1544])).
% 2.75/0.75  fof(f1544,plain,(
% 2.75/0.75    spl5_90 <=> r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4)),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 2.75/0.75  fof(f1549,plain,(
% 2.75/0.75    spl5_91 <=> ! [X15] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X15),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X15))),
% 2.75/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 2.75/0.75  fof(f1518,plain,(
% 2.75/0.75    ( ! [X29] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X29),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X29) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4)) ) | (~spl5_15 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f215])).
% 2.75/0.75  fof(f1554,plain,(
% 2.75/0.75    spl5_89 | spl5_91 | ~spl5_15 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1517,f893,f144,f1549,f1540])).
% 2.75/0.75  fof(f1517,plain,(
% 2.75/0.75    ( ! [X28,X27] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X27),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X27) | ~r1_tarski(X28,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X28)) ) | (~spl5_15 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f219])).
% 2.75/0.75  fof(f1553,plain,(
% 2.75/0.75    spl5_88 | spl5_91 | ~spl5_15 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1516,f893,f144,f1549,f1536])).
% 2.75/0.75  fof(f1516,plain,(
% 2.75/0.75    ( ! [X26,X24,X25] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X24),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X24) | ~r1_tarski(X25,X26) | ~r1_tarski(X26,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X25)) ) | (~spl5_15 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f245])).
% 2.75/0.75  fof(f1552,plain,(
% 2.75/0.75    spl5_87 | spl5_91 | ~spl5_15 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1515,f893,f144,f1549,f1532])).
% 2.75/0.75  fof(f1515,plain,(
% 2.75/0.75    ( ! [X23,X21,X22,X20] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X20),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X20) | ~r1_tarski(X21,sK4) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X22)) ) | (~spl5_15 | ~spl5_63)),
% 2.75/0.75    inference(resolution,[],[f894,f370])).
% 2.75/0.75  fof(f1551,plain,(
% 2.75/0.75    spl5_85 | spl5_91 | ~spl5_15 | ~spl5_63),
% 2.75/0.75    inference(avatar_split_clause,[],[f1514,f893,f144,f1549,f1525])).
% 2.75/0.76  fof(f1514,plain,(
% 2.75/0.76    ( ! [X19,X17,X15,X18,X16] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),X15),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X15) | ~r1_tarski(X16,X17) | ~r1_tarski(X17,X18) | ~r1_tarski(X19,X16) | ~r1_tarski(X18,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X19)) ) | (~spl5_15 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f654])).
% 2.75/0.76  fof(f654,plain,(
% 2.75/0.76    ( ! [X24,X23,X21,X25,X22] : (r1_tarski(X25,u1_struct_0(sK1)) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(X24,X22) | ~r1_tarski(X21,sK4) | ~r1_tarski(X25,X24)) ) | ~spl5_15),
% 2.75/0.76    inference(resolution,[],[f370,f68])).
% 2.75/0.76  fof(f1547,plain,(
% 2.75/0.76    ~spl5_90 | spl5_86 | ~spl5_2 | ~spl5_63),
% 2.75/0.76    inference(avatar_split_clause,[],[f1513,f893,f77,f1528,f1544])).
% 2.75/0.76  fof(f1528,plain,(
% 2.75/0.76    spl5_86 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X0),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 2.75/0.76  fof(f1513,plain,(
% 2.75/0.76    ( ! [X14] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X14),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X14) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4)) ) | (~spl5_2 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f214])).
% 2.75/0.76  fof(f1542,plain,(
% 2.75/0.76    spl5_89 | spl5_86 | ~spl5_2 | ~spl5_63),
% 2.75/0.76    inference(avatar_split_clause,[],[f1512,f893,f77,f1528,f1540])).
% 2.75/0.76  fof(f1512,plain,(
% 2.75/0.76    ( ! [X12,X13] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X12),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12) | ~r1_tarski(X13,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13)) ) | (~spl5_2 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f216])).
% 2.75/0.76  fof(f1538,plain,(
% 2.75/0.76    spl5_88 | spl5_86 | ~spl5_2 | ~spl5_63),
% 2.75/0.76    inference(avatar_split_clause,[],[f1511,f893,f77,f1528,f1536])).
% 2.75/0.76  fof(f1511,plain,(
% 2.75/0.76    ( ! [X10,X11,X9] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X9),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X9) | ~r1_tarski(X10,X11) | ~r1_tarski(X11,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X10)) ) | (~spl5_2 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f240])).
% 2.75/0.76  fof(f1534,plain,(
% 2.75/0.76    spl5_87 | spl5_86 | ~spl5_2 | ~spl5_63),
% 2.75/0.76    inference(avatar_split_clause,[],[f1510,f893,f77,f1528,f1532])).
% 2.75/0.76  fof(f1510,plain,(
% 2.75/0.76    ( ! [X6,X8,X7,X5] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X5),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X5) | ~r1_tarski(X6,sK4) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X7)) ) | (~spl5_2 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f341])).
% 2.75/0.76  fof(f1530,plain,(
% 2.75/0.76    spl5_85 | spl5_86 | ~spl5_2 | ~spl5_63),
% 2.75/0.76    inference(avatar_split_clause,[],[f1509,f893,f77,f1528,f1525])).
% 2.75/0.76  fof(f1509,plain,(
% 2.75/0.76    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK2),X0),sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X4,X1) | ~r1_tarski(X3,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)) ) | (~spl5_2 | ~spl5_63)),
% 2.75/0.76    inference(resolution,[],[f894,f586])).
% 2.75/0.76  fof(f586,plain,(
% 2.75/0.76    ( ! [X21,X19,X22,X20,X18] : (r1_tarski(X22,u1_struct_0(sK2)) | ~r1_tarski(X19,X20) | ~r1_tarski(X20,X18) | ~r1_tarski(X21,X19) | ~r1_tarski(X18,sK4) | ~r1_tarski(X22,X21)) ) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f341,f68])).
% 2.75/0.76  fof(f1408,plain,(
% 2.75/0.76    ~spl5_20 | spl5_84 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1399,f149,f1406,f171])).
% 2.75/0.76  fof(f1406,plain,(
% 2.75/0.76    spl5_84 <=> ! [X1,X2] : (v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2) | ~v1_relat_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2)))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 2.75/0.76  fof(f1399,plain,(
% 2.75/0.76    ( ! [X2,X1] : (v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) ) | ~spl5_16),
% 2.75/0.76    inference(duplicate_literal_removal,[],[f1394])).
% 2.75/0.76  fof(f1394,plain,(
% 2.75/0.76    ( ! [X2,X1] : (v4_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2),X2) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),X2)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(sK3) | ~v1_relat_1(k7_relat_1(sK3,X1))) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f1367,f251])).
% 2.75/0.76  fof(f1404,plain,(
% 2.75/0.76    ~spl5_20 | spl5_83 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1400,f149,f1402,f171])).
% 2.75/0.76  fof(f1402,plain,(
% 2.75/0.76    spl5_83 <=> ! [X0] : (v4_relat_1(k7_relat_1(sK3,X0),X0) | ~v1_relat_1(k7_relat_1(sK3,X0)))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 2.75/0.76  fof(f1400,plain,(
% 2.75/0.76    ( ! [X0] : (v4_relat_1(k7_relat_1(sK3,X0),X0) | ~v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) ) | ~spl5_16),
% 2.75/0.76    inference(duplicate_literal_removal,[],[f1393])).
% 2.75/0.76  fof(f1393,plain,(
% 2.75/0.76    ( ! [X0] : (v4_relat_1(k7_relat_1(sK3,X0),X0) | ~v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f1367,f59])).
% 2.75/0.76  fof(f1233,plain,(
% 2.75/0.76    ~spl5_19 | spl5_82 | ~spl5_78),
% 2.75/0.76    inference(avatar_split_clause,[],[f1225,f1186,f1231,f167])).
% 2.75/0.76  fof(f1231,plain,(
% 2.75/0.76    spl5_82 <=> ! [X49,X51,X48,X50] : (~r1_tarski(X48,sK4) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X50) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X49) | ~r1_tarski(k2_zfmisc_1(X49,X50),X51) | ~r1_tarski(X51,X48))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 2.75/0.76  fof(f1225,plain,(
% 2.75/0.76    ( ! [X50,X48,X51,X49] : (~r1_tarski(X48,sK4) | ~r1_tarski(k2_zfmisc_1(X49,X50),X51) | ~r1_tarski(X51,X48) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X49) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X50)) ) | ~spl5_78),
% 2.75/0.76    inference(resolution,[],[f1187,f753])).
% 2.75/0.76  fof(f1187,plain,(
% 2.75/0.76    ( ! [X6,X8,X7] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7) | ~r1_tarski(X6,sK4) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6)) ) | ~spl5_78),
% 2.75/0.76    inference(avatar_component_clause,[],[f1186])).
% 2.75/0.76  fof(f1229,plain,(
% 2.75/0.76    spl5_77 | spl5_81 | ~spl5_2 | ~spl5_78),
% 2.75/0.76    inference(avatar_split_clause,[],[f1212,f1186,f77,f1227,f1182])).
% 2.75/0.76  fof(f1182,plain,(
% 2.75/0.76    spl5_77 <=> ! [X1,X3,X2,X4] : (~r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X4) | ~r1_tarski(X3,sK4) | ~r1_tarski(X4,X1) | ~r1_tarski(X2,X3))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 2.75/0.76  fof(f1227,plain,(
% 2.75/0.76    spl5_81 <=> ! [X1,X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(u1_struct_0(sK2),X1) | ~r1_tarski(X1,X0))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 2.75/0.76  fof(f1212,plain,(
% 2.75/0.76    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(X0,sK4) | ~r1_tarski(u1_struct_0(sK2),X1) | ~r1_tarski(X1,X0) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X4) | ~r1_tarski(X5,X2) | ~r1_tarski(X4,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X5)) ) | (~spl5_2 | ~spl5_78)),
% 2.75/0.76    inference(resolution,[],[f1187,f586])).
% 2.75/0.76  fof(f1196,plain,(
% 2.75/0.76    ~spl5_19 | spl5_80 | ~spl5_54),
% 2.75/0.76    inference(avatar_split_clause,[],[f1180,f635,f1194,f167])).
% 2.75/0.76  fof(f1194,plain,(
% 2.75/0.76    spl5_80 <=> ! [X36,X35,X37] : (~r1_tarski(k2_zfmisc_1(X35,X36),X37) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X36) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35) | ~r1_tarski(X37,sK4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 2.75/0.76  fof(f1180,plain,(
% 2.75/0.76    ( ! [X37,X35,X36] : (~r1_tarski(k2_zfmisc_1(X35,X36),X37) | ~r1_tarski(X37,sK4) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X35) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X36)) ) | ~spl5_54),
% 2.75/0.76    inference(resolution,[],[f636,f753])).
% 2.75/0.76  fof(f1192,plain,(
% 2.75/0.76    spl5_78 | spl5_79 | ~spl5_15 | ~spl5_54),
% 2.75/0.76    inference(avatar_split_clause,[],[f1172,f635,f144,f1190,f1186])).
% 2.75/0.76  fof(f1172,plain,(
% 2.75/0.76    ( ! [X17,X15,X18,X16] : (~r1_tarski(u1_struct_0(sK1),X15) | ~r1_tarski(X15,sK4) | ~r1_tarski(X16,sK4) | ~r1_tarski(X17,X18) | ~r1_tarski(X18,X16) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X17)) ) | (~spl5_15 | ~spl5_54)),
% 2.75/0.76    inference(resolution,[],[f636,f370])).
% 2.75/0.76  fof(f1188,plain,(
% 2.75/0.76    spl5_78 | spl5_73 | ~spl5_2 | ~spl5_54),
% 2.75/0.76    inference(avatar_split_clause,[],[f1168,f635,f77,f1134,f1186])).
% 2.75/0.76  fof(f1168,plain,(
% 2.75/0.76    ( ! [X6,X8,X7,X5] : (~r1_tarski(u1_struct_0(sK2),X5) | ~r1_tarski(X5,sK4) | ~r1_tarski(X6,sK4) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X7)) ) | (~spl5_2 | ~spl5_54)),
% 2.75/0.76    inference(resolution,[],[f636,f341])).
% 2.75/0.76  fof(f1184,plain,(
% 2.75/0.76    spl5_77 | spl5_73 | ~spl5_2 | ~spl5_54),
% 2.75/0.76    inference(avatar_split_clause,[],[f1167,f635,f77,f1134,f1182])).
% 2.75/0.76  fof(f1167,plain,(
% 2.75/0.76    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(u1_struct_0(sK2),X0) | ~r1_tarski(X0,sK4) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X4,X1) | ~r1_tarski(X3,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X4)) ) | (~spl5_2 | ~spl5_54)),
% 2.75/0.76    inference(resolution,[],[f636,f586])).
% 2.75/0.76  fof(f1166,plain,(
% 2.75/0.76    spl5_37 | spl5_54 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1157,f149,f77,f635,f362])).
% 2.75/0.76  fof(f362,plain,(
% 2.75/0.76    spl5_37 <=> ! [X13] : (v5_relat_1(X13,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X13),sK3) | ~v1_relat_1(X13))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.75/0.76  fof(f1157,plain,(
% 2.75/0.76    ( ! [X64,X62,X63] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X62) | ~r1_tarski(X62,X63) | ~r1_tarski(X63,sK4) | v5_relat_1(X64,u1_struct_0(sK2)) | ~v1_relat_1(X64) | ~r1_tarski(k2_relat_1(X64),sK3)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f590,f213])).
% 2.75/0.76  fof(f1165,plain,(
% 2.75/0.76    spl5_35 | spl5_54 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1156,f149,f77,f635,f354])).
% 2.75/0.76  fof(f354,plain,(
% 2.75/0.76    spl5_35 <=> ! [X11,X12] : (v5_relat_1(X11,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X11),X12) | ~r1_tarski(X12,sK3) | ~v1_relat_1(X11))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.75/0.76  fof(f1156,plain,(
% 2.75/0.76    ( ! [X61,X59,X60,X58] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X58) | ~r1_tarski(X58,X59) | ~r1_tarski(X59,sK4) | v5_relat_1(X60,u1_struct_0(sK2)) | ~v1_relat_1(X60) | ~r1_tarski(X61,sK3) | ~r1_tarski(k2_relat_1(X60),X61)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f590,f229])).
% 2.75/0.76  fof(f1164,plain,(
% 2.75/0.76    spl5_52 | spl5_54 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1155,f149,f77,f635,f616])).
% 2.75/0.76  fof(f1155,plain,(
% 2.75/0.76    ( ! [X57,X54,X56,X55,X53] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X53) | ~r1_tarski(X53,X54) | ~r1_tarski(X54,sK4) | v5_relat_1(X55,u1_struct_0(sK2)) | ~v1_relat_1(X55) | ~r1_tarski(X56,X57) | ~r1_tarski(X57,sK3) | ~r1_tarski(k2_relat_1(X55),X56)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f590,f277])).
% 2.75/0.76  fof(f1163,plain,(
% 2.75/0.76    spl5_76 | spl5_54 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f1154,f149,f77,f635,f1161])).
% 2.75/0.76  fof(f1154,plain,(
% 2.75/0.76    ( ! [X47,X52,X50,X48,X51,X49] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X47) | ~r1_tarski(X47,X48) | ~r1_tarski(X48,sK4) | v5_relat_1(X49,u1_struct_0(sK2)) | ~v1_relat_1(X49) | ~r1_tarski(X50,sK3) | ~r1_tarski(X51,X52) | ~r1_tarski(X52,X50) | ~r1_tarski(k2_relat_1(X49),X51)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f590,f439])).
% 2.75/0.76  fof(f1143,plain,(
% 2.75/0.76    spl5_73 | spl5_75 | ~spl5_2),
% 2.75/0.76    inference(avatar_split_clause,[],[f1123,f77,f1141,f1134])).
% 2.75/0.76  fof(f1141,plain,(
% 2.75/0.76    spl5_75 <=> ! [X84,X86,X85,X87,X88] : (~r1_tarski(X84,X85) | ~v1_relat_1(X88) | v5_relat_1(X88,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X88),X87) | ~r1_tarski(X86,sK4) | ~r1_tarski(X87,X84) | ~r1_tarski(X85,X86))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 2.75/0.76  fof(f1123,plain,(
% 2.75/0.76    ( ! [X88,X87,X85,X89,X86,X84] : (~r1_tarski(X84,X85) | ~r1_tarski(X85,X86) | ~r1_tarski(X87,X84) | ~r1_tarski(X86,sK4) | ~r1_tarski(k2_relat_1(X88),X87) | ~r1_tarski(X89,sK4) | ~r1_tarski(u1_struct_0(sK2),X89) | v5_relat_1(X88,u1_struct_0(sK2)) | ~v1_relat_1(X88)) ) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f586,f343])).
% 2.75/0.76  fof(f1139,plain,(
% 2.75/0.76    spl5_73 | spl5_74 | ~spl5_2 | ~spl5_15),
% 2.75/0.76    inference(avatar_split_clause,[],[f1122,f144,f77,f1137,f1134])).
% 2.75/0.76  fof(f1137,plain,(
% 2.75/0.76    spl5_74 <=> ! [X82,X79,X81,X78,X80] : (~r1_tarski(X78,X79) | ~v1_relat_1(X82) | v5_relat_1(X82,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X82),X81) | ~r1_tarski(X80,sK4) | ~r1_tarski(X81,X78) | ~r1_tarski(X79,X80))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 2.75/0.76  fof(f1122,plain,(
% 2.75/0.76    ( ! [X80,X78,X83,X81,X79,X82] : (~r1_tarski(X78,X79) | ~r1_tarski(X79,X80) | ~r1_tarski(X81,X78) | ~r1_tarski(X80,sK4) | ~r1_tarski(k2_relat_1(X82),X81) | ~r1_tarski(X83,sK4) | ~r1_tarski(u1_struct_0(sK2),X83) | v5_relat_1(X82,u1_struct_0(sK1)) | ~v1_relat_1(X82)) ) | (~spl5_2 | ~spl5_15)),
% 2.75/0.76    inference(resolution,[],[f586,f373])).
% 2.75/0.76  fof(f1081,plain,(
% 2.75/0.76    spl5_72 | spl5_64 | ~spl5_16 | ~spl5_71),
% 2.75/0.76    inference(avatar_split_clause,[],[f1073,f1058,f149,f918,f1079])).
% 2.75/0.76  fof(f1079,plain,(
% 2.75/0.76    spl5_72 <=> ! [X22,X21,X23] : (~r1_tarski(X21,sK3) | ~r1_tarski(u1_struct_0(sK0),X22) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 2.75/0.76  fof(f1073,plain,(
% 2.75/0.76    ( ! [X23,X21,X22,X20] : (~r1_tarski(X20,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20) | ~r1_tarski(X21,sK3) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(u1_struct_0(sK0),X22)) ) | (~spl5_16 | ~spl5_71)),
% 2.75/0.76    inference(resolution,[],[f1059,f439])).
% 2.75/0.76  fof(f1064,plain,(
% 2.75/0.76    ~spl5_20 | spl5_25 | spl5_71 | ~spl5_23 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f1045,f921,f206,f1058,f261,f171])).
% 2.75/0.76  fof(f261,plain,(
% 2.75/0.76    spl5_25 <=> v1_relat_1(k2_relat_1(sK3))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.75/0.76  fof(f206,plain,(
% 2.75/0.76    spl5_23 <=> v5_relat_1(sK3,u1_struct_0(sK0))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.75/0.76  fof(f1045,plain,(
% 2.75/0.76    ( ! [X72,X71] : (~r1_tarski(X71,sK3) | ~r1_tarski(u1_struct_0(sK0),X72) | ~r1_tarski(X72,X71) | v1_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | (~spl5_23 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f938,f208])).
% 2.75/0.76  fof(f208,plain,(
% 2.75/0.76    v5_relat_1(sK3,u1_struct_0(sK0)) | ~spl5_23),
% 2.75/0.76    inference(avatar_component_clause,[],[f206])).
% 2.75/0.76  fof(f938,plain,(
% 2.75/0.76    ( ! [X61,X59,X62,X60] : (~v5_relat_1(X59,X61) | ~r1_tarski(X60,sK3) | ~r1_tarski(X61,X62) | ~r1_tarski(X62,X60) | v1_relat_1(k2_relat_1(X59)) | ~v1_relat_1(X59)) ) | ~spl5_65),
% 2.75/0.76    inference(resolution,[],[f922,f61])).
% 2.75/0.76  fof(f1063,plain,(
% 2.75/0.76    spl5_27 | spl5_71 | ~spl5_16 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f1032,f921,f149,f1058,f270])).
% 2.75/0.76  fof(f270,plain,(
% 2.75/0.76    spl5_27 <=> ! [X3] : (~v1_relat_1(X3) | ~r1_tarski(X3,sK3) | v1_relat_1(k2_relat_1(X3)))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.75/0.76  fof(f1032,plain,(
% 2.75/0.76    ( ! [X17,X15,X16] : (~r1_tarski(X15,sK3) | ~r1_tarski(u1_struct_0(sK0),X16) | ~r1_tarski(X16,X15) | v1_relat_1(k2_relat_1(X17)) | ~v1_relat_1(X17) | ~r1_tarski(X17,sK3)) ) | (~spl5_16 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f938,f227])).
% 2.75/0.76  fof(f1062,plain,(
% 2.75/0.76    spl5_33 | spl5_71 | ~spl5_16 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f1031,f921,f149,f1058,f327])).
% 2.75/0.76  fof(f327,plain,(
% 2.75/0.76    spl5_33 <=> ! [X1,X0] : (v1_relat_1(k2_relat_1(X0)) | ~r1_tarski(X1,sK3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.75/0.76  fof(f1031,plain,(
% 2.75/0.76    ( ! [X14,X12,X13,X11] : (~r1_tarski(X11,sK3) | ~r1_tarski(u1_struct_0(sK0),X12) | ~r1_tarski(X12,X11) | v1_relat_1(k2_relat_1(X13)) | ~v1_relat_1(X13) | ~r1_tarski(X13,X14) | ~r1_tarski(X14,sK3)) ) | (~spl5_16 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f938,f275])).
% 2.75/0.76  fof(f1061,plain,(
% 2.75/0.76    spl5_47 | spl5_71 | ~spl5_16 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f1030,f921,f149,f1058,f553])).
% 2.75/0.76  fof(f553,plain,(
% 2.75/0.76    spl5_47 <=> ! [X1,X3,X2] : (v1_relat_1(k2_relat_1(X1)) | ~r1_tarski(X3,X2) | ~r1_tarski(X1,X3) | ~r1_tarski(X2,sK3) | ~v1_relat_1(X1))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 2.75/0.76  fof(f1030,plain,(
% 2.75/0.76    ( ! [X6,X10,X8,X7,X9] : (~r1_tarski(X6,sK3) | ~r1_tarski(u1_struct_0(sK0),X7) | ~r1_tarski(X7,X6) | v1_relat_1(k2_relat_1(X8)) | ~v1_relat_1(X8) | ~r1_tarski(X9,sK3) | ~r1_tarski(X8,X10) | ~r1_tarski(X10,X9)) ) | (~spl5_16 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f938,f436])).
% 2.75/0.76  fof(f436,plain,(
% 2.75/0.76    ( ! [X2,X0,X1] : (v5_relat_1(X2,u1_struct_0(sK0)) | ~r1_tarski(X1,sK3) | ~r1_tarski(X2,X0) | ~r1_tarski(X0,X1)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f277,f204])).
% 2.75/0.76  fof(f1060,plain,(
% 2.75/0.76    spl5_70 | spl5_71 | ~spl5_16 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f1029,f921,f149,f1058,f1055])).
% 2.75/0.76  fof(f1055,plain,(
% 2.75/0.76    spl5_70 <=> ! [X3,X5,X2,X4] : (v1_relat_1(k2_relat_1(X2)) | ~r1_tarski(X5,sK3) | ~r1_tarski(X2,X3) | ~r1_tarski(X4,X5) | ~r1_tarski(X3,X4) | ~v1_relat_1(X2))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 2.75/0.76  fof(f1029,plain,(
% 2.75/0.76    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(X0,sK3) | ~r1_tarski(u1_struct_0(sK0),X1) | ~r1_tarski(X1,X0) | v1_relat_1(k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r1_tarski(X3,X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,sK3)) ) | (~spl5_16 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f938,f896])).
% 2.75/0.76  fof(f896,plain,(
% 2.75/0.76    ( ! [X2,X0,X3,X1] : (v5_relat_1(X3,u1_struct_0(sK0)) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0) | ~r1_tarski(X3,X1) | ~r1_tarski(X0,sK3)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f439,f204])).
% 2.75/0.76  fof(f999,plain,(
% 2.75/0.76    spl5_69 | spl5_64 | ~spl5_16 | ~spl5_67),
% 2.75/0.76    inference(avatar_split_clause,[],[f991,f958,f149,f918,f997])).
% 2.75/0.76  fof(f997,plain,(
% 2.75/0.76    spl5_69 <=> ! [X22,X21,X23] : (~r1_tarski(X21,sK3) | ~r1_tarski(u1_struct_0(sK1),X22) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 2.75/0.76  fof(f991,plain,(
% 2.75/0.76    ( ! [X23,X21,X22,X20] : (~r1_tarski(X20,sK3) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20) | ~r1_tarski(X21,sK3) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(u1_struct_0(sK1),X22)) ) | (~spl5_16 | ~spl5_67)),
% 2.75/0.76    inference(resolution,[],[f959,f439])).
% 2.75/0.76  fof(f982,plain,(
% 2.75/0.76    spl5_68 | spl5_64 | ~spl5_16 | ~spl5_46),
% 2.75/0.76    inference(avatar_split_clause,[],[f974,f522,f149,f918,f980])).
% 2.75/0.76  fof(f980,plain,(
% 2.75/0.76    spl5_68 <=> ! [X22,X21,X23] : (~r1_tarski(X21,sK3) | ~r1_tarski(u1_struct_0(sK2),X22) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 2.75/0.76  fof(f974,plain,(
% 2.75/0.76    ( ! [X23,X21,X22,X20] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X20) | ~r1_tarski(X20,sK3) | ~r1_tarski(X21,sK3) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(u1_struct_0(sK2),X22)) ) | (~spl5_16 | ~spl5_46)),
% 2.75/0.76    inference(resolution,[],[f523,f439])).
% 2.75/0.76  fof(f965,plain,(
% 2.75/0.76    spl5_67 | spl5_18 | ~spl5_15 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f949,f921,f144,f162,f958])).
% 2.75/0.76  fof(f162,plain,(
% 2.75/0.76    spl5_18 <=> v1_relat_1(sK4)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.75/0.76  fof(f949,plain,(
% 2.75/0.76    ( ! [X105,X106] : (v1_relat_1(sK4) | ~r1_tarski(X105,sK3) | ~r1_tarski(u1_struct_0(sK1),X106) | ~r1_tarski(X106,X105)) ) | (~spl5_15 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f146])).
% 2.75/0.76  fof(f964,plain,(
% 2.75/0.76    spl5_46 | spl5_18 | ~spl5_2 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f948,f921,f77,f162,f522])).
% 2.75/0.76  fof(f948,plain,(
% 2.75/0.76    ( ! [X103,X104] : (v1_relat_1(sK4) | ~r1_tarski(X103,sK3) | ~r1_tarski(u1_struct_0(sK2),X104) | ~r1_tarski(X104,X103)) ) | (~spl5_2 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f79])).
% 2.75/0.76  fof(f963,plain,(
% 2.75/0.76    spl5_67 | spl5_31 | ~spl5_15 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f932,f921,f144,f305,f958])).
% 2.75/0.76  fof(f305,plain,(
% 2.75/0.76    spl5_31 <=> ! [X2] : (v1_relat_1(X2) | ~r1_tarski(X2,sK4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.75/0.76  fof(f932,plain,(
% 2.75/0.76    ( ! [X35,X33,X34] : (v1_relat_1(X33) | ~r1_tarski(X34,sK3) | ~r1_tarski(u1_struct_0(sK1),X35) | ~r1_tarski(X35,X34) | ~r1_tarski(X33,sK4)) ) | (~spl5_15 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f215])).
% 2.75/0.76  fof(f962,plain,(
% 2.75/0.76    spl5_67 | spl5_30 | ~spl5_15 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f931,f921,f144,f301,f958])).
% 2.75/0.76  fof(f301,plain,(
% 2.75/0.76    spl5_30 <=> ! [X1,X0] : (v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,sK4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.75/0.76  fof(f931,plain,(
% 2.75/0.76    ( ! [X30,X31,X29,X32] : (v1_relat_1(X29) | ~r1_tarski(X30,sK3) | ~r1_tarski(u1_struct_0(sK1),X31) | ~r1_tarski(X31,X30) | ~r1_tarski(X32,sK4) | ~r1_tarski(X29,X32)) ) | (~spl5_15 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f219])).
% 2.75/0.76  fof(f961,plain,(
% 2.75/0.76    spl5_67 | spl5_41 | ~spl5_15 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f930,f921,f144,f475,f958])).
% 2.75/0.76  fof(f475,plain,(
% 2.75/0.76    spl5_41 <=> ! [X3,X0,X2] : (v1_relat_1(X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,sK4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.75/0.76  fof(f930,plain,(
% 2.75/0.76    ( ! [X28,X26,X24,X27,X25] : (v1_relat_1(X24) | ~r1_tarski(X25,sK3) | ~r1_tarski(u1_struct_0(sK1),X26) | ~r1_tarski(X26,X25) | ~r1_tarski(X27,X28) | ~r1_tarski(X28,sK4) | ~r1_tarski(X24,X27)) ) | (~spl5_15 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f245])).
% 2.75/0.76  fof(f960,plain,(
% 2.75/0.76    spl5_67 | spl5_66 | ~spl5_15 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f929,f921,f144,f951,f958])).
% 2.75/0.76  fof(f951,plain,(
% 2.75/0.76    spl5_66 <=> ! [X3,X5,X0,X4] : (v1_relat_1(X0) | ~r1_tarski(X0,X4) | ~r1_tarski(X3,sK4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,X3))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 2.75/0.76  fof(f929,plain,(
% 2.75/0.76    ( ! [X23,X21,X19,X22,X20,X18] : (v1_relat_1(X18) | ~r1_tarski(X19,sK3) | ~r1_tarski(u1_struct_0(sK1),X20) | ~r1_tarski(X20,X19) | ~r1_tarski(X21,sK4) | ~r1_tarski(X22,X23) | ~r1_tarski(X23,X21) | ~r1_tarski(X18,X22)) ) | (~spl5_15 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f370])).
% 2.75/0.76  fof(f956,plain,(
% 2.75/0.76    spl5_46 | spl5_31 | ~spl5_2 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f928,f921,f77,f305,f522])).
% 2.75/0.76  fof(f928,plain,(
% 2.75/0.76    ( ! [X17,X15,X16] : (v1_relat_1(X15) | ~r1_tarski(X16,sK3) | ~r1_tarski(u1_struct_0(sK2),X17) | ~r1_tarski(X17,X16) | ~r1_tarski(X15,sK4)) ) | (~spl5_2 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f214])).
% 2.75/0.76  fof(f955,plain,(
% 2.75/0.76    spl5_46 | spl5_30 | ~spl5_2 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f927,f921,f77,f301,f522])).
% 2.75/0.76  fof(f927,plain,(
% 2.75/0.76    ( ! [X14,X12,X13,X11] : (v1_relat_1(X11) | ~r1_tarski(X12,sK3) | ~r1_tarski(u1_struct_0(sK2),X13) | ~r1_tarski(X13,X12) | ~r1_tarski(X14,sK4) | ~r1_tarski(X11,X14)) ) | (~spl5_2 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f216])).
% 2.75/0.76  fof(f954,plain,(
% 2.75/0.76    spl5_46 | spl5_41 | ~spl5_2 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f926,f921,f77,f475,f522])).
% 2.75/0.76  fof(f926,plain,(
% 2.75/0.76    ( ! [X6,X10,X8,X7,X9] : (v1_relat_1(X6) | ~r1_tarski(X7,sK3) | ~r1_tarski(u1_struct_0(sK2),X8) | ~r1_tarski(X8,X7) | ~r1_tarski(X9,X10) | ~r1_tarski(X10,sK4) | ~r1_tarski(X6,X9)) ) | (~spl5_2 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f240])).
% 2.75/0.76  fof(f953,plain,(
% 2.75/0.76    spl5_46 | spl5_66 | ~spl5_2 | ~spl5_65),
% 2.75/0.76    inference(avatar_split_clause,[],[f925,f921,f77,f951,f522])).
% 2.75/0.76  fof(f925,plain,(
% 2.75/0.76    ( ! [X4,X2,X0,X5,X3,X1] : (v1_relat_1(X0) | ~r1_tarski(X1,sK3) | ~r1_tarski(u1_struct_0(sK2),X2) | ~r1_tarski(X2,X1) | ~r1_tarski(X3,sK4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,X3) | ~r1_tarski(X0,X4)) ) | (~spl5_2 | ~spl5_65)),
% 2.75/0.76    inference(resolution,[],[f922,f341])).
% 2.75/0.76  fof(f924,plain,(
% 2.75/0.76    ~spl5_19 | spl5_65 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f905,f149,f921,f167])).
% 2.75/0.76  fof(f905,plain,(
% 2.75/0.76    ( ! [X37,X35,X36,X34] : (~r1_tarski(X34,sK3) | ~r1_tarski(X35,X36) | ~r1_tarski(X36,X34) | ~r1_tarski(X37,X35) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(X37)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f439,f156])).
% 2.75/0.76  fof(f923,plain,(
% 2.75/0.76    spl5_64 | spl5_65 | ~spl5_16 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f902,f449,f149,f921,f918])).
% 2.75/0.76  fof(f902,plain,(
% 2.75/0.76    ( ! [X24,X23,X21,X22,X20] : (~r1_tarski(X20,sK3) | ~r1_tarski(X21,X22) | ~r1_tarski(X22,X20) | ~r1_tarski(X23,X21) | v1_relat_1(X23) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X24) | ~r1_tarski(X24,sK3)) ) | (~spl5_16 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f439,f450])).
% 2.75/0.76  fof(f895,plain,(
% 2.75/0.76    ~spl5_19 | spl5_63 | ~spl5_53),
% 2.75/0.76    inference(avatar_split_clause,[],[f876,f619,f893,f167])).
% 2.75/0.76  fof(f876,plain,(
% 2.75/0.76    ( ! [X12,X13] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X12) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X13) | ~r1_tarski(k2_zfmisc_1(X12,X13),sK4)) ) | ~spl5_53),
% 2.75/0.76    inference(resolution,[],[f753,f620])).
% 2.75/0.76  fof(f797,plain,(
% 2.75/0.76    ~spl5_18 | spl5_62 | ~spl5_2),
% 2.75/0.76    inference(avatar_split_clause,[],[f791,f77,f795,f162])).
% 2.75/0.76  fof(f795,plain,(
% 2.75/0.76    spl5_62 <=> ! [X3,X2,X4] : (~v1_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))),X4) | v4_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)),u1_struct_0(sK2)))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 2.75/0.76  fof(f791,plain,(
% 2.75/0.76    ( ! [X4,X2,X3] : (~v1_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))) | v4_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3)),u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(k7_relat_1(X2,k7_relat_1(sK4,X3))),X4) | ~v1_relat_1(sK4) | ~v1_relat_1(X2)) ) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f781,f252])).
% 2.75/0.76  fof(f781,plain,(
% 2.75/0.76    ( ! [X28,X27] : (~r1_tarski(k1_relat_1(X27),sK4) | ~v1_relat_1(X27) | v4_relat_1(X27,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X27),X28)) ) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f751,f214])).
% 2.75/0.76  fof(f773,plain,(
% 2.75/0.76    ~spl5_61 | spl5_56),
% 2.75/0.76    inference(avatar_split_clause,[],[f755,f742,f770])).
% 2.75/0.76  fof(f755,plain,(
% 2.75/0.76    ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | spl5_56),
% 2.75/0.76    inference(resolution,[],[f744,f64])).
% 2.75/0.76  fof(f768,plain,(
% 2.75/0.76    ~spl5_58 | ~spl5_59 | ~spl5_60 | spl5_56),
% 2.75/0.76    inference(avatar_split_clause,[],[f754,f742,f765,f761,f757])).
% 2.75/0.76  fof(f754,plain,(
% 2.75/0.76    ~r1_tarski(k2_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK0)) | ~r1_tarski(k1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)),u1_struct_0(sK2)) | ~v1_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | spl5_56),
% 2.75/0.76    inference(resolution,[],[f744,f65])).
% 2.75/0.76  fof(f749,plain,(
% 2.75/0.76    ~spl5_56 | ~spl5_57 | spl5_1),
% 2.75/0.76    inference(avatar_split_clause,[],[f740,f72,f746,f742])).
% 2.75/0.76  fof(f740,plain,(
% 2.75/0.76    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k9_relat_1(k2_tmap_1(sK1,sK0,sK3,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | spl5_1),
% 2.75/0.76    inference(superposition,[],[f74,f69])).
% 2.75/0.76  fof(f641,plain,(
% 2.75/0.76    spl5_54 | ~spl5_55 | ~spl5_15 | ~spl5_53),
% 2.75/0.76    inference(avatar_split_clause,[],[f628,f619,f144,f638,f635])).
% 2.75/0.76  fof(f638,plain,(
% 2.75/0.76    spl5_55 <=> r1_tarski(u1_struct_0(sK1),sK4)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 2.75/0.76  fof(f628,plain,(
% 2.75/0.76    ( ! [X6,X7] : (~r1_tarski(u1_struct_0(sK1),sK4) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X6)) ) | (~spl5_15 | ~spl5_53)),
% 2.75/0.76    inference(resolution,[],[f620,f245])).
% 2.75/0.76  fof(f623,plain,(
% 2.75/0.76    spl5_37 | spl5_53 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f613,f149,f77,f619,f362])).
% 2.75/0.76  fof(f613,plain,(
% 2.75/0.76    ( ! [X33,X34] : (~r1_tarski(X33,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X33) | v5_relat_1(X34,u1_struct_0(sK2)) | ~v1_relat_1(X34) | ~r1_tarski(k2_relat_1(X34),sK3)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f343,f213])).
% 2.75/0.76  fof(f622,plain,(
% 2.75/0.76    spl5_35 | spl5_53 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f612,f149,f77,f619,f354])).
% 2.75/0.76  fof(f612,plain,(
% 2.75/0.76    ( ! [X30,X31,X32] : (~r1_tarski(X30,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X30) | v5_relat_1(X31,u1_struct_0(sK2)) | ~v1_relat_1(X31) | ~r1_tarski(X32,sK3) | ~r1_tarski(k2_relat_1(X31),X32)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f343,f229])).
% 2.75/0.76  fof(f621,plain,(
% 2.75/0.76    spl5_52 | spl5_53 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f611,f149,f77,f619,f616])).
% 2.75/0.76  fof(f611,plain,(
% 2.75/0.76    ( ! [X28,X26,X29,X27] : (~r1_tarski(X26,sK4) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X26) | v5_relat_1(X27,u1_struct_0(sK2)) | ~v1_relat_1(X27) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,sK3) | ~r1_tarski(k2_relat_1(X27),X28)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f343,f277])).
% 2.75/0.76  fof(f602,plain,(
% 2.75/0.76    ~spl5_49 | spl5_51 | ~spl5_2),
% 2.75/0.76    inference(avatar_split_clause,[],[f589,f77,f600,f592])).
% 2.75/0.76  fof(f592,plain,(
% 2.75/0.76    spl5_49 <=> r1_tarski(u1_struct_0(sK2),sK4)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.75/0.76  fof(f600,plain,(
% 2.75/0.76    spl5_51 <=> ! [X32,X34,X31,X33] : (~r1_tarski(X31,sK4) | ~v1_relat_1(X34) | v5_relat_1(X34,u1_struct_0(sK2)) | ~r1_tarski(k2_relat_1(X34),X32) | ~r1_tarski(X32,X33) | ~r1_tarski(X33,X31))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.75/0.76  fof(f589,plain,(
% 2.75/0.76    ( ! [X33,X31,X34,X32] : (~r1_tarski(X31,sK4) | ~r1_tarski(X32,X33) | ~r1_tarski(X33,X31) | ~r1_tarski(k2_relat_1(X34),X32) | ~r1_tarski(u1_struct_0(sK2),sK4) | v5_relat_1(X34,u1_struct_0(sK2)) | ~v1_relat_1(X34)) ) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f341,f242])).
% 2.75/0.76  fof(f598,plain,(
% 2.75/0.76    ~spl5_49 | spl5_50 | ~spl5_2 | ~spl5_15),
% 2.75/0.76    inference(avatar_split_clause,[],[f588,f144,f77,f596,f592])).
% 2.75/0.76  fof(f596,plain,(
% 2.75/0.76    spl5_50 <=> ! [X27,X29,X28,X30] : (~r1_tarski(X27,sK4) | ~v1_relat_1(X30) | v5_relat_1(X30,u1_struct_0(sK1)) | ~r1_tarski(k2_relat_1(X30),X28) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,X27))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.75/0.76  fof(f588,plain,(
% 2.75/0.76    ( ! [X30,X28,X29,X27] : (~r1_tarski(X27,sK4) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,X27) | ~r1_tarski(k2_relat_1(X30),X28) | ~r1_tarski(u1_struct_0(sK2),sK4) | v5_relat_1(X30,u1_struct_0(sK1)) | ~v1_relat_1(X30)) ) | (~spl5_2 | ~spl5_15)),
% 2.75/0.76    inference(resolution,[],[f341,f247])).
% 2.75/0.76  fof(f561,plain,(
% 2.75/0.76    ~spl5_20 | spl5_25 | spl5_48 | ~spl5_23 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f546,f449,f206,f556,f261,f171])).
% 2.75/0.76  fof(f546,plain,(
% 2.75/0.76    ( ! [X29] : (~r1_tarski(u1_struct_0(sK0),X29) | ~r1_tarski(X29,sK3) | v1_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | (~spl5_23 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f462,f208])).
% 2.75/0.76  fof(f462,plain,(
% 2.75/0.76    ( ! [X28,X29,X27] : (~v5_relat_1(X27,X28) | ~r1_tarski(X28,X29) | ~r1_tarski(X29,sK3) | v1_relat_1(k2_relat_1(X27)) | ~v1_relat_1(X27)) ) | ~spl5_39),
% 2.75/0.76    inference(resolution,[],[f450,f61])).
% 2.75/0.76  fof(f560,plain,(
% 2.75/0.76    spl5_27 | spl5_48 | ~spl5_16 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f538,f449,f149,f556,f270])).
% 2.75/0.76  fof(f538,plain,(
% 2.75/0.76    ( ! [X8,X7] : (~r1_tarski(u1_struct_0(sK0),X7) | ~r1_tarski(X7,sK3) | v1_relat_1(k2_relat_1(X8)) | ~v1_relat_1(X8) | ~r1_tarski(X8,sK3)) ) | (~spl5_16 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f462,f227])).
% 2.75/0.76  fof(f559,plain,(
% 2.75/0.76    spl5_33 | spl5_48 | ~spl5_16 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f537,f449,f149,f556,f327])).
% 2.75/0.76  fof(f537,plain,(
% 2.75/0.76    ( ! [X6,X4,X5] : (~r1_tarski(u1_struct_0(sK0),X4) | ~r1_tarski(X4,sK3) | v1_relat_1(k2_relat_1(X5)) | ~v1_relat_1(X5) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,sK3)) ) | (~spl5_16 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f462,f275])).
% 2.75/0.76  fof(f558,plain,(
% 2.75/0.76    spl5_47 | spl5_48 | ~spl5_16 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f536,f449,f149,f556,f553])).
% 2.75/0.76  fof(f536,plain,(
% 2.75/0.76    ( ! [X2,X0,X3,X1] : (~r1_tarski(u1_struct_0(sK0),X0) | ~r1_tarski(X0,sK3) | v1_relat_1(k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X2,sK3) | ~r1_tarski(X1,X3) | ~r1_tarski(X3,X2)) ) | (~spl5_16 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f462,f436])).
% 2.75/0.76  fof(f524,plain,(
% 2.75/0.76    spl5_46 | ~spl5_38 | ~spl5_16 | ~spl5_40),
% 2.75/0.76    inference(avatar_split_clause,[],[f518,f472,f149,f445,f522])).
% 2.75/0.76  fof(f445,plain,(
% 2.75/0.76    spl5_38 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.75/0.76  fof(f518,plain,(
% 2.75/0.76    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK3) | ~r1_tarski(u1_struct_0(sK2),X6)) ) | (~spl5_16 | ~spl5_40)),
% 2.75/0.76    inference(resolution,[],[f473,f277])).
% 2.75/0.76  fof(f511,plain,(
% 2.75/0.76    ~spl5_18 | spl5_45 | ~spl5_30),
% 2.75/0.76    inference(avatar_split_clause,[],[f498,f301,f509,f162])).
% 2.75/0.76  fof(f509,plain,(
% 2.75/0.76    spl5_45 <=> ! [X9,X11,X10] : (~r1_tarski(X9,k1_relat_1(k7_relat_1(X10,k7_relat_1(sK4,X11)))) | ~v1_relat_1(X10) | v1_relat_1(X9))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.75/0.76  fof(f498,plain,(
% 2.75/0.76    ( ! [X10,X11,X9] : (~r1_tarski(X9,k1_relat_1(k7_relat_1(X10,k7_relat_1(sK4,X11)))) | v1_relat_1(X9) | ~v1_relat_1(sK4) | ~v1_relat_1(X10)) ) | ~spl5_30),
% 2.75/0.76    inference(resolution,[],[f302,f252])).
% 2.75/0.76  fof(f302,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~r1_tarski(X1,sK4) | ~r1_tarski(X0,X1) | v1_relat_1(X0)) ) | ~spl5_30),
% 2.75/0.76    inference(avatar_component_clause,[],[f301])).
% 2.75/0.76  fof(f507,plain,(
% 2.75/0.76    ~spl5_18 | spl5_44 | ~spl5_30),
% 2.75/0.76    inference(avatar_split_clause,[],[f496,f301,f505,f162])).
% 2.75/0.76  fof(f505,plain,(
% 2.75/0.76    spl5_44 <=> ! [X5,X4,X6] : (~r1_tarski(X4,k7_relat_1(k7_relat_1(sK4,X5),X6)) | ~v1_relat_1(k7_relat_1(sK4,X5)) | v1_relat_1(X4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 2.75/0.76  fof(f496,plain,(
% 2.75/0.76    ( ! [X6,X4,X5] : (~r1_tarski(X4,k7_relat_1(k7_relat_1(sK4,X5),X6)) | v1_relat_1(X4) | ~v1_relat_1(sK4) | ~v1_relat_1(k7_relat_1(sK4,X5))) ) | ~spl5_30),
% 2.75/0.76    inference(resolution,[],[f302,f251])).
% 2.75/0.76  fof(f503,plain,(
% 2.75/0.76    ~spl5_18 | spl5_43 | ~spl5_30),
% 2.75/0.76    inference(avatar_split_clause,[],[f495,f301,f501,f162])).
% 2.75/0.76  fof(f501,plain,(
% 2.75/0.76    spl5_43 <=> ! [X3,X2] : (~r1_tarski(X2,k7_relat_1(sK4,X3)) | v1_relat_1(X2))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.75/0.76  fof(f495,plain,(
% 2.75/0.76    ( ! [X2,X3] : (~r1_tarski(X2,k7_relat_1(sK4,X3)) | v1_relat_1(X2) | ~v1_relat_1(sK4)) ) | ~spl5_30),
% 2.75/0.76    inference(resolution,[],[f302,f59])).
% 2.75/0.76  fof(f487,plain,(
% 2.75/0.76    spl5_42 | spl5_18 | ~spl5_15 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f470,f449,f144,f162,f481])).
% 2.75/0.76  fof(f470,plain,(
% 2.75/0.76    ( ! [X50] : (v1_relat_1(sK4) | ~r1_tarski(u1_struct_0(sK1),X50) | ~r1_tarski(X50,sK3)) ) | (~spl5_15 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f146])).
% 2.75/0.76  fof(f486,plain,(
% 2.75/0.76    spl5_40 | spl5_18 | ~spl5_2 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f469,f449,f77,f162,f472])).
% 2.75/0.76  fof(f469,plain,(
% 2.75/0.76    ( ! [X49] : (v1_relat_1(sK4) | ~r1_tarski(u1_struct_0(sK2),X49) | ~r1_tarski(X49,sK3)) ) | (~spl5_2 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f79])).
% 2.75/0.76  fof(f485,plain,(
% 2.75/0.76    spl5_42 | spl5_31 | ~spl5_15 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f458,f449,f144,f305,f481])).
% 2.75/0.76  fof(f458,plain,(
% 2.75/0.76    ( ! [X17,X16] : (v1_relat_1(X16) | ~r1_tarski(u1_struct_0(sK1),X17) | ~r1_tarski(X17,sK3) | ~r1_tarski(X16,sK4)) ) | (~spl5_15 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f215])).
% 2.75/0.76  fof(f484,plain,(
% 2.75/0.76    spl5_42 | spl5_30 | ~spl5_15 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f457,f449,f144,f301,f481])).
% 2.75/0.76  fof(f457,plain,(
% 2.75/0.76    ( ! [X14,X15,X13] : (v1_relat_1(X13) | ~r1_tarski(u1_struct_0(sK1),X14) | ~r1_tarski(X14,sK3) | ~r1_tarski(X15,sK4) | ~r1_tarski(X13,X15)) ) | (~spl5_15 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f219])).
% 2.75/0.76  fof(f483,plain,(
% 2.75/0.76    spl5_42 | spl5_41 | ~spl5_15 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f456,f449,f144,f475,f481])).
% 2.75/0.76  fof(f456,plain,(
% 2.75/0.76    ( ! [X12,X10,X11,X9] : (v1_relat_1(X9) | ~r1_tarski(u1_struct_0(sK1),X10) | ~r1_tarski(X10,sK3) | ~r1_tarski(X11,X12) | ~r1_tarski(X12,sK4) | ~r1_tarski(X9,X11)) ) | (~spl5_15 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f245])).
% 2.75/0.76  fof(f479,plain,(
% 2.75/0.76    spl5_40 | spl5_31 | ~spl5_2 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f455,f449,f77,f305,f472])).
% 2.75/0.76  fof(f455,plain,(
% 2.75/0.76    ( ! [X8,X7] : (v1_relat_1(X7) | ~r1_tarski(u1_struct_0(sK2),X8) | ~r1_tarski(X8,sK3) | ~r1_tarski(X7,sK4)) ) | (~spl5_2 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f214])).
% 2.75/0.76  fof(f478,plain,(
% 2.75/0.76    spl5_40 | spl5_30 | ~spl5_2 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f454,f449,f77,f301,f472])).
% 2.75/0.76  fof(f454,plain,(
% 2.75/0.76    ( ! [X6,X4,X5] : (v1_relat_1(X4) | ~r1_tarski(u1_struct_0(sK2),X5) | ~r1_tarski(X5,sK3) | ~r1_tarski(X6,sK4) | ~r1_tarski(X4,X6)) ) | (~spl5_2 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f216])).
% 2.75/0.76  fof(f477,plain,(
% 2.75/0.76    spl5_40 | spl5_41 | ~spl5_2 | ~spl5_39),
% 2.75/0.76    inference(avatar_split_clause,[],[f453,f449,f77,f475,f472])).
% 2.75/0.76  fof(f453,plain,(
% 2.75/0.76    ( ! [X2,X0,X3,X1] : (v1_relat_1(X0) | ~r1_tarski(u1_struct_0(sK2),X1) | ~r1_tarski(X1,sK3) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,sK4) | ~r1_tarski(X0,X2)) ) | (~spl5_2 | ~spl5_39)),
% 2.75/0.76    inference(resolution,[],[f450,f240])).
% 2.75/0.76  fof(f452,plain,(
% 2.75/0.76    ~spl5_19 | spl5_39 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f440,f149,f449,f167])).
% 2.75/0.76  fof(f440,plain,(
% 2.75/0.76    ( ! [X14,X15,X13] : (~r1_tarski(X13,X14) | ~r1_tarski(X14,sK3) | ~r1_tarski(X15,X13) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(X15)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f277,f156])).
% 2.75/0.76  fof(f451,plain,(
% 2.75/0.76    ~spl5_38 | spl5_39 | ~spl5_16 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f438,f281,f149,f449,f445])).
% 2.75/0.76  fof(f438,plain,(
% 2.75/0.76    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | ~r1_tarski(X7,sK3) | ~r1_tarski(X8,X6) | v1_relat_1(X8) | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3)) ) | (~spl5_16 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f277,f282])).
% 2.75/0.76  fof(f364,plain,(
% 2.75/0.76    spl5_37 | ~spl5_36 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f351,f149,f77,f357,f362])).
% 2.75/0.76  fof(f357,plain,(
% 2.75/0.76    spl5_36 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.75/0.76  fof(f351,plain,(
% 2.75/0.76    ( ! [X13] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4) | v5_relat_1(X13,u1_struct_0(sK2)) | ~v1_relat_1(X13) | ~r1_tarski(k2_relat_1(X13),sK3)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f242,f213])).
% 2.75/0.76  fof(f360,plain,(
% 2.75/0.76    spl5_35 | ~spl5_36 | ~spl5_2 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f350,f149,f77,f357,f354])).
% 2.75/0.76  fof(f350,plain,(
% 2.75/0.76    ( ! [X12,X11] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4) | v5_relat_1(X11,u1_struct_0(sK2)) | ~v1_relat_1(X11) | ~r1_tarski(X12,sK3) | ~r1_tarski(k2_relat_1(X11),X12)) ) | (~spl5_2 | ~spl5_16)),
% 2.75/0.76    inference(resolution,[],[f242,f229])).
% 2.75/0.76  fof(f335,plain,(
% 2.75/0.76    ~spl5_20 | spl5_25 | ~spl5_34 | ~spl5_23 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f323,f281,f206,f330,f261,f171])).
% 2.75/0.76  fof(f330,plain,(
% 2.75/0.76    spl5_34 <=> r1_tarski(u1_struct_0(sK0),sK3)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 2.75/0.76  fof(f323,plain,(
% 2.75/0.76    ~r1_tarski(u1_struct_0(sK0),sK3) | v1_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl5_23 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f290,f208])).
% 2.75/0.76  fof(f290,plain,(
% 2.75/0.76    ( ! [X10,X9] : (~v5_relat_1(X9,X10) | ~r1_tarski(X10,sK3) | v1_relat_1(k2_relat_1(X9)) | ~v1_relat_1(X9)) ) | ~spl5_28),
% 2.75/0.76    inference(resolution,[],[f282,f61])).
% 2.75/0.76  fof(f334,plain,(
% 2.75/0.76    spl5_27 | ~spl5_34 | ~spl5_16 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f318,f281,f149,f330,f270])).
% 2.75/0.76  fof(f318,plain,(
% 2.75/0.76    ( ! [X2] : (~r1_tarski(u1_struct_0(sK0),sK3) | v1_relat_1(k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r1_tarski(X2,sK3)) ) | (~spl5_16 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f290,f227])).
% 2.75/0.76  fof(f333,plain,(
% 2.75/0.76    spl5_33 | ~spl5_34 | ~spl5_16 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f317,f281,f149,f330,f327])).
% 2.75/0.76  fof(f317,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK0),sK3) | v1_relat_1(k2_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,sK3)) ) | (~spl5_16 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f290,f275])).
% 2.75/0.76  fof(f315,plain,(
% 2.75/0.76    ~spl5_32 | spl5_18 | ~spl5_15 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f295,f281,f144,f162,f309])).
% 2.75/0.76  fof(f309,plain,(
% 2.75/0.76    spl5_32 <=> r1_tarski(u1_struct_0(sK1),sK3)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.75/0.76  fof(f295,plain,(
% 2.75/0.76    v1_relat_1(sK4) | ~r1_tarski(u1_struct_0(sK1),sK3) | (~spl5_15 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f146])).
% 2.75/0.76  fof(f314,plain,(
% 2.75/0.76    ~spl5_29 | spl5_18 | ~spl5_2 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f294,f281,f77,f162,f297])).
% 2.75/0.76  fof(f297,plain,(
% 2.75/0.76    spl5_29 <=> r1_tarski(u1_struct_0(sK2),sK3)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.75/0.76  fof(f294,plain,(
% 2.75/0.76    v1_relat_1(sK4) | ~r1_tarski(u1_struct_0(sK2),sK3) | (~spl5_2 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f79])).
% 2.75/0.76  fof(f313,plain,(
% 2.75/0.76    ~spl5_32 | spl5_31 | ~spl5_15 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f287,f281,f144,f305,f309])).
% 2.75/0.76  fof(f287,plain,(
% 2.75/0.76    ( ! [X5] : (v1_relat_1(X5) | ~r1_tarski(u1_struct_0(sK1),sK3) | ~r1_tarski(X5,sK4)) ) | (~spl5_15 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f215])).
% 2.75/0.76  fof(f312,plain,(
% 2.75/0.76    ~spl5_32 | spl5_30 | ~spl5_15 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f286,f281,f144,f301,f309])).
% 2.75/0.76  fof(f286,plain,(
% 2.75/0.76    ( ! [X4,X3] : (v1_relat_1(X3) | ~r1_tarski(u1_struct_0(sK1),sK3) | ~r1_tarski(X4,sK4) | ~r1_tarski(X3,X4)) ) | (~spl5_15 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f219])).
% 2.75/0.76  fof(f307,plain,(
% 2.75/0.76    ~spl5_29 | spl5_31 | ~spl5_2 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f285,f281,f77,f305,f297])).
% 2.75/0.76  fof(f285,plain,(
% 2.75/0.76    ( ! [X2] : (v1_relat_1(X2) | ~r1_tarski(u1_struct_0(sK2),sK3) | ~r1_tarski(X2,sK4)) ) | (~spl5_2 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f214])).
% 2.75/0.76  fof(f303,plain,(
% 2.75/0.76    ~spl5_29 | spl5_30 | ~spl5_2 | ~spl5_28),
% 2.75/0.76    inference(avatar_split_clause,[],[f284,f281,f77,f301,f297])).
% 2.75/0.76  fof(f284,plain,(
% 2.75/0.76    ( ! [X0,X1] : (v1_relat_1(X0) | ~r1_tarski(u1_struct_0(sK2),sK3) | ~r1_tarski(X1,sK4) | ~r1_tarski(X0,X1)) ) | (~spl5_2 | ~spl5_28)),
% 2.75/0.76    inference(resolution,[],[f282,f216])).
% 2.75/0.76  fof(f283,plain,(
% 2.75/0.76    ~spl5_19 | spl5_28 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f278,f149,f281,f167])).
% 2.75/0.76  fof(f278,plain,(
% 2.75/0.76    ( ! [X8,X7] : (~r1_tarski(X7,sK3) | ~r1_tarski(X8,X7) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(X8)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f229,f156])).
% 2.75/0.76  fof(f272,plain,(
% 2.75/0.76    ~spl5_26 | spl5_27 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f255,f149,f270,f265])).
% 2.75/0.76  fof(f265,plain,(
% 2.75/0.76    spl5_26 <=> v1_relat_1(u1_struct_0(sK0))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.75/0.76  fof(f255,plain,(
% 2.75/0.76    ( ! [X3] : (~v1_relat_1(X3) | ~v1_relat_1(u1_struct_0(sK0)) | v1_relat_1(k2_relat_1(X3)) | ~r1_tarski(X3,sK3)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f188,f227])).
% 2.75/0.76  fof(f188,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~v5_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k2_relat_1(X0))) )),
% 2.75/0.76    inference(resolution,[],[f61,f156])).
% 2.75/0.76  fof(f268,plain,(
% 2.75/0.76    spl5_25 | ~spl5_26 | ~spl5_20 | ~spl5_23),
% 2.75/0.76    inference(avatar_split_clause,[],[f253,f206,f171,f265,f261])).
% 2.75/0.76  fof(f253,plain,(
% 2.75/0.76    ~v1_relat_1(sK3) | ~v1_relat_1(u1_struct_0(sK0)) | v1_relat_1(k2_relat_1(sK3)) | ~spl5_23),
% 2.75/0.76    inference(resolution,[],[f188,f208])).
% 2.75/0.76  fof(f235,plain,(
% 2.75/0.76    ~spl5_19 | spl5_24 | ~spl5_16),
% 2.75/0.76    inference(avatar_split_clause,[],[f230,f149,f233,f167])).
% 2.75/0.76  fof(f233,plain,(
% 2.75/0.76    spl5_24 <=> ! [X4] : (~r1_tarski(X4,sK3) | v1_relat_1(X4))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.75/0.76  fof(f230,plain,(
% 2.75/0.76    ( ! [X4] : (~r1_tarski(X4,sK3) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(X4)) ) | ~spl5_16),
% 2.75/0.76    inference(resolution,[],[f213,f156])).
% 2.75/0.76  fof(f209,plain,(
% 2.75/0.76    spl5_23 | ~spl5_4),
% 2.75/0.76    inference(avatar_split_clause,[],[f203,f87,f206])).
% 2.75/0.76  fof(f203,plain,(
% 2.75/0.76    v5_relat_1(sK3,u1_struct_0(sK0)) | ~spl5_4),
% 2.75/0.76    inference(resolution,[],[f67,f89])).
% 2.75/0.76  fof(f89,plain,(
% 2.75/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_4),
% 2.75/0.76    inference(avatar_component_clause,[],[f87])).
% 2.75/0.76  fof(f197,plain,(
% 2.75/0.76    spl5_22 | ~spl5_4),
% 2.75/0.76    inference(avatar_split_clause,[],[f191,f87,f194])).
% 2.75/0.76  fof(f194,plain,(
% 2.75/0.76    spl5_22 <=> v4_relat_1(sK3,u1_struct_0(sK1))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.75/0.76  fof(f191,plain,(
% 2.75/0.76    v4_relat_1(sK3,u1_struct_0(sK1)) | ~spl5_4),
% 2.75/0.76    inference(resolution,[],[f66,f89])).
% 2.75/0.76  fof(f186,plain,(
% 2.75/0.76    spl5_18 | ~spl5_21 | ~spl5_2),
% 2.75/0.76    inference(avatar_split_clause,[],[f177,f77,f183,f162])).
% 2.75/0.76  fof(f183,plain,(
% 2.75/0.76    spl5_21 <=> v1_relat_1(u1_struct_0(sK2))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.75/0.76  fof(f177,plain,(
% 2.75/0.76    ~v1_relat_1(u1_struct_0(sK2)) | v1_relat_1(sK4) | ~spl5_2),
% 2.75/0.76    inference(resolution,[],[f156,f79])).
% 2.75/0.76  fof(f176,plain,(
% 2.75/0.76    spl5_19),
% 2.75/0.76    inference(avatar_contradiction_clause,[],[f175])).
% 2.75/0.76  fof(f175,plain,(
% 2.75/0.76    $false | spl5_19),
% 2.75/0.76    inference(resolution,[],[f169,f58])).
% 2.75/0.76  fof(f169,plain,(
% 2.75/0.76    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | spl5_19),
% 2.75/0.76    inference(avatar_component_clause,[],[f167])).
% 2.75/0.76  fof(f174,plain,(
% 2.75/0.76    ~spl5_19 | spl5_20 | ~spl5_4),
% 2.75/0.76    inference(avatar_split_clause,[],[f155,f87,f171,f167])).
% 2.75/0.76  fof(f155,plain,(
% 2.75/0.76    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~spl5_4),
% 2.75/0.76    inference(resolution,[],[f55,f89])).
% 2.75/0.76  fof(f165,plain,(
% 2.75/0.76    ~spl5_17 | spl5_18 | ~spl5_3),
% 2.75/0.76    inference(avatar_split_clause,[],[f154,f82,f162,f158])).
% 2.75/0.76  fof(f158,plain,(
% 2.75/0.76    spl5_17 <=> v1_relat_1(u1_struct_0(sK1))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.75/0.76  fof(f82,plain,(
% 2.75/0.76    spl5_3 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.75/0.76  fof(f154,plain,(
% 2.75/0.76    v1_relat_1(sK4) | ~v1_relat_1(u1_struct_0(sK1)) | ~spl5_3),
% 2.75/0.76    inference(resolution,[],[f55,f84])).
% 2.75/0.76  fof(f84,plain,(
% 2.75/0.76    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_3),
% 2.75/0.76    inference(avatar_component_clause,[],[f82])).
% 2.75/0.76  fof(f152,plain,(
% 2.75/0.76    spl5_16 | ~spl5_4),
% 2.75/0.76    inference(avatar_split_clause,[],[f142,f87,f149])).
% 2.75/0.76  fof(f142,plain,(
% 2.75/0.76    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~spl5_4),
% 2.75/0.76    inference(resolution,[],[f63,f89])).
% 2.75/0.76  fof(f147,plain,(
% 2.75/0.76    spl5_15 | ~spl5_3),
% 2.75/0.76    inference(avatar_split_clause,[],[f141,f82,f144])).
% 2.75/0.76  fof(f141,plain,(
% 2.75/0.76    r1_tarski(sK4,u1_struct_0(sK1)) | ~spl5_3),
% 2.75/0.76    inference(resolution,[],[f63,f84])).
% 2.75/0.76  fof(f140,plain,(
% 2.75/0.76    ~spl5_14),
% 2.75/0.76    inference(avatar_split_clause,[],[f41,f137])).
% 2.75/0.76  fof(f41,plain,(
% 2.75/0.76    ~v2_struct_0(sK0)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f38,plain,(
% 2.75/0.76    ((((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.75/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f37,f36,f35,f34,f33])).
% 2.75/0.76  fof(f33,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f34,plain,(
% 2.75/0.76    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f35,plain,(
% 2.75/0.76    ? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f36,plain,(
% 2.75/0.76    ? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f37,plain,(
% 2.75/0.76    ? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f17,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.75/0.76    inference(flattening,[],[f16])).
% 2.75/0.76  fof(f16,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.75/0.76    inference(ennf_transformation,[],[f15])).
% 2.75/0.76  fof(f15,negated_conjecture,(
% 2.75/0.76    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.75/0.76    inference(negated_conjecture,[],[f14])).
% 2.75/0.76  fof(f14,conjecture,(
% 2.75/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).
% 2.75/0.76  fof(f135,plain,(
% 2.75/0.76    spl5_13),
% 2.75/0.76    inference(avatar_split_clause,[],[f42,f132])).
% 2.75/0.76  fof(f42,plain,(
% 2.75/0.76    v2_pre_topc(sK0)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f130,plain,(
% 2.75/0.76    spl5_12),
% 2.75/0.76    inference(avatar_split_clause,[],[f43,f127])).
% 2.75/0.76  fof(f43,plain,(
% 2.75/0.76    l1_pre_topc(sK0)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f125,plain,(
% 2.75/0.76    ~spl5_11),
% 2.75/0.76    inference(avatar_split_clause,[],[f44,f122])).
% 2.75/0.76  fof(f44,plain,(
% 2.75/0.76    ~v2_struct_0(sK1)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f120,plain,(
% 2.75/0.76    spl5_10),
% 2.75/0.76    inference(avatar_split_clause,[],[f45,f117])).
% 2.75/0.76  fof(f45,plain,(
% 2.75/0.76    v2_pre_topc(sK1)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f115,plain,(
% 2.75/0.76    spl5_9),
% 2.75/0.76    inference(avatar_split_clause,[],[f46,f112])).
% 2.75/0.76  fof(f46,plain,(
% 2.75/0.76    l1_pre_topc(sK1)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f110,plain,(
% 2.75/0.76    ~spl5_8),
% 2.75/0.76    inference(avatar_split_clause,[],[f47,f107])).
% 2.75/0.76  fof(f107,plain,(
% 2.75/0.76    spl5_8 <=> v2_struct_0(sK2)),
% 2.75/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.75/0.76  fof(f47,plain,(
% 2.75/0.76    ~v2_struct_0(sK2)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f105,plain,(
% 2.75/0.76    spl5_7),
% 2.75/0.76    inference(avatar_split_clause,[],[f48,f102])).
% 2.75/0.76  fof(f48,plain,(
% 2.75/0.76    m1_pre_topc(sK2,sK1)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f100,plain,(
% 2.75/0.76    spl5_6),
% 2.75/0.76    inference(avatar_split_clause,[],[f49,f97])).
% 2.75/0.76  fof(f49,plain,(
% 2.75/0.76    v1_funct_1(sK3)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f95,plain,(
% 2.75/0.76    spl5_5),
% 2.75/0.76    inference(avatar_split_clause,[],[f50,f92])).
% 2.75/0.76  fof(f50,plain,(
% 2.75/0.76    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f90,plain,(
% 2.75/0.76    spl5_4),
% 2.75/0.76    inference(avatar_split_clause,[],[f51,f87])).
% 2.75/0.76  fof(f51,plain,(
% 2.75/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f85,plain,(
% 2.75/0.76    spl5_3),
% 2.75/0.76    inference(avatar_split_clause,[],[f52,f82])).
% 2.75/0.76  fof(f52,plain,(
% 2.75/0.76    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f80,plain,(
% 2.75/0.76    spl5_2),
% 2.75/0.76    inference(avatar_split_clause,[],[f53,f77])).
% 2.75/0.76  fof(f53,plain,(
% 2.75/0.76    r1_tarski(sK4,u1_struct_0(sK2))),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  fof(f75,plain,(
% 2.75/0.76    ~spl5_1),
% 2.75/0.76    inference(avatar_split_clause,[],[f54,f72])).
% 2.75/0.76  fof(f54,plain,(
% 2.75/0.76    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 2.75/0.76    inference(cnf_transformation,[],[f38])).
% 2.75/0.76  % SZS output end Proof for theBenchmark
% 2.75/0.76  % (24246)------------------------------
% 2.75/0.76  % (24246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.76  % (24246)Termination reason: Refutation
% 2.75/0.76  
% 2.75/0.76  % (24246)Memory used [KB]: 8187
% 2.75/0.76  % (24246)Time elapsed: 0.344 s
% 2.75/0.76  % (24246)------------------------------
% 2.75/0.76  % (24246)------------------------------
% 2.75/0.76  % (24241)Success in time 0.397 s
%------------------------------------------------------------------------------
