%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t29_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:30 EDT 2019

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       : 1362 (4794 expanded)
%              Number of leaves         :  358 (1951 expanded)
%              Depth                    :   13
%              Number of atoms          : 3408 (12323 expanded)
%              Number of equality atoms :   42 ( 207 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8529,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f355,f362,f369,f376,f383,f390,f397,f404,f411,f418,f425,f432,f439,f446,f453,f460,f467,f474,f481,f488,f495,f502,f509,f516,f523,f530,f537,f544,f551,f562,f569,f577,f590,f602,f615,f627,f641,f649,f663,f671,f713,f720,f762,f772,f779,f789,f799,f809,f854,f862,f883,f891,f899,f919,f927,f974,f982,f989,f997,f1005,f1013,f1060,f1067,f1098,f1109,f1122,f1130,f1137,f1163,f1171,f1178,f1186,f1194,f1205,f1213,f1250,f1258,f1277,f1285,f1321,f1333,f1344,f1364,f1366,f1374,f1381,f1388,f1401,f1409,f1428,f1436,f1472,f1484,f1494,f1514,f1523,f1544,f1552,f1560,f1573,f1619,f1620,f1621,f1622,f1623,f1624,f1625,f1626,f1627,f1628,f1629,f1630,f1631,f1632,f1633,f1634,f1635,f1636,f1637,f1638,f1639,f1640,f1641,f1642,f1643,f1644,f1645,f1646,f1647,f1648,f1649,f1650,f1651,f1652,f1653,f1654,f1655,f1656,f1657,f1658,f1659,f1660,f1671,f1691,f1699,f1735,f1743,f1751,f1780,f1788,f1802,f1810,f1836,f1844,f1851,f1859,f1867,f1875,f1883,f1891,f1948,f1956,f1992,f2000,f2008,f2016,f2030,f2039,f2106,f2115,f2124,f2133,f2142,f2151,f2170,f2181,f2190,f2199,f2221,f2229,f2236,f2244,f2312,f2320,f2327,f2335,f2380,f2388,f2395,f2403,f2486,f2495,f2502,f2510,f2555,f2564,f2571,f2586,f2629,f2638,f2668,f2676,f2919,f2957,f2992,f3000,f3041,f3340,f3384,f3393,f3402,f3429,f3438,f3447,f3456,f3465,f3474,f3483,f3492,f3501,f3574,f3583,f3592,f3601,f3610,f3619,f3634,f3643,f3698,f3707,f3730,f3739,f3748,f3757,f3766,f3775,f3784,f3793,f3854,f4197,f4206,f4215,f4385,f4395,f4512,f4522,f4591,f4601,f4700,f4710,f4779,f4789,f5222,f5231,f5257,f5266,f5368,f5376,f5440,f5449,f5886,f5895,f5965,f6043,f6089,f6138,f6146,f6273,f6323,f6331,f6403,f6484,f6583,f6591,f6777,f6785,f6849,f6857,f6992,f7000,f7078,f7086,f7161,f7169,f7279,f7287,f7352,f7360,f7425,f7435,f7525,f7533,f7608,f7616,f7862,f7870,f7947,f7955,f8131,f8139,f8216,f8224,f8303,f8320,f8361,f8369,f8446,f8454,f8526])).

fof(f8526,plain,
    ( ~ spl26_0
    | ~ spl26_54
    | ~ spl26_64
    | spl26_357 ),
    inference(avatar_contradiction_clause,[],[f8520])).

fof(f8520,plain,
    ( $false
    | ~ spl26_0
    | ~ spl26_54
    | ~ spl26_64
    | ~ spl26_357 ),
    inference(resolution,[],[f8513,f3040])).

fof(f3040,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl26_357 ),
    inference(avatar_component_clause,[],[f3039])).

fof(f3039,plain,
    ( spl26_357
  <=> ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_357])])).

fof(f8513,plain,
    ( ! [X2] : v2_tex_2(k3_xboole_0(sK1,X2),sK0)
    | ~ spl26_0
    | ~ spl26_54
    | ~ spl26_64 ),
    inference(subsumption_resolution,[],[f8494,f3013])).

fof(f3013,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_54 ),
    inference(superposition,[],[f3003,f296])).

fof(f296,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',commutativity_k3_xboole_0)).

fof(f3003,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_54 ),
    inference(superposition,[],[f2271,f2746])).

fof(f2746,plain,
    ( ! [X8] : k9_subset_1(u1_struct_0(sK0),X8,sK1) = k3_xboole_0(X8,sK1)
    | ~ spl26_54 ),
    inference(resolution,[],[f307,f543])).

fof(f543,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_54 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl26_54
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_54])])).

fof(f307,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',redefinition_k9_subset_1)).

fof(f2271,plain,
    ( ! [X5] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X5,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_54 ),
    inference(resolution,[],[f306,f543])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',dt_k9_subset_1)).

fof(f8494,plain,
    ( ! [X2] :
        ( v2_tex_2(k3_xboole_0(sK1,X2),sK0)
        | ~ m1_subset_1(k3_xboole_0(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_54
    | ~ spl26_64 ),
    inference(resolution,[],[f8325,f295])).

fof(f295,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t17_xboole_1)).

fof(f8325,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_54
    | ~ spl26_64 ),
    inference(subsumption_resolution,[],[f8324,f354])).

fof(f354,plain,
    ( l1_pre_topc(sK0)
    | ~ spl26_0 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl26_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_0])])).

fof(f8324,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl26_54
    | ~ spl26_64 ),
    inference(subsumption_resolution,[],[f8323,f543])).

fof(f8323,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl26_64 ),
    inference(resolution,[],[f583,f244])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f78])).

fof(f78,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t28_tex_2)).

fof(f583,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl26_64 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl26_64
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_64])])).

fof(f8454,plain,
    ( spl26_554
    | ~ spl26_212 ),
    inference(avatar_split_clause,[],[f8432,f1571,f8452])).

fof(f8452,plain,
    ( spl26_554
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK8(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_554])])).

fof(f1571,plain,
    ( spl26_212
  <=> v1_relat_1(sK8(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_212])])).

fof(f8432,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK8(sK22))))
    | ~ spl26_212 ),
    inference(resolution,[],[f1664,f289])).

fof(f289,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f188])).

fof(f188,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',existence_m1_subset_1)).

fof(f1664,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_212 ),
    inference(resolution,[],[f1572,f250])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc2_relat_1)).

fof(f1572,plain,
    ( v1_relat_1(sK8(sK22))
    | ~ spl26_212 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f8446,plain,
    ( spl26_552
    | ~ spl26_212 ),
    inference(avatar_split_clause,[],[f8434,f1571,f8444])).

fof(f8444,plain,
    ( spl26_552
  <=> v1_relat_1(sK12(sK8(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_552])])).

fof(f8434,plain,
    ( v1_relat_1(sK12(sK8(sK22)))
    | ~ spl26_212 ),
    inference(resolution,[],[f1664,f292])).

fof(f292,plain,(
    ! [X0] : m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK12(X0),X0)
      & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f68,f192])).

fof(f192,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK12(X0),X0)
        & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc3_subset_1)).

fof(f8369,plain,
    ( spl26_550
    | ~ spl26_208 ),
    inference(avatar_split_clause,[],[f8347,f1558,f8367])).

fof(f8367,plain,
    ( spl26_550
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK6(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_550])])).

fof(f1558,plain,
    ( spl26_208
  <=> v1_relat_1(sK6(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_208])])).

fof(f8347,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK6(sK22))))
    | ~ spl26_208 ),
    inference(resolution,[],[f1663,f289])).

fof(f1663,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_208 ),
    inference(resolution,[],[f1559,f250])).

fof(f1559,plain,
    ( v1_relat_1(sK6(sK22))
    | ~ spl26_208 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f8361,plain,
    ( spl26_548
    | ~ spl26_208 ),
    inference(avatar_split_clause,[],[f8349,f1558,f8359])).

fof(f8359,plain,
    ( spl26_548
  <=> v1_relat_1(sK12(sK6(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_548])])).

fof(f8349,plain,
    ( v1_relat_1(sK12(sK6(sK22)))
    | ~ spl26_208 ),
    inference(resolution,[],[f1663,f292])).

fof(f8320,plain,
    ( ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66
    | spl26_357 ),
    inference(avatar_contradiction_clause,[],[f8314])).

fof(f8314,plain,
    ( $false
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66
    | ~ spl26_357 ),
    inference(resolution,[],[f8289,f3040])).

fof(f8289,plain,
    ( ! [X1] : v2_tex_2(k3_xboole_0(X1,sK2),sK0)
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(subsumption_resolution,[],[f8288,f3032])).

fof(f3032,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_56 ),
    inference(superposition,[],[f2272,f2747])).

fof(f2747,plain,
    ( ! [X9] : k9_subset_1(u1_struct_0(sK0),X9,sK2) = k3_xboole_0(X9,sK2)
    | ~ spl26_56 ),
    inference(resolution,[],[f307,f550])).

fof(f550,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_56 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl26_56
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_56])])).

fof(f2272,plain,
    ( ! [X6] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X6,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl26_56 ),
    inference(resolution,[],[f306,f550])).

fof(f8288,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k3_xboole_0(X1,sK2),sK0) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(forward_demodulation,[],[f8287,f5549])).

fof(f5549,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k3_xboole_0(X3,X2) ),
    inference(resolution,[],[f5540,f307])).

fof(f5540,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f5451,f1893])).

fof(f1893,plain,(
    ! [X4,X3] : k9_subset_1(X3,X4,X4) = X4 ),
    inference(resolution,[],[f305,f605])).

fof(f605,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f290,f591])).

fof(f591,plain,(
    ! [X0] : k1_xboole_0 = sK11(X0) ),
    inference(resolution,[],[f256,f291])).

fof(f291,plain,(
    ! [X0] : v1_xboole_0(sK11(X0)) ),
    inference(cnf_transformation,[],[f191])).

fof(f191,plain,(
    ! [X0] :
      ( v1_xboole_0(sK11(X0))
      & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f63,f190])).

fof(f190,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK11(X0))
        & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_subset_1)).

fof(f256,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f84])).

fof(f84,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t6_boole)).

fof(f290,plain,(
    ! [X0] : m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f191])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f163])).

fof(f163,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',idempotence_k9_subset_1)).

fof(f5451,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,X0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f2269,f607])).

fof(f607,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f295,f294])).

fof(f294,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',idempotence_k3_xboole_0)).

fof(f2269,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f306,f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t3_subset)).

fof(f8287,plain,
    ( ! [X1] :
        ( v2_tex_2(k3_xboole_0(X1,sK2),sK0)
        | ~ m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(forward_demodulation,[],[f8268,f5549])).

fof(f8268,plain,
    ( ! [X1] :
        ( v2_tex_2(k9_subset_1(sK2,X1,sK2),sK0)
        | ~ m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(resolution,[],[f3157,f5502])).

fof(f5502,plain,(
    ! [X14,X13] : r1_tarski(k9_subset_1(X13,X14,X13),X13) ),
    inference(resolution,[],[f5451,f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f3157,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(subsumption_resolution,[],[f3156,f354])).

fof(f3156,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(subsumption_resolution,[],[f3155,f550])).

fof(f3155,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl26_66 ),
    inference(resolution,[],[f244,f589])).

fof(f589,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl26_66 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl26_66
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_66])])).

fof(f8303,plain,
    ( spl26_546
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(avatar_split_clause,[],[f8286,f588,f549,f353,f8301])).

fof(f8301,plain,
    ( spl26_546
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_546])])).

fof(f8286,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(subsumption_resolution,[],[f8285,f605])).

fof(f8285,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(forward_demodulation,[],[f8284,f2758])).

fof(f2758,plain,(
    ! [X6,X7] : k9_subset_1(X6,X7,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f2745,f230])).

fof(f230,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t2_boole)).

fof(f2745,plain,(
    ! [X6,X7] : k9_subset_1(X6,X7,k1_xboole_0) = k3_xboole_0(X7,k1_xboole_0) ),
    inference(resolution,[],[f307,f605])).

fof(f8284,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_xboole_0,sK0)
        | ~ m1_subset_1(k9_subset_1(sK2,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(forward_demodulation,[],[f8267,f2758])).

fof(f8267,plain,
    ( ! [X0] :
        ( v2_tex_2(k9_subset_1(sK2,X0,k1_xboole_0),sK0)
        | ~ m1_subset_1(k9_subset_1(sK2,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl26_0
    | ~ spl26_56
    | ~ spl26_66 ),
    inference(resolution,[],[f3157,f2681])).

fof(f2681,plain,(
    ! [X8,X7] : r1_tarski(k9_subset_1(X7,X8,k1_xboole_0),X7) ),
    inference(resolution,[],[f2270,f301])).

fof(f2270,plain,(
    ! [X4,X3] : m1_subset_1(k9_subset_1(X3,X4,k1_xboole_0),k1_zfmisc_1(X3)) ),
    inference(resolution,[],[f306,f605])).

fof(f8224,plain,
    ( spl26_544
    | ~ spl26_204 ),
    inference(avatar_split_clause,[],[f8202,f1521,f8222])).

fof(f8222,plain,
    ( spl26_544
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_544])])).

fof(f1521,plain,
    ( spl26_204
  <=> v1_relat_1(sK5(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_204])])).

fof(f8202,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK22))))
    | ~ spl26_204 ),
    inference(resolution,[],[f1662,f289])).

fof(f1662,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_204 ),
    inference(resolution,[],[f1522,f250])).

fof(f1522,plain,
    ( v1_relat_1(sK5(sK22))
    | ~ spl26_204 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f8216,plain,
    ( spl26_542
    | ~ spl26_204 ),
    inference(avatar_split_clause,[],[f8204,f1521,f8214])).

fof(f8214,plain,
    ( spl26_542
  <=> v1_relat_1(sK12(sK5(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_542])])).

fof(f8204,plain,
    ( v1_relat_1(sK12(sK5(sK22)))
    | ~ spl26_204 ),
    inference(resolution,[],[f1662,f292])).

fof(f8139,plain,
    ( spl26_540
    | ~ spl26_182 ),
    inference(avatar_split_clause,[],[f8117,f1386,f8137])).

fof(f8137,plain,
    ( spl26_540
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK6(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_540])])).

fof(f1386,plain,
    ( spl26_182
  <=> v1_relat_1(sK6(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_182])])).

fof(f8117,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK6(sK21))))
    | ~ spl26_182 ),
    inference(resolution,[],[f1529,f289])).

fof(f1529,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK21)))
        | v1_relat_1(X0) )
    | ~ spl26_182 ),
    inference(resolution,[],[f1387,f250])).

fof(f1387,plain,
    ( v1_relat_1(sK6(sK21))
    | ~ spl26_182 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f8131,plain,
    ( spl26_538
    | ~ spl26_182 ),
    inference(avatar_split_clause,[],[f8119,f1386,f8129])).

fof(f8129,plain,
    ( spl26_538
  <=> v1_relat_1(sK12(sK6(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_538])])).

fof(f8119,plain,
    ( v1_relat_1(sK12(sK6(sK21)))
    | ~ spl26_182 ),
    inference(resolution,[],[f1529,f292])).

fof(f7955,plain,
    ( spl26_536
    | ~ spl26_180 ),
    inference(avatar_split_clause,[],[f7933,f1379,f7953])).

fof(f7953,plain,
    ( spl26_536
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_536])])).

fof(f1379,plain,
    ( spl26_180
  <=> v1_relat_1(sK5(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_180])])).

fof(f7933,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK21))))
    | ~ spl26_180 ),
    inference(resolution,[],[f1528,f289])).

fof(f1528,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK21)))
        | v1_relat_1(X0) )
    | ~ spl26_180 ),
    inference(resolution,[],[f1380,f250])).

fof(f1380,plain,
    ( v1_relat_1(sK5(sK21))
    | ~ spl26_180 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f7947,plain,
    ( spl26_534
    | ~ spl26_180 ),
    inference(avatar_split_clause,[],[f7935,f1379,f7945])).

fof(f7945,plain,
    ( spl26_534
  <=> v1_relat_1(sK12(sK5(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_534])])).

fof(f7935,plain,
    ( v1_relat_1(sK12(sK5(sK21)))
    | ~ spl26_180 ),
    inference(resolution,[],[f1528,f292])).

fof(f7870,plain,
    ( spl26_532
    | ~ spl26_174 ),
    inference(avatar_split_clause,[],[f7848,f1342,f7868])).

fof(f7868,plain,
    ( spl26_532
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_532])])).

fof(f1342,plain,
    ( spl26_174
  <=> v1_relat_1(sK4(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_174])])).

fof(f7848,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK21))))
    | ~ spl26_174 ),
    inference(resolution,[],[f1527,f289])).

fof(f1527,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK21)))
        | v1_relat_1(X0) )
    | ~ spl26_174 ),
    inference(resolution,[],[f1343,f250])).

fof(f1343,plain,
    ( v1_relat_1(sK4(sK21))
    | ~ spl26_174 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f7862,plain,
    ( spl26_530
    | ~ spl26_174 ),
    inference(avatar_split_clause,[],[f7850,f1342,f7860])).

fof(f7860,plain,
    ( spl26_530
  <=> v1_relat_1(sK12(sK4(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_530])])).

fof(f7850,plain,
    ( v1_relat_1(sK12(sK4(sK21)))
    | ~ spl26_174 ),
    inference(resolution,[],[f1527,f292])).

fof(f7616,plain,
    ( spl26_528
    | ~ spl26_170 ),
    inference(avatar_split_clause,[],[f7594,f1319,f7614])).

fof(f7614,plain,
    ( spl26_528
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_528])])).

fof(f1319,plain,
    ( spl26_170
  <=> v1_relat_1(sK3(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_170])])).

fof(f7594,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK21))))
    | ~ spl26_170 ),
    inference(resolution,[],[f1526,f289])).

fof(f1526,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK21)))
        | v1_relat_1(X0) )
    | ~ spl26_170 ),
    inference(resolution,[],[f1320,f250])).

fof(f1320,plain,
    ( v1_relat_1(sK3(sK21))
    | ~ spl26_170 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f7608,plain,
    ( spl26_526
    | ~ spl26_170 ),
    inference(avatar_split_clause,[],[f7596,f1319,f7606])).

fof(f7606,plain,
    ( spl26_526
  <=> v1_relat_1(sK12(sK3(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_526])])).

fof(f7596,plain,
    ( v1_relat_1(sK12(sK3(sK21)))
    | ~ spl26_170 ),
    inference(resolution,[],[f1526,f292])).

fof(f7533,plain,
    ( spl26_524
    | ~ spl26_200 ),
    inference(avatar_split_clause,[],[f7511,f1492,f7531])).

fof(f7531,plain,
    ( spl26_524
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_524])])).

fof(f1492,plain,
    ( spl26_200
  <=> v1_relat_1(sK4(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_200])])).

fof(f7511,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK22))))
    | ~ spl26_200 ),
    inference(resolution,[],[f1516,f289])).

fof(f1516,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_200 ),
    inference(resolution,[],[f1493,f250])).

fof(f1493,plain,
    ( v1_relat_1(sK4(sK22))
    | ~ spl26_200 ),
    inference(avatar_component_clause,[],[f1492])).

fof(f7525,plain,
    ( spl26_522
    | ~ spl26_200 ),
    inference(avatar_split_clause,[],[f7513,f1492,f7523])).

fof(f7523,plain,
    ( spl26_522
  <=> v1_relat_1(sK12(sK4(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_522])])).

fof(f7513,plain,
    ( v1_relat_1(sK12(sK4(sK22)))
    | ~ spl26_200 ),
    inference(resolution,[],[f1516,f292])).

fof(f7435,plain,
    ( spl26_520
    | ~ spl26_196 ),
    inference(avatar_split_clause,[],[f7411,f1470,f7433])).

fof(f7433,plain,
    ( spl26_520
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_520])])).

fof(f1470,plain,
    ( spl26_196
  <=> v1_relat_1(sK3(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_196])])).

fof(f7411,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK22))))
    | ~ spl26_196 ),
    inference(resolution,[],[f1515,f289])).

fof(f1515,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_196 ),
    inference(resolution,[],[f1471,f250])).

fof(f1471,plain,
    ( v1_relat_1(sK3(sK22))
    | ~ spl26_196 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f7425,plain,
    ( spl26_518
    | ~ spl26_196 ),
    inference(avatar_split_clause,[],[f7413,f1470,f7423])).

fof(f7423,plain,
    ( spl26_518
  <=> v1_relat_1(sK12(sK3(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_518])])).

fof(f7413,plain,
    ( v1_relat_1(sK12(sK3(sK22)))
    | ~ spl26_196 ),
    inference(resolution,[],[f1515,f292])).

fof(f7360,plain,
    ( spl26_516
    | ~ spl26_190 ),
    inference(avatar_split_clause,[],[f7338,f1426,f7358])).

fof(f7358,plain,
    ( spl26_516
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK22)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_516])])).

fof(f1426,plain,
    ( spl26_190
  <=> v1_relat_1(sK12(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_190])])).

fof(f7338,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK22))))
    | ~ spl26_190 ),
    inference(resolution,[],[f1429,f289])).

fof(f1429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK22)))
        | v1_relat_1(X0) )
    | ~ spl26_190 ),
    inference(resolution,[],[f1427,f250])).

fof(f1427,plain,
    ( v1_relat_1(sK12(sK22))
    | ~ spl26_190 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f7352,plain,
    ( spl26_514
    | ~ spl26_190 ),
    inference(avatar_split_clause,[],[f7340,f1426,f7350])).

fof(f7350,plain,
    ( spl26_514
  <=> v1_relat_1(sK12(sK12(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_514])])).

fof(f7340,plain,
    ( v1_relat_1(sK12(sK12(sK22)))
    | ~ spl26_190 ),
    inference(resolution,[],[f1429,f292])).

fof(f7287,plain,
    ( spl26_512
    | ~ spl26_164 ),
    inference(avatar_split_clause,[],[f7265,f1275,f7285])).

fof(f7285,plain,
    ( spl26_512
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_512])])).

fof(f1275,plain,
    ( spl26_164
  <=> v1_relat_1(sK12(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_164])])).

fof(f7265,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK21))))
    | ~ spl26_164 ),
    inference(resolution,[],[f1278,f289])).

fof(f1278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK21)))
        | v1_relat_1(X0) )
    | ~ spl26_164 ),
    inference(resolution,[],[f1276,f250])).

fof(f1276,plain,
    ( v1_relat_1(sK12(sK21))
    | ~ spl26_164 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f7279,plain,
    ( spl26_510
    | ~ spl26_164 ),
    inference(avatar_split_clause,[],[f7267,f1275,f7277])).

fof(f7277,plain,
    ( spl26_510
  <=> v1_relat_1(sK12(sK12(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_510])])).

fof(f7267,plain,
    ( v1_relat_1(sK12(sK12(sK21)))
    | ~ spl26_164 ),
    inference(resolution,[],[f1278,f292])).

fof(f7169,plain,
    ( spl26_508
    | ~ spl26_156 ),
    inference(avatar_split_clause,[],[f7147,f1211,f7167])).

fof(f7167,plain,
    ( spl26_508
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK6(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_508])])).

fof(f1211,plain,
    ( spl26_156
  <=> v1_relat_1(sK6(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_156])])).

fof(f7147,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK6(sK20))))
    | ~ spl26_156 ),
    inference(resolution,[],[f1214,f289])).

fof(f1214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK20)))
        | v1_relat_1(X0) )
    | ~ spl26_156 ),
    inference(resolution,[],[f1212,f250])).

fof(f1212,plain,
    ( v1_relat_1(sK6(sK20))
    | ~ spl26_156 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f7161,plain,
    ( spl26_506
    | ~ spl26_156 ),
    inference(avatar_split_clause,[],[f7149,f1211,f7159])).

fof(f7159,plain,
    ( spl26_506
  <=> v1_relat_1(sK12(sK6(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_506])])).

fof(f7149,plain,
    ( v1_relat_1(sK12(sK6(sK20)))
    | ~ spl26_156 ),
    inference(resolution,[],[f1214,f292])).

fof(f7086,plain,
    ( spl26_504
    | ~ spl26_152 ),
    inference(avatar_split_clause,[],[f7064,f1192,f7084])).

fof(f7084,plain,
    ( spl26_504
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_504])])).

fof(f1192,plain,
    ( spl26_152
  <=> v1_relat_1(sK5(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_152])])).

fof(f7064,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK20))))
    | ~ spl26_152 ),
    inference(resolution,[],[f1198,f289])).

fof(f1198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK20)))
        | v1_relat_1(X0) )
    | ~ spl26_152 ),
    inference(resolution,[],[f1193,f250])).

fof(f1193,plain,
    ( v1_relat_1(sK5(sK20))
    | ~ spl26_152 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f7078,plain,
    ( spl26_502
    | ~ spl26_152 ),
    inference(avatar_split_clause,[],[f7066,f1192,f7076])).

fof(f7076,plain,
    ( spl26_502
  <=> v1_relat_1(sK12(sK5(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_502])])).

fof(f7066,plain,
    ( v1_relat_1(sK12(sK5(sK20)))
    | ~ spl26_152 ),
    inference(resolution,[],[f1198,f292])).

fof(f7000,plain,
    ( spl26_500
    | ~ spl26_150 ),
    inference(avatar_split_clause,[],[f6917,f1184,f6998])).

fof(f6998,plain,
    ( spl26_500
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_500])])).

fof(f1184,plain,
    ( spl26_150
  <=> v1_relat_1(sK4(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_150])])).

fof(f6917,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK20))))
    | ~ spl26_150 ),
    inference(resolution,[],[f1187,f289])).

fof(f1187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK20)))
        | v1_relat_1(X0) )
    | ~ spl26_150 ),
    inference(resolution,[],[f1185,f250])).

fof(f1185,plain,
    ( v1_relat_1(sK4(sK20))
    | ~ spl26_150 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f6992,plain,
    ( spl26_498
    | ~ spl26_150 ),
    inference(avatar_split_clause,[],[f6919,f1184,f6990])).

fof(f6990,plain,
    ( spl26_498
  <=> v1_relat_1(sK12(sK4(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_498])])).

fof(f6919,plain,
    ( v1_relat_1(sK12(sK4(sK20)))
    | ~ spl26_150 ),
    inference(resolution,[],[f1187,f292])).

fof(f6857,plain,
    ( spl26_496
    | ~ spl26_148 ),
    inference(avatar_split_clause,[],[f6835,f1176,f6855])).

fof(f6855,plain,
    ( spl26_496
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_496])])).

fof(f1176,plain,
    ( spl26_148
  <=> v1_relat_1(sK3(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_148])])).

fof(f6835,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK20))))
    | ~ spl26_148 ),
    inference(resolution,[],[f1179,f289])).

fof(f1179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK20)))
        | v1_relat_1(X0) )
    | ~ spl26_148 ),
    inference(resolution,[],[f1177,f250])).

fof(f1177,plain,
    ( v1_relat_1(sK3(sK20))
    | ~ spl26_148 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f6849,plain,
    ( spl26_494
    | ~ spl26_148 ),
    inference(avatar_split_clause,[],[f6837,f1176,f6847])).

fof(f6847,plain,
    ( spl26_494
  <=> v1_relat_1(sK12(sK3(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_494])])).

fof(f6837,plain,
    ( v1_relat_1(sK12(sK3(sK20)))
    | ~ spl26_148 ),
    inference(resolution,[],[f1179,f292])).

fof(f6785,plain,
    ( spl26_492
    | ~ spl26_144 ),
    inference(avatar_split_clause,[],[f6763,f1161,f6783])).

fof(f6783,plain,
    ( spl26_492
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_492])])).

fof(f1161,plain,
    ( spl26_144
  <=> v1_relat_1(sK12(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_144])])).

fof(f6763,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK20))))
    | ~ spl26_144 ),
    inference(resolution,[],[f1164,f289])).

fof(f1164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK20)))
        | v1_relat_1(X0) )
    | ~ spl26_144 ),
    inference(resolution,[],[f1162,f250])).

fof(f1162,plain,
    ( v1_relat_1(sK12(sK20))
    | ~ spl26_144 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f6777,plain,
    ( spl26_490
    | ~ spl26_144 ),
    inference(avatar_split_clause,[],[f6765,f1161,f6775])).

fof(f6775,plain,
    ( spl26_490
  <=> v1_relat_1(sK12(sK12(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_490])])).

fof(f6765,plain,
    ( v1_relat_1(sK12(sK12(sK20)))
    | ~ spl26_144 ),
    inference(resolution,[],[f1164,f292])).

fof(f6591,plain,
    ( spl26_488
    | ~ spl26_126 ),
    inference(avatar_split_clause,[],[f6569,f1011,f6589])).

fof(f6589,plain,
    ( spl26_488
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK6(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_488])])).

fof(f1011,plain,
    ( spl26_126
  <=> v1_relat_1(sK6(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_126])])).

fof(f6569,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK6(sK19))))
    | ~ spl26_126 ),
    inference(resolution,[],[f1014,f289])).

fof(f1014,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK19)))
        | v1_relat_1(X0) )
    | ~ spl26_126 ),
    inference(resolution,[],[f1012,f250])).

fof(f1012,plain,
    ( v1_relat_1(sK6(sK19))
    | ~ spl26_126 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f6583,plain,
    ( spl26_486
    | ~ spl26_126 ),
    inference(avatar_split_clause,[],[f6571,f1011,f6581])).

fof(f6581,plain,
    ( spl26_486
  <=> v1_relat_1(sK12(sK6(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_486])])).

fof(f6571,plain,
    ( v1_relat_1(sK12(sK6(sK19)))
    | ~ spl26_126 ),
    inference(resolution,[],[f1014,f292])).

fof(f6484,plain,
    ( spl26_484
    | ~ spl26_124 ),
    inference(avatar_split_clause,[],[f6389,f1003,f6482])).

fof(f6482,plain,
    ( spl26_484
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_484])])).

fof(f1003,plain,
    ( spl26_124
  <=> v1_relat_1(sK5(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_124])])).

fof(f6389,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK19))))
    | ~ spl26_124 ),
    inference(resolution,[],[f1006,f289])).

fof(f1006,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK19)))
        | v1_relat_1(X0) )
    | ~ spl26_124 ),
    inference(resolution,[],[f1004,f250])).

fof(f1004,plain,
    ( v1_relat_1(sK5(sK19))
    | ~ spl26_124 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f6403,plain,
    ( spl26_482
    | ~ spl26_124 ),
    inference(avatar_split_clause,[],[f6391,f1003,f6401])).

fof(f6401,plain,
    ( spl26_482
  <=> v1_relat_1(sK12(sK5(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_482])])).

fof(f6391,plain,
    ( v1_relat_1(sK12(sK5(sK19)))
    | ~ spl26_124 ),
    inference(resolution,[],[f1006,f292])).

fof(f6331,plain,
    ( spl26_480
    | ~ spl26_122 ),
    inference(avatar_split_clause,[],[f6309,f995,f6329])).

fof(f6329,plain,
    ( spl26_480
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_480])])).

fof(f995,plain,
    ( spl26_122
  <=> v1_relat_1(sK4(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_122])])).

fof(f6309,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK19))))
    | ~ spl26_122 ),
    inference(resolution,[],[f998,f289])).

fof(f998,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK19)))
        | v1_relat_1(X0) )
    | ~ spl26_122 ),
    inference(resolution,[],[f996,f250])).

fof(f996,plain,
    ( v1_relat_1(sK4(sK19))
    | ~ spl26_122 ),
    inference(avatar_component_clause,[],[f995])).

fof(f6323,plain,
    ( spl26_478
    | ~ spl26_122 ),
    inference(avatar_split_clause,[],[f6311,f995,f6321])).

fof(f6321,plain,
    ( spl26_478
  <=> v1_relat_1(sK12(sK4(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_478])])).

fof(f6311,plain,
    ( v1_relat_1(sK12(sK4(sK19)))
    | ~ spl26_122 ),
    inference(resolution,[],[f998,f292])).

fof(f6273,plain,
    ( spl26_476
    | spl26_19
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f6265,f423,f416,f6271])).

fof(f6271,plain,
    ( spl26_476
  <=> v1_zfmisc_1(sK5(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_476])])).

fof(f416,plain,
    ( spl26_19
  <=> ~ v1_xboole_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_19])])).

fof(f423,plain,
    ( spl26_20
  <=> v1_zfmisc_1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_20])])).

fof(f6265,plain,
    ( v1_zfmisc_1(sK5(sK18))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(superposition,[],[f6234,f1893])).

fof(f6234,plain,
    ( ! [X42] : v1_zfmisc_1(k9_subset_1(sK18,X42,sK5(sK18)))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(subsumption_resolution,[],[f6206,f417])).

fof(f417,plain,
    ( ~ v1_xboole_0(sK18)
    | ~ spl26_19 ),
    inference(avatar_component_clause,[],[f416])).

fof(f6206,plain,
    ( ! [X42] :
        ( v1_xboole_0(sK18)
        | v1_zfmisc_1(k9_subset_1(sK18,X42,sK5(sK18))) )
    | ~ spl26_20 ),
    inference(resolution,[],[f2275,f755])).

fof(f755,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK18))
        | v1_zfmisc_1(X8) )
    | ~ spl26_20 ),
    inference(resolution,[],[f249,f424])).

fof(f424,plain,
    ( v1_zfmisc_1(sK18)
    | ~ spl26_20 ),
    inference(avatar_component_clause,[],[f423])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc5_funct_1)).

fof(f2275,plain,(
    ! [X12,X11] :
      ( m1_subset_1(k9_subset_1(X11,X12,sK5(X11)),k1_zfmisc_1(X11))
      | v1_xboole_0(X11) ) ),
    inference(resolution,[],[f306,f239])).

fof(f239,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f111,f178])).

fof(f178,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc3_realset1)).

fof(f6146,plain,
    ( spl26_474
    | ~ spl26_120 ),
    inference(avatar_split_clause,[],[f6124,f987,f6144])).

fof(f6144,plain,
    ( spl26_474
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_474])])).

fof(f987,plain,
    ( spl26_120
  <=> v1_relat_1(sK3(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_120])])).

fof(f6124,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK19))))
    | ~ spl26_120 ),
    inference(resolution,[],[f990,f289])).

fof(f990,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK19)))
        | v1_relat_1(X0) )
    | ~ spl26_120 ),
    inference(resolution,[],[f988,f250])).

fof(f988,plain,
    ( v1_relat_1(sK3(sK19))
    | ~ spl26_120 ),
    inference(avatar_component_clause,[],[f987])).

fof(f6138,plain,
    ( spl26_472
    | ~ spl26_120 ),
    inference(avatar_split_clause,[],[f6126,f987,f6136])).

fof(f6136,plain,
    ( spl26_472
  <=> v1_relat_1(sK12(sK3(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_472])])).

fof(f6126,plain,
    ( v1_relat_1(sK12(sK3(sK19)))
    | ~ spl26_120 ),
    inference(resolution,[],[f990,f292])).

fof(f6089,plain,
    ( spl26_470
    | spl26_19
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f6081,f423,f416,f6087])).

fof(f6087,plain,
    ( spl26_470
  <=> v1_zfmisc_1(sK4(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_470])])).

fof(f6081,plain,
    ( v1_zfmisc_1(sK4(sK18))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(superposition,[],[f6021,f1893])).

fof(f6021,plain,
    ( ! [X41] : v1_zfmisc_1(k9_subset_1(sK18,X41,sK4(sK18)))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(subsumption_resolution,[],[f5993,f417])).

fof(f5993,plain,
    ( ! [X41] :
        ( v1_xboole_0(sK18)
        | v1_zfmisc_1(k9_subset_1(sK18,X41,sK4(sK18))) )
    | ~ spl26_20 ),
    inference(resolution,[],[f2274,f755])).

fof(f2274,plain,(
    ! [X10,X9] :
      ( m1_subset_1(k9_subset_1(X9,X10,sK4(X9)),k1_zfmisc_1(X9))
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f306,f236])).

fof(f236,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f110,f176])).

fof(f176,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_tex_2)).

fof(f6043,plain,
    ( spl26_468
    | ~ spl26_116 ),
    inference(avatar_split_clause,[],[f5951,f972,f6041])).

fof(f6041,plain,
    ( spl26_468
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_468])])).

fof(f972,plain,
    ( spl26_116
  <=> v1_relat_1(sK12(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_116])])).

fof(f5951,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK19))))
    | ~ spl26_116 ),
    inference(resolution,[],[f975,f289])).

fof(f975,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK19)))
        | v1_relat_1(X0) )
    | ~ spl26_116 ),
    inference(resolution,[],[f973,f250])).

fof(f973,plain,
    ( v1_relat_1(sK12(sK19))
    | ~ spl26_116 ),
    inference(avatar_component_clause,[],[f972])).

fof(f5965,plain,
    ( spl26_466
    | ~ spl26_116 ),
    inference(avatar_split_clause,[],[f5953,f972,f5963])).

fof(f5963,plain,
    ( spl26_466
  <=> v1_relat_1(sK12(sK12(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_466])])).

fof(f5953,plain,
    ( v1_relat_1(sK12(sK12(sK19)))
    | ~ spl26_116 ),
    inference(resolution,[],[f975,f292])).

fof(f5895,plain,
    ( spl26_464
    | ~ spl26_114 ),
    inference(avatar_split_clause,[],[f5872,f925,f5893])).

fof(f5893,plain,
    ( spl26_464
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK6(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_464])])).

fof(f925,plain,
    ( spl26_114
  <=> v1_zfmisc_1(sK6(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_114])])).

fof(f5872,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK6(sK18))))
    | ~ spl26_114 ),
    inference(resolution,[],[f928,f289])).

fof(f928,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK18)))
        | v1_zfmisc_1(X0) )
    | ~ spl26_114 ),
    inference(resolution,[],[f926,f249])).

fof(f926,plain,
    ( v1_zfmisc_1(sK6(sK18))
    | ~ spl26_114 ),
    inference(avatar_component_clause,[],[f925])).

fof(f5886,plain,
    ( spl26_462
    | ~ spl26_114 ),
    inference(avatar_split_clause,[],[f5874,f925,f5884])).

fof(f5884,plain,
    ( spl26_462
  <=> v1_zfmisc_1(sK12(sK6(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_462])])).

fof(f5874,plain,
    ( v1_zfmisc_1(sK12(sK6(sK18)))
    | ~ spl26_114 ),
    inference(resolution,[],[f928,f292])).

fof(f5449,plain,
    ( spl26_460
    | ~ spl26_112 ),
    inference(avatar_split_clause,[],[f5427,f917,f5447])).

fof(f5447,plain,
    ( spl26_460
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK3(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_460])])).

fof(f917,plain,
    ( spl26_112
  <=> v1_zfmisc_1(sK3(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_112])])).

fof(f5427,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK3(sK18))))
    | ~ spl26_112 ),
    inference(resolution,[],[f920,f289])).

fof(f920,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK18)))
        | v1_zfmisc_1(X0) )
    | ~ spl26_112 ),
    inference(resolution,[],[f918,f249])).

fof(f918,plain,
    ( v1_zfmisc_1(sK3(sK18))
    | ~ spl26_112 ),
    inference(avatar_component_clause,[],[f917])).

fof(f5440,plain,
    ( spl26_458
    | ~ spl26_112 ),
    inference(avatar_split_clause,[],[f5429,f917,f5438])).

fof(f5438,plain,
    ( spl26_458
  <=> v1_zfmisc_1(sK12(sK3(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_458])])).

fof(f5429,plain,
    ( v1_zfmisc_1(sK12(sK3(sK18)))
    | ~ spl26_112 ),
    inference(resolution,[],[f920,f292])).

fof(f5376,plain,
    ( spl26_456
    | ~ spl26_76 ),
    inference(avatar_split_clause,[],[f5355,f639,f5374])).

fof(f5374,plain,
    ( spl26_456
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK10(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_456])])).

fof(f639,plain,
    ( spl26_76
  <=> v1_relat_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_76])])).

fof(f5355,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK10(sK17))))
    | ~ spl26_76 ),
    inference(resolution,[],[f904,f289])).

fof(f904,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(sK10(sK17)))
        | v1_relat_1(X9) )
    | ~ spl26_76 ),
    inference(resolution,[],[f250,f640])).

fof(f640,plain,
    ( v1_relat_1(sK10(sK17))
    | ~ spl26_76 ),
    inference(avatar_component_clause,[],[f639])).

fof(f5368,plain,
    ( spl26_454
    | ~ spl26_76 ),
    inference(avatar_split_clause,[],[f5357,f639,f5366])).

fof(f5366,plain,
    ( spl26_454
  <=> v1_relat_1(sK12(sK10(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_454])])).

fof(f5357,plain,
    ( v1_relat_1(sK12(sK10(sK17)))
    | ~ spl26_76 ),
    inference(resolution,[],[f904,f292])).

fof(f5266,plain,
    ( spl26_452
    | ~ spl26_108 ),
    inference(avatar_split_clause,[],[f5244,f889,f5264])).

fof(f5264,plain,
    ( spl26_452
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_452])])).

fof(f889,plain,
    ( spl26_108
  <=> v1_zfmisc_1(sK12(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_108])])).

fof(f5244,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK12(sK18))))
    | ~ spl26_108 ),
    inference(resolution,[],[f892,f289])).

fof(f892,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK18)))
        | v1_zfmisc_1(X0) )
    | ~ spl26_108 ),
    inference(resolution,[],[f890,f249])).

fof(f890,plain,
    ( v1_zfmisc_1(sK12(sK18))
    | ~ spl26_108 ),
    inference(avatar_component_clause,[],[f889])).

fof(f5257,plain,
    ( spl26_450
    | ~ spl26_108 ),
    inference(avatar_split_clause,[],[f5246,f889,f5255])).

fof(f5255,plain,
    ( spl26_450
  <=> v1_zfmisc_1(sK12(sK12(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_450])])).

fof(f5246,plain,
    ( v1_zfmisc_1(sK12(sK12(sK18)))
    | ~ spl26_108 ),
    inference(resolution,[],[f892,f292])).

fof(f5231,plain,
    ( spl26_448
    | ~ spl26_90 ),
    inference(avatar_split_clause,[],[f5224,f770,f5229])).

fof(f5229,plain,
    ( spl26_448
  <=> v1_relat_1(sK10(sK10(k1_zfmisc_1(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_448])])).

fof(f770,plain,
    ( spl26_90
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_90])])).

fof(f5224,plain,
    ( v1_relat_1(sK10(sK10(k1_zfmisc_1(sK17))))
    | ~ spl26_90 ),
    inference(resolution,[],[f815,f289])).

fof(f815,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK10(k1_zfmisc_1(sK17)))
        | v1_relat_1(X2) )
    | ~ spl26_90 ),
    inference(resolution,[],[f771,f246])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
          | ~ m1_subset_1(X1,X0) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ( v1_funct_1(X1)
            & v1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc9_funct_1)).

fof(f771,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl26_90 ),
    inference(avatar_component_clause,[],[f770])).

fof(f5222,plain,
    ( spl26_446
    | ~ spl26_90 ),
    inference(avatar_split_clause,[],[f5215,f770,f5220])).

fof(f5220,plain,
    ( spl26_446
  <=> v1_funct_1(sK10(sK10(k1_zfmisc_1(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_446])])).

fof(f5215,plain,
    ( v1_funct_1(sK10(sK10(k1_zfmisc_1(sK17))))
    | ~ spl26_90 ),
    inference(resolution,[],[f814,f289])).

fof(f814,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK10(k1_zfmisc_1(sK17)))
        | v1_funct_1(X1) )
    | ~ spl26_90 ),
    inference(resolution,[],[f771,f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f4789,plain,
    ( spl26_444
    | ~ spl26_98 ),
    inference(avatar_split_clause,[],[f4768,f807,f4787])).

fof(f4787,plain,
    ( spl26_444
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK6(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_444])])).

fof(f807,plain,
    ( spl26_98
  <=> v4_funct_1(sK6(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_98])])).

fof(f4768,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK6(sK17))))
    | ~ spl26_98 ),
    inference(resolution,[],[f810,f289])).

fof(f810,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(sK17)))
        | v4_funct_1(X0) )
    | ~ spl26_98 ),
    inference(resolution,[],[f808,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v4_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v4_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc10_funct_1)).

fof(f808,plain,
    ( v4_funct_1(sK6(sK17))
    | ~ spl26_98 ),
    inference(avatar_component_clause,[],[f807])).

fof(f4779,plain,
    ( spl26_442
    | ~ spl26_98 ),
    inference(avatar_split_clause,[],[f4770,f807,f4777])).

fof(f4777,plain,
    ( spl26_442
  <=> v4_funct_1(sK12(sK6(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_442])])).

fof(f4770,plain,
    ( v4_funct_1(sK12(sK6(sK17)))
    | ~ spl26_98 ),
    inference(resolution,[],[f810,f292])).

fof(f4710,plain,
    ( spl26_440
    | ~ spl26_96 ),
    inference(avatar_split_clause,[],[f4689,f797,f4708])).

fof(f4708,plain,
    ( spl26_440
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK5(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_440])])).

fof(f797,plain,
    ( spl26_96
  <=> v4_funct_1(sK5(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_96])])).

fof(f4689,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK5(sK17))))
    | ~ spl26_96 ),
    inference(resolution,[],[f800,f289])).

fof(f800,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK17)))
        | v4_funct_1(X0) )
    | ~ spl26_96 ),
    inference(resolution,[],[f798,f248])).

fof(f798,plain,
    ( v4_funct_1(sK5(sK17))
    | ~ spl26_96 ),
    inference(avatar_component_clause,[],[f797])).

fof(f4700,plain,
    ( spl26_438
    | ~ spl26_96 ),
    inference(avatar_split_clause,[],[f4691,f797,f4698])).

fof(f4698,plain,
    ( spl26_438
  <=> v4_funct_1(sK12(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_438])])).

fof(f4691,plain,
    ( v4_funct_1(sK12(sK5(sK17)))
    | ~ spl26_96 ),
    inference(resolution,[],[f800,f292])).

fof(f4601,plain,
    ( spl26_436
    | ~ spl26_94 ),
    inference(avatar_split_clause,[],[f4580,f787,f4599])).

fof(f4599,plain,
    ( spl26_436
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK4(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_436])])).

fof(f787,plain,
    ( spl26_94
  <=> v4_funct_1(sK4(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_94])])).

fof(f4580,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK4(sK17))))
    | ~ spl26_94 ),
    inference(resolution,[],[f790,f289])).

fof(f790,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK17)))
        | v4_funct_1(X0) )
    | ~ spl26_94 ),
    inference(resolution,[],[f788,f248])).

fof(f788,plain,
    ( v4_funct_1(sK4(sK17))
    | ~ spl26_94 ),
    inference(avatar_component_clause,[],[f787])).

fof(f4591,plain,
    ( spl26_434
    | ~ spl26_94 ),
    inference(avatar_split_clause,[],[f4582,f787,f4589])).

fof(f4589,plain,
    ( spl26_434
  <=> v4_funct_1(sK12(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_434])])).

fof(f4582,plain,
    ( v4_funct_1(sK12(sK4(sK17)))
    | ~ spl26_94 ),
    inference(resolution,[],[f790,f292])).

fof(f4522,plain,
    ( spl26_432
    | ~ spl26_92 ),
    inference(avatar_split_clause,[],[f4501,f777,f4520])).

fof(f4520,plain,
    ( spl26_432
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK3(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_432])])).

fof(f777,plain,
    ( spl26_92
  <=> v4_funct_1(sK3(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_92])])).

fof(f4501,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK3(sK17))))
    | ~ spl26_92 ),
    inference(resolution,[],[f780,f289])).

fof(f780,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK17)))
        | v4_funct_1(X0) )
    | ~ spl26_92 ),
    inference(resolution,[],[f778,f248])).

fof(f778,plain,
    ( v4_funct_1(sK3(sK17))
    | ~ spl26_92 ),
    inference(avatar_component_clause,[],[f777])).

fof(f4512,plain,
    ( spl26_430
    | ~ spl26_92 ),
    inference(avatar_split_clause,[],[f4503,f777,f4510])).

fof(f4510,plain,
    ( spl26_430
  <=> v4_funct_1(sK12(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_430])])).

fof(f4503,plain,
    ( v4_funct_1(sK12(sK3(sK17)))
    | ~ spl26_92 ),
    inference(resolution,[],[f780,f292])).

fof(f4395,plain,
    ( spl26_428
    | ~ spl26_88 ),
    inference(avatar_split_clause,[],[f4374,f760,f4393])).

fof(f4393,plain,
    ( spl26_428
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK12(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_428])])).

fof(f760,plain,
    ( spl26_88
  <=> v4_funct_1(sK12(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_88])])).

fof(f4374,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK12(sK17))))
    | ~ spl26_88 ),
    inference(resolution,[],[f763,f289])).

fof(f763,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK17)))
        | v4_funct_1(X0) )
    | ~ spl26_88 ),
    inference(resolution,[],[f761,f248])).

fof(f761,plain,
    ( v4_funct_1(sK12(sK17))
    | ~ spl26_88 ),
    inference(avatar_component_clause,[],[f760])).

fof(f4385,plain,
    ( spl26_426
    | ~ spl26_88 ),
    inference(avatar_split_clause,[],[f4376,f760,f4383])).

fof(f4383,plain,
    ( spl26_426
  <=> v4_funct_1(sK12(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_426])])).

fof(f4376,plain,
    ( v4_funct_1(sK12(sK12(sK17)))
    | ~ spl26_88 ),
    inference(resolution,[],[f763,f292])).

fof(f4215,plain,
    ( spl26_258
    | spl26_424
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3714,f528,f521,f4213,f1984])).

fof(f1984,plain,
    ( spl26_258
  <=> v1_xboole_0(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_258])])).

fof(f4213,plain,
    ( spl26_424
  <=> v1_funct_1(sK6(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_424])])).

fof(f521,plain,
    ( spl26_48
  <=> v1_relat_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_48])])).

fof(f528,plain,
    ( spl26_50
  <=> v1_funct_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_50])])).

fof(f3714,plain,
    ( v1_funct_1(sK6(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f242])).

fof(f242,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f112,f180])).

fof(f180,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc4_subset_1)).

fof(f1773,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK25))
        | v1_funct_1(X8) )
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(subsumption_resolution,[],[f1764,f522])).

fof(f522,plain,
    ( v1_relat_1(sK25)
    | ~ spl26_48 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1764,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK25))
        | v1_funct_1(X8)
        | ~ v1_relat_1(sK25) )
    | ~ spl26_50 ),
    inference(resolution,[],[f281,f529])).

fof(f529,plain,
    ( v1_funct_1(sK25)
    | ~ spl26_50 ),
    inference(avatar_component_clause,[],[f528])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc3_funct_1)).

fof(f4206,plain,
    ( spl26_258
    | spl26_422
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3713,f528,f521,f4204,f1984])).

fof(f4204,plain,
    ( spl26_422
  <=> v1_funct_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_422])])).

fof(f3713,plain,
    ( v1_funct_1(sK5(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f239])).

fof(f4197,plain,
    ( spl26_258
    | spl26_420
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3712,f528,f521,f4195,f1984])).

fof(f4195,plain,
    ( spl26_420
  <=> v1_funct_1(sK4(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_420])])).

fof(f3712,plain,
    ( v1_funct_1(sK4(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f236])).

fof(f3854,plain,
    ( spl26_258
    | spl26_418
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3711,f528,f521,f3852,f1984])).

fof(f3852,plain,
    ( spl26_418
  <=> v1_funct_1(sK3(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_418])])).

fof(f3711,plain,
    ( v1_funct_1(sK3(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f234])).

fof(f234,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f109,f174])).

fof(f174,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_subset_1)).

fof(f3793,plain,
    ( spl26_416
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3717,f528,f521,f3791])).

fof(f3791,plain,
    ( spl26_416
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_416])])).

fof(f3717,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f289])).

fof(f3784,plain,
    ( spl26_414
    | ~ spl26_42
    | ~ spl26_44
    | spl26_155 ),
    inference(avatar_split_clause,[],[f3690,f1203,f507,f500,f3782])).

fof(f3782,plain,
    ( spl26_414
  <=> v1_funct_1(sK9(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_414])])).

fof(f500,plain,
    ( spl26_42
  <=> v1_relat_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_42])])).

fof(f507,plain,
    ( spl26_44
  <=> v1_funct_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_44])])).

fof(f1203,plain,
    ( spl26_155
  <=> ~ v1_zfmisc_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_155])])).

fof(f3690,plain,
    ( v1_funct_1(sK9(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_155 ),
    inference(subsumption_resolution,[],[f3680,f1204])).

fof(f1204,plain,
    ( ~ v1_zfmisc_1(sK24)
    | ~ spl26_155 ),
    inference(avatar_component_clause,[],[f1203])).

fof(f3680,plain,
    ( v1_funct_1(sK9(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f345])).

fof(f345,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f267,f231])).

fof(f231,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
     => ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc1_realset1)).

fof(f267,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK9(X0),X0)
        & v1_zfmisc_1(sK9(X0))
        & ~ v1_xboole_0(sK9(X0))
        & m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f135,f186])).

fof(f186,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK9(X0),X0)
        & v1_zfmisc_1(sK9(X0))
        & ~ v1_xboole_0(sK9(X0))
        & m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f135,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_tex_2)).

fof(f1772,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(sK24))
        | v1_funct_1(X7) )
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(subsumption_resolution,[],[f1763,f501])).

fof(f501,plain,
    ( v1_relat_1(sK24)
    | ~ spl26_42 ),
    inference(avatar_component_clause,[],[f500])).

fof(f1763,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(sK24))
        | v1_funct_1(X7)
        | ~ v1_relat_1(sK24) )
    | ~ spl26_44 ),
    inference(resolution,[],[f281,f508])).

fof(f508,plain,
    ( v1_funct_1(sK24)
    | ~ spl26_44 ),
    inference(avatar_component_clause,[],[f507])).

fof(f3775,plain,
    ( spl26_412
    | ~ spl26_42
    | ~ spl26_44
    | spl26_155 ),
    inference(avatar_split_clause,[],[f3689,f1203,f507,f500,f3773])).

fof(f3773,plain,
    ( spl26_412
  <=> v1_funct_1(sK8(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_412])])).

fof(f3689,plain,
    ( v1_funct_1(sK8(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_155 ),
    inference(subsumption_resolution,[],[f3679,f1204])).

fof(f3679,plain,
    ( v1_funct_1(sK8(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f341])).

fof(f341,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f263,f231])).

fof(f263,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK8(X0),X0)
        & ~ v1_zfmisc_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f133,f184])).

fof(f184,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK8(X0),X0)
        & ~ v1_zfmisc_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f133,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f132])).

fof(f132,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc3_tex_2)).

fof(f3766,plain,
    ( spl26_410
    | ~ spl26_42
    | ~ spl26_44
    | spl26_63 ),
    inference(avatar_split_clause,[],[f3688,f575,f507,f500,f3764])).

fof(f3764,plain,
    ( spl26_410
  <=> v1_funct_1(sK6(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_410])])).

fof(f575,plain,
    ( spl26_63
  <=> ~ v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_63])])).

fof(f3688,plain,
    ( v1_funct_1(sK6(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f3678,f576])).

fof(f576,plain,
    ( ~ v1_xboole_0(sK24)
    | ~ spl26_63 ),
    inference(avatar_component_clause,[],[f575])).

fof(f3678,plain,
    ( v1_funct_1(sK6(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f242])).

fof(f3757,plain,
    ( spl26_408
    | ~ spl26_42
    | ~ spl26_44
    | spl26_63 ),
    inference(avatar_split_clause,[],[f3687,f575,f507,f500,f3755])).

fof(f3755,plain,
    ( spl26_408
  <=> v1_funct_1(sK5(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_408])])).

fof(f3687,plain,
    ( v1_funct_1(sK5(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f3677,f576])).

fof(f3677,plain,
    ( v1_funct_1(sK5(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f239])).

fof(f3748,plain,
    ( spl26_406
    | ~ spl26_42
    | ~ spl26_44
    | spl26_63 ),
    inference(avatar_split_clause,[],[f3686,f575,f507,f500,f3746])).

fof(f3746,plain,
    ( spl26_406
  <=> v1_funct_1(sK4(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_406])])).

fof(f3686,plain,
    ( v1_funct_1(sK4(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f3676,f576])).

fof(f3676,plain,
    ( v1_funct_1(sK4(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f236])).

fof(f3739,plain,
    ( spl26_404
    | ~ spl26_42
    | ~ spl26_44
    | spl26_63 ),
    inference(avatar_split_clause,[],[f3685,f575,f507,f500,f3737])).

fof(f3737,plain,
    ( spl26_404
  <=> v1_funct_1(sK3(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_404])])).

fof(f3685,plain,
    ( v1_funct_1(sK3(sK24))
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f3675,f576])).

fof(f3675,plain,
    ( v1_funct_1(sK3(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f234])).

fof(f3730,plain,
    ( spl26_402
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(avatar_split_clause,[],[f3719,f528,f521,f3728])).

fof(f3728,plain,
    ( spl26_402
  <=> v1_funct_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_402])])).

fof(f3719,plain,
    ( v1_funct_1(sK12(sK25))
    | ~ spl26_48
    | ~ spl26_50 ),
    inference(resolution,[],[f1773,f292])).

fof(f3707,plain,
    ( spl26_400
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(avatar_split_clause,[],[f3681,f507,f500,f3705])).

fof(f3705,plain,
    ( spl26_400
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_400])])).

fof(f3681,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK24)))
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f289])).

fof(f3698,plain,
    ( spl26_398
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(avatar_split_clause,[],[f3683,f507,f500,f3696])).

fof(f3696,plain,
    ( spl26_398
  <=> v1_funct_1(sK12(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_398])])).

fof(f3683,plain,
    ( v1_funct_1(sK12(sK24))
    | ~ spl26_42
    | ~ spl26_44 ),
    inference(resolution,[],[f1772,f292])).

fof(f3643,plain,
    ( spl26_210
    | spl26_396
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(avatar_split_clause,[],[f3411,f479,f472,f3641,f1565])).

fof(f1565,plain,
    ( spl26_210
  <=> v1_zfmisc_1(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_210])])).

fof(f3641,plain,
    ( spl26_396
  <=> v1_funct_1(sK9(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_396])])).

fof(f472,plain,
    ( spl26_34
  <=> v1_relat_1(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_34])])).

fof(f479,plain,
    ( spl26_36
  <=> v1_funct_1(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_36])])).

fof(f3411,plain,
    ( v1_funct_1(sK9(sK22))
    | v1_zfmisc_1(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f345])).

fof(f1769,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK22))
        | v1_funct_1(X5) )
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(subsumption_resolution,[],[f1761,f473])).

fof(f473,plain,
    ( v1_relat_1(sK22)
    | ~ spl26_34 ),
    inference(avatar_component_clause,[],[f472])).

fof(f1761,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK22))
        | v1_funct_1(X5)
        | ~ v1_relat_1(sK22) )
    | ~ spl26_36 ),
    inference(resolution,[],[f281,f480])).

fof(f480,plain,
    ( v1_funct_1(sK22)
    | ~ spl26_36 ),
    inference(avatar_component_clause,[],[f479])).

fof(f3634,plain,
    ( spl26_210
    | spl26_394
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(avatar_split_clause,[],[f3410,f479,f472,f3632,f1565])).

fof(f3632,plain,
    ( spl26_394
  <=> v1_funct_1(sK8(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_394])])).

fof(f3410,plain,
    ( v1_funct_1(sK8(sK22))
    | v1_zfmisc_1(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f341])).

fof(f3619,plain,
    ( spl26_392
    | ~ spl26_38
    | ~ spl26_40
    | spl26_221 ),
    inference(avatar_split_clause,[],[f3566,f1724,f493,f486,f3617])).

fof(f3617,plain,
    ( spl26_392
  <=> v1_funct_1(sK6(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_392])])).

fof(f486,plain,
    ( spl26_38
  <=> v1_relat_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_38])])).

fof(f493,plain,
    ( spl26_40
  <=> v1_funct_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_40])])).

fof(f1724,plain,
    ( spl26_221
  <=> ~ v1_xboole_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_221])])).

fof(f3566,plain,
    ( v1_funct_1(sK6(sK23))
    | ~ spl26_38
    | ~ spl26_40
    | ~ spl26_221 ),
    inference(subsumption_resolution,[],[f3556,f1725])).

fof(f1725,plain,
    ( ~ v1_xboole_0(sK23)
    | ~ spl26_221 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f3556,plain,
    ( v1_funct_1(sK6(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f242])).

fof(f1770,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK23))
        | v1_funct_1(X6) )
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(subsumption_resolution,[],[f1762,f487])).

fof(f487,plain,
    ( v1_relat_1(sK23)
    | ~ spl26_38 ),
    inference(avatar_component_clause,[],[f486])).

fof(f1762,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK23))
        | v1_funct_1(X6)
        | ~ v1_relat_1(sK23) )
    | ~ spl26_40 ),
    inference(resolution,[],[f281,f494])).

fof(f494,plain,
    ( v1_funct_1(sK23)
    | ~ spl26_40 ),
    inference(avatar_component_clause,[],[f493])).

fof(f3610,plain,
    ( spl26_390
    | ~ spl26_38
    | ~ spl26_40
    | spl26_221 ),
    inference(avatar_split_clause,[],[f3565,f1724,f493,f486,f3608])).

fof(f3608,plain,
    ( spl26_390
  <=> v1_funct_1(sK5(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_390])])).

fof(f3565,plain,
    ( v1_funct_1(sK5(sK23))
    | ~ spl26_38
    | ~ spl26_40
    | ~ spl26_221 ),
    inference(subsumption_resolution,[],[f3555,f1725])).

fof(f3555,plain,
    ( v1_funct_1(sK5(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f239])).

fof(f3601,plain,
    ( spl26_388
    | ~ spl26_38
    | ~ spl26_40
    | spl26_221 ),
    inference(avatar_split_clause,[],[f3564,f1724,f493,f486,f3599])).

fof(f3599,plain,
    ( spl26_388
  <=> v1_funct_1(sK4(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_388])])).

fof(f3564,plain,
    ( v1_funct_1(sK4(sK23))
    | ~ spl26_38
    | ~ spl26_40
    | ~ spl26_221 ),
    inference(subsumption_resolution,[],[f3554,f1725])).

fof(f3554,plain,
    ( v1_funct_1(sK4(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f236])).

fof(f3592,plain,
    ( spl26_386
    | ~ spl26_38
    | ~ spl26_40
    | spl26_221 ),
    inference(avatar_split_clause,[],[f3563,f1724,f493,f486,f3590])).

fof(f3590,plain,
    ( spl26_386
  <=> v1_funct_1(sK3(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_386])])).

fof(f3563,plain,
    ( v1_funct_1(sK3(sK23))
    | ~ spl26_38
    | ~ spl26_40
    | ~ spl26_221 ),
    inference(subsumption_resolution,[],[f3553,f1725])).

fof(f3553,plain,
    ( v1_funct_1(sK3(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f234])).

fof(f3583,plain,
    ( spl26_384
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(avatar_split_clause,[],[f3559,f493,f486,f3581])).

fof(f3581,plain,
    ( spl26_384
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_384])])).

fof(f3559,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK23)))
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f289])).

fof(f3574,plain,
    ( spl26_382
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(avatar_split_clause,[],[f3561,f493,f486,f3572])).

fof(f3572,plain,
    ( spl26_382
  <=> v1_funct_1(sK12(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_382])])).

fof(f3561,plain,
    ( v1_funct_1(sK12(sK23))
    | ~ spl26_38
    | ~ spl26_40 ),
    inference(resolution,[],[f1770,f292])).

fof(f3501,plain,
    ( spl26_380
    | ~ spl26_34
    | ~ spl26_36
    | spl26_195 ),
    inference(avatar_split_clause,[],[f3419,f1461,f479,f472,f3499])).

fof(f3499,plain,
    ( spl26_380
  <=> v1_funct_1(sK6(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_380])])).

fof(f1461,plain,
    ( spl26_195
  <=> ~ v1_xboole_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_195])])).

fof(f3419,plain,
    ( v1_funct_1(sK6(sK22))
    | ~ spl26_34
    | ~ spl26_36
    | ~ spl26_195 ),
    inference(subsumption_resolution,[],[f3409,f1462])).

fof(f1462,plain,
    ( ~ v1_xboole_0(sK22)
    | ~ spl26_195 ),
    inference(avatar_component_clause,[],[f1461])).

fof(f3409,plain,
    ( v1_funct_1(sK6(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f242])).

fof(f3492,plain,
    ( spl26_378
    | ~ spl26_34
    | ~ spl26_36
    | spl26_195 ),
    inference(avatar_split_clause,[],[f3418,f1461,f479,f472,f3490])).

fof(f3490,plain,
    ( spl26_378
  <=> v1_funct_1(sK5(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_378])])).

fof(f3418,plain,
    ( v1_funct_1(sK5(sK22))
    | ~ spl26_34
    | ~ spl26_36
    | ~ spl26_195 ),
    inference(subsumption_resolution,[],[f3408,f1462])).

fof(f3408,plain,
    ( v1_funct_1(sK5(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f239])).

fof(f3483,plain,
    ( spl26_376
    | ~ spl26_34
    | ~ spl26_36
    | spl26_195 ),
    inference(avatar_split_clause,[],[f3417,f1461,f479,f472,f3481])).

fof(f3481,plain,
    ( spl26_376
  <=> v1_funct_1(sK4(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_376])])).

fof(f3417,plain,
    ( v1_funct_1(sK4(sK22))
    | ~ spl26_34
    | ~ spl26_36
    | ~ spl26_195 ),
    inference(subsumption_resolution,[],[f3407,f1462])).

fof(f3407,plain,
    ( v1_funct_1(sK4(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f236])).

fof(f3474,plain,
    ( spl26_374
    | ~ spl26_34
    | ~ spl26_36
    | spl26_195 ),
    inference(avatar_split_clause,[],[f3416,f1461,f479,f472,f3472])).

fof(f3472,plain,
    ( spl26_374
  <=> v1_funct_1(sK3(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_374])])).

fof(f3416,plain,
    ( v1_funct_1(sK3(sK22))
    | ~ spl26_34
    | ~ spl26_36
    | ~ spl26_195 ),
    inference(subsumption_resolution,[],[f3406,f1462])).

fof(f3406,plain,
    ( v1_funct_1(sK3(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f234])).

fof(f3465,plain,
    ( spl26_372
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(avatar_split_clause,[],[f3412,f479,f472,f3463])).

fof(f3463,plain,
    ( spl26_372
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_372])])).

fof(f3412,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK22)))
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f289])).

fof(f3456,plain,
    ( spl26_370
    | spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3376,f458,f451,f444,f3454])).

fof(f3454,plain,
    ( spl26_370
  <=> v1_funct_1(sK6(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_370])])).

fof(f444,plain,
    ( spl26_27
  <=> ~ v1_xboole_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_27])])).

fof(f451,plain,
    ( spl26_28
  <=> v1_relat_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_28])])).

fof(f458,plain,
    ( spl26_30
  <=> v1_funct_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_30])])).

fof(f3376,plain,
    ( v1_funct_1(sK6(sK20))
    | ~ spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(subsumption_resolution,[],[f3366,f445])).

fof(f445,plain,
    ( ~ v1_xboole_0(sK20)
    | ~ spl26_27 ),
    inference(avatar_component_clause,[],[f444])).

fof(f3366,plain,
    ( v1_funct_1(sK6(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f242])).

fof(f1768,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK20))
        | v1_funct_1(X4) )
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(subsumption_resolution,[],[f1760,f452])).

fof(f452,plain,
    ( v1_relat_1(sK20)
    | ~ spl26_28 ),
    inference(avatar_component_clause,[],[f451])).

fof(f1760,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK20))
        | v1_funct_1(X4)
        | ~ v1_relat_1(sK20) )
    | ~ spl26_30 ),
    inference(resolution,[],[f281,f459])).

fof(f459,plain,
    ( v1_funct_1(sK20)
    | ~ spl26_30 ),
    inference(avatar_component_clause,[],[f458])).

fof(f3447,plain,
    ( spl26_368
    | spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3375,f458,f451,f444,f3445])).

fof(f3445,plain,
    ( spl26_368
  <=> v1_funct_1(sK5(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_368])])).

fof(f3375,plain,
    ( v1_funct_1(sK5(sK20))
    | ~ spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(subsumption_resolution,[],[f3365,f445])).

fof(f3365,plain,
    ( v1_funct_1(sK5(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f239])).

fof(f3438,plain,
    ( spl26_366
    | spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3374,f458,f451,f444,f3436])).

fof(f3436,plain,
    ( spl26_366
  <=> v1_funct_1(sK4(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_366])])).

fof(f3374,plain,
    ( v1_funct_1(sK4(sK20))
    | ~ spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(subsumption_resolution,[],[f3364,f445])).

fof(f3364,plain,
    ( v1_funct_1(sK4(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f236])).

fof(f3429,plain,
    ( spl26_364
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(avatar_split_clause,[],[f3414,f479,f472,f3427])).

fof(f3427,plain,
    ( spl26_364
  <=> v1_funct_1(sK12(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_364])])).

fof(f3414,plain,
    ( v1_funct_1(sK12(sK22))
    | ~ spl26_34
    | ~ spl26_36 ),
    inference(resolution,[],[f1769,f292])).

fof(f3402,plain,
    ( spl26_362
    | spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3373,f458,f451,f444,f3400])).

fof(f3400,plain,
    ( spl26_362
  <=> v1_funct_1(sK3(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_362])])).

fof(f3373,plain,
    ( v1_funct_1(sK3(sK20))
    | ~ spl26_27
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(subsumption_resolution,[],[f3363,f445])).

fof(f3363,plain,
    ( v1_funct_1(sK3(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f234])).

fof(f3393,plain,
    ( spl26_360
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3369,f458,f451,f3391])).

fof(f3391,plain,
    ( spl26_360
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_360])])).

fof(f3369,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK20)))
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f289])).

fof(f3384,plain,
    ( spl26_358
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(avatar_split_clause,[],[f3371,f458,f451,f3382])).

fof(f3382,plain,
    ( spl26_358
  <=> v1_funct_1(sK12(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_358])])).

fof(f3371,plain,
    ( v1_funct_1(sK12(sK20))
    | ~ spl26_28
    | ~ spl26_30 ),
    inference(resolution,[],[f1768,f292])).

fof(f3340,plain,(
    spl26_202 ),
    inference(avatar_split_clause,[],[f3336,f1512])).

fof(f1512,plain,
    ( spl26_202
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_202])])).

fof(f3336,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f3325,f2758])).

fof(f3325,plain,(
    ! [X1] : v1_funct_1(k9_subset_1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(resolution,[],[f3319,f2270])).

fof(f3319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f3313,f2758])).

fof(f3313,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k9_subset_1(k1_xboole_0,X1,k1_xboole_0))) ) ),
    inference(resolution,[],[f1765,f2684])).

fof(f2684,plain,(
    ! [X11] : v1_xboole_0(k9_subset_1(k1_xboole_0,X11,k1_xboole_0)) ),
    inference(resolution,[],[f2270,f1041])).

fof(f1041,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f1038,f591])).

fof(f1038,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK11(X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f257,f291])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc1_subset_1)).

fof(f1765,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f1757,f255])).

fof(f255,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc1_relat_1)).

fof(f1757,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f281,f252])).

fof(f252,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc1_funct_1)).

fof(f3041,plain,
    ( ~ spl26_357
    | ~ spl26_56
    | spl26_71 ),
    inference(avatar_split_clause,[],[f3031,f613,f549,f3039])).

fof(f613,plain,
    ( spl26_71
  <=> ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_71])])).

fof(f3031,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl26_56
    | ~ spl26_71 ),
    inference(superposition,[],[f614,f2747])).

fof(f614,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl26_71 ),
    inference(avatar_component_clause,[],[f613])).

fof(f3000,plain,
    ( ~ spl26_355
    | spl26_353 ),
    inference(avatar_split_clause,[],[f2993,f2990,f2998])).

fof(f2998,plain,
    ( spl26_355
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_355])])).

fof(f2990,plain,
    ( spl26_353
  <=> ~ v1_zfmisc_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_353])])).

fof(f2993,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl26_353 ),
    inference(resolution,[],[f2991,f231])).

fof(f2991,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ spl26_353 ),
    inference(avatar_component_clause,[],[f2990])).

fof(f2992,plain,
    ( spl26_342
    | spl26_350
    | ~ spl26_353
    | ~ spl26_56 ),
    inference(avatar_split_clause,[],[f2426,f549,f2990,f2984,f2905])).

fof(f2905,plain,
    ( spl26_342
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_342])])).

fof(f2984,plain,
    ( spl26_350
  <=> v1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_350])])).

fof(f2426,plain,
    ( ~ v1_zfmisc_1(sK2)
    | v1_subset_1(sK2,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl26_56 ),
    inference(resolution,[],[f337,f550])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X1)
      | v1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f336,f231])).

fof(f336,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f260,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc3_subset_1)).

fof(f260,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,X0)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc4_tex_2)).

fof(f2957,plain,
    ( ~ spl26_349
    | spl26_347 ),
    inference(avatar_split_clause,[],[f2950,f2917,f2955])).

fof(f2955,plain,
    ( spl26_349
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_349])])).

fof(f2917,plain,
    ( spl26_347
  <=> ~ v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_347])])).

fof(f2950,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl26_347 ),
    inference(resolution,[],[f2918,f231])).

fof(f2918,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ spl26_347 ),
    inference(avatar_component_clause,[],[f2917])).

fof(f2919,plain,
    ( spl26_342
    | spl26_344
    | ~ spl26_347
    | ~ spl26_54 ),
    inference(avatar_split_clause,[],[f2425,f542,f2917,f2911,f2905])).

fof(f2911,plain,
    ( spl26_344
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_344])])).

fof(f2425,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl26_54 ),
    inference(resolution,[],[f337,f543])).

fof(f2676,plain,
    ( spl26_258
    | spl26_340
    | ~ spl26_268 ),
    inference(avatar_split_clause,[],[f2616,f2022,f2674,f1984])).

fof(f2674,plain,
    ( spl26_340
  <=> v1_zfmisc_1(sK6(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_340])])).

fof(f2022,plain,
    ( spl26_268
  <=> v1_zfmisc_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_268])])).

fof(f2616,plain,
    ( v1_zfmisc_1(sK6(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_268 ),
    inference(resolution,[],[f2031,f242])).

fof(f2031,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25))
        | v1_zfmisc_1(X0) )
    | ~ spl26_268 ),
    inference(resolution,[],[f2023,f249])).

fof(f2023,plain,
    ( v1_zfmisc_1(sK25)
    | ~ spl26_268 ),
    inference(avatar_component_clause,[],[f2022])).

fof(f2668,plain,
    ( spl26_258
    | spl26_338
    | ~ spl26_268 ),
    inference(avatar_split_clause,[],[f2613,f2022,f2666,f1984])).

fof(f2666,plain,
    ( spl26_338
  <=> v1_zfmisc_1(sK3(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_338])])).

fof(f2613,plain,
    ( v1_zfmisc_1(sK3(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_268 ),
    inference(resolution,[],[f2031,f234])).

fof(f2638,plain,
    ( spl26_336
    | ~ spl26_268 ),
    inference(avatar_split_clause,[],[f2619,f2022,f2636])).

fof(f2636,plain,
    ( spl26_336
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_336])])).

fof(f2619,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl26_268 ),
    inference(resolution,[],[f2031,f289])).

fof(f2629,plain,
    ( spl26_334
    | ~ spl26_268 ),
    inference(avatar_split_clause,[],[f2621,f2022,f2627])).

fof(f2627,plain,
    ( spl26_334
  <=> v1_zfmisc_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_334])])).

fof(f2621,plain,
    ( v1_zfmisc_1(sK12(sK25))
    | ~ spl26_268 ),
    inference(resolution,[],[f2031,f292])).

fof(f2586,plain,
    ( spl26_332
    | spl26_221
    | ~ spl26_232 ),
    inference(avatar_split_clause,[],[f2547,f1794,f1724,f2584])).

fof(f2584,plain,
    ( spl26_332
  <=> v1_zfmisc_1(sK6(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_332])])).

fof(f1794,plain,
    ( spl26_232
  <=> v1_zfmisc_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_232])])).

fof(f2547,plain,
    ( v1_zfmisc_1(sK6(sK23))
    | ~ spl26_221
    | ~ spl26_232 ),
    inference(subsumption_resolution,[],[f2540,f1725])).

fof(f2540,plain,
    ( v1_zfmisc_1(sK6(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_232 ),
    inference(resolution,[],[f1811,f242])).

fof(f1811,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK23))
        | v1_zfmisc_1(X0) )
    | ~ spl26_232 ),
    inference(resolution,[],[f1795,f249])).

fof(f1795,plain,
    ( v1_zfmisc_1(sK23)
    | ~ spl26_232 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f2571,plain,
    ( spl26_330
    | spl26_221
    | ~ spl26_232 ),
    inference(avatar_split_clause,[],[f2546,f1794,f1724,f2569])).

fof(f2569,plain,
    ( spl26_330
  <=> v1_zfmisc_1(sK3(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_330])])).

fof(f2546,plain,
    ( v1_zfmisc_1(sK3(sK23))
    | ~ spl26_221
    | ~ spl26_232 ),
    inference(subsumption_resolution,[],[f2537,f1725])).

fof(f2537,plain,
    ( v1_zfmisc_1(sK3(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_232 ),
    inference(resolution,[],[f1811,f234])).

fof(f2564,plain,
    ( spl26_328
    | ~ spl26_232 ),
    inference(avatar_split_clause,[],[f2543,f1794,f2562])).

fof(f2562,plain,
    ( spl26_328
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_328])])).

fof(f2543,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK23)))
    | ~ spl26_232 ),
    inference(resolution,[],[f1811,f289])).

fof(f2555,plain,
    ( spl26_326
    | ~ spl26_232 ),
    inference(avatar_split_clause,[],[f2545,f1794,f2553])).

fof(f2553,plain,
    ( spl26_326
  <=> v1_zfmisc_1(sK12(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_326])])).

fof(f2545,plain,
    ( v1_zfmisc_1(sK12(sK23))
    | ~ spl26_232 ),
    inference(resolution,[],[f1811,f292])).

fof(f2510,plain,
    ( spl26_324
    | spl26_169
    | ~ spl26_184 ),
    inference(avatar_split_clause,[],[f2478,f1393,f1310,f2508])).

fof(f2508,plain,
    ( spl26_324
  <=> v1_zfmisc_1(sK6(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_324])])).

fof(f1310,plain,
    ( spl26_169
  <=> ~ v1_xboole_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_169])])).

fof(f1393,plain,
    ( spl26_184
  <=> v1_zfmisc_1(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_184])])).

fof(f2478,plain,
    ( v1_zfmisc_1(sK6(sK21))
    | ~ spl26_169
    | ~ spl26_184 ),
    inference(subsumption_resolution,[],[f2471,f1311])).

fof(f1311,plain,
    ( ~ v1_xboole_0(sK21)
    | ~ spl26_169 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f2471,plain,
    ( v1_zfmisc_1(sK6(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_184 ),
    inference(resolution,[],[f1525,f242])).

fof(f1525,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK21))
        | v1_zfmisc_1(X0) )
    | ~ spl26_184 ),
    inference(resolution,[],[f1394,f249])).

fof(f1394,plain,
    ( v1_zfmisc_1(sK21)
    | ~ spl26_184 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f2502,plain,
    ( spl26_322
    | spl26_169
    | ~ spl26_184 ),
    inference(avatar_split_clause,[],[f2477,f1393,f1310,f2500])).

fof(f2500,plain,
    ( spl26_322
  <=> v1_zfmisc_1(sK3(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_322])])).

fof(f2477,plain,
    ( v1_zfmisc_1(sK3(sK21))
    | ~ spl26_169
    | ~ spl26_184 ),
    inference(subsumption_resolution,[],[f2468,f1311])).

fof(f2468,plain,
    ( v1_zfmisc_1(sK3(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_184 ),
    inference(resolution,[],[f1525,f234])).

fof(f2495,plain,
    ( spl26_320
    | ~ spl26_184 ),
    inference(avatar_split_clause,[],[f2474,f1393,f2493])).

fof(f2493,plain,
    ( spl26_320
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_320])])).

fof(f2474,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK21)))
    | ~ spl26_184 ),
    inference(resolution,[],[f1525,f289])).

fof(f2486,plain,
    ( spl26_318
    | ~ spl26_184 ),
    inference(avatar_split_clause,[],[f2476,f1393,f2484])).

fof(f2484,plain,
    ( spl26_318
  <=> v1_zfmisc_1(sK12(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_318])])).

fof(f2476,plain,
    ( v1_zfmisc_1(sK12(sK21))
    | ~ spl26_184 ),
    inference(resolution,[],[f1525,f292])).

fof(f2403,plain,
    ( spl26_316
    | spl26_27
    | ~ spl26_158 ),
    inference(avatar_split_clause,[],[f2372,f1242,f444,f2401])).

fof(f2401,plain,
    ( spl26_316
  <=> v1_zfmisc_1(sK6(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_316])])).

fof(f1242,plain,
    ( spl26_158
  <=> v1_zfmisc_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_158])])).

fof(f2372,plain,
    ( v1_zfmisc_1(sK6(sK20))
    | ~ spl26_27
    | ~ spl26_158 ),
    inference(subsumption_resolution,[],[f2365,f445])).

fof(f2365,plain,
    ( v1_zfmisc_1(sK6(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_158 ),
    inference(resolution,[],[f1251,f242])).

fof(f1251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK20))
        | v1_zfmisc_1(X0) )
    | ~ spl26_158 ),
    inference(resolution,[],[f1243,f249])).

fof(f1243,plain,
    ( v1_zfmisc_1(sK20)
    | ~ spl26_158 ),
    inference(avatar_component_clause,[],[f1242])).

fof(f2395,plain,
    ( spl26_314
    | spl26_27
    | ~ spl26_158 ),
    inference(avatar_split_clause,[],[f2371,f1242,f444,f2393])).

fof(f2393,plain,
    ( spl26_314
  <=> v1_zfmisc_1(sK3(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_314])])).

fof(f2371,plain,
    ( v1_zfmisc_1(sK3(sK20))
    | ~ spl26_27
    | ~ spl26_158 ),
    inference(subsumption_resolution,[],[f2362,f445])).

fof(f2362,plain,
    ( v1_zfmisc_1(sK3(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_158 ),
    inference(resolution,[],[f1251,f234])).

fof(f2388,plain,
    ( spl26_312
    | ~ spl26_158 ),
    inference(avatar_split_clause,[],[f2368,f1242,f2386])).

fof(f2386,plain,
    ( spl26_312
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_312])])).

fof(f2368,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK20)))
    | ~ spl26_158 ),
    inference(resolution,[],[f1251,f289])).

fof(f2380,plain,
    ( spl26_310
    | ~ spl26_158 ),
    inference(avatar_split_clause,[],[f2370,f1242,f2378])).

fof(f2378,plain,
    ( spl26_310
  <=> v1_zfmisc_1(sK12(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_310])])).

fof(f2370,plain,
    ( v1_zfmisc_1(sK12(sK20))
    | ~ spl26_158 ),
    inference(resolution,[],[f1251,f292])).

fof(f2335,plain,
    ( spl26_308
    | spl26_23
    | ~ spl26_136 ),
    inference(avatar_split_clause,[],[f2304,f1114,f430,f2333])).

fof(f2333,plain,
    ( spl26_308
  <=> v1_zfmisc_1(sK6(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_308])])).

fof(f430,plain,
    ( spl26_23
  <=> ~ v1_xboole_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_23])])).

fof(f1114,plain,
    ( spl26_136
  <=> v1_zfmisc_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_136])])).

fof(f2304,plain,
    ( v1_zfmisc_1(sK6(sK19))
    | ~ spl26_23
    | ~ spl26_136 ),
    inference(subsumption_resolution,[],[f2297,f431])).

fof(f431,plain,
    ( ~ v1_xboole_0(sK19)
    | ~ spl26_23 ),
    inference(avatar_component_clause,[],[f430])).

fof(f2297,plain,
    ( v1_zfmisc_1(sK6(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_136 ),
    inference(resolution,[],[f1123,f242])).

fof(f1123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK19))
        | v1_zfmisc_1(X0) )
    | ~ spl26_136 ),
    inference(resolution,[],[f1115,f249])).

fof(f1115,plain,
    ( v1_zfmisc_1(sK19)
    | ~ spl26_136 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f2327,plain,
    ( spl26_306
    | spl26_23
    | ~ spl26_136 ),
    inference(avatar_split_clause,[],[f2303,f1114,f430,f2325])).

fof(f2325,plain,
    ( spl26_306
  <=> v1_zfmisc_1(sK3(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_306])])).

fof(f2303,plain,
    ( v1_zfmisc_1(sK3(sK19))
    | ~ spl26_23
    | ~ spl26_136 ),
    inference(subsumption_resolution,[],[f2294,f431])).

fof(f2294,plain,
    ( v1_zfmisc_1(sK3(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_136 ),
    inference(resolution,[],[f1123,f234])).

fof(f2320,plain,
    ( spl26_304
    | ~ spl26_136 ),
    inference(avatar_split_clause,[],[f2300,f1114,f2318])).

fof(f2318,plain,
    ( spl26_304
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_304])])).

fof(f2300,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK19)))
    | ~ spl26_136 ),
    inference(resolution,[],[f1123,f289])).

fof(f2312,plain,
    ( spl26_302
    | ~ spl26_136 ),
    inference(avatar_split_clause,[],[f2302,f1114,f2310])).

fof(f2310,plain,
    ( spl26_302
  <=> v1_zfmisc_1(sK12(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_302])])).

fof(f2302,plain,
    ( v1_zfmisc_1(sK12(sK19))
    | ~ spl26_136 ),
    inference(resolution,[],[f1123,f292])).

fof(f2244,plain,
    ( spl26_300
    | spl26_15
    | ~ spl26_100 ),
    inference(avatar_split_clause,[],[f2213,f846,f402,f2242])).

fof(f2242,plain,
    ( spl26_300
  <=> v1_zfmisc_1(sK6(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_300])])).

fof(f402,plain,
    ( spl26_15
  <=> ~ v1_xboole_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_15])])).

fof(f846,plain,
    ( spl26_100
  <=> v1_zfmisc_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_100])])).

fof(f2213,plain,
    ( v1_zfmisc_1(sK6(sK17))
    | ~ spl26_15
    | ~ spl26_100 ),
    inference(subsumption_resolution,[],[f2206,f403])).

fof(f403,plain,
    ( ~ v1_xboole_0(sK17)
    | ~ spl26_15 ),
    inference(avatar_component_clause,[],[f402])).

fof(f2206,plain,
    ( v1_zfmisc_1(sK6(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_100 ),
    inference(resolution,[],[f855,f242])).

fof(f855,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17))
        | v1_zfmisc_1(X0) )
    | ~ spl26_100 ),
    inference(resolution,[],[f847,f249])).

fof(f847,plain,
    ( v1_zfmisc_1(sK17)
    | ~ spl26_100 ),
    inference(avatar_component_clause,[],[f846])).

fof(f2236,plain,
    ( spl26_298
    | spl26_15
    | ~ spl26_100 ),
    inference(avatar_split_clause,[],[f2212,f846,f402,f2234])).

fof(f2234,plain,
    ( spl26_298
  <=> v1_zfmisc_1(sK3(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_298])])).

fof(f2212,plain,
    ( v1_zfmisc_1(sK3(sK17))
    | ~ spl26_15
    | ~ spl26_100 ),
    inference(subsumption_resolution,[],[f2203,f403])).

fof(f2203,plain,
    ( v1_zfmisc_1(sK3(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_100 ),
    inference(resolution,[],[f855,f234])).

fof(f2229,plain,
    ( spl26_296
    | ~ spl26_100 ),
    inference(avatar_split_clause,[],[f2209,f846,f2227])).

fof(f2227,plain,
    ( spl26_296
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_296])])).

fof(f2209,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl26_100 ),
    inference(resolution,[],[f855,f289])).

fof(f2221,plain,
    ( spl26_294
    | ~ spl26_100 ),
    inference(avatar_split_clause,[],[f2211,f846,f2219])).

fof(f2219,plain,
    ( spl26_294
  <=> v1_zfmisc_1(sK12(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_294])])).

fof(f2211,plain,
    ( v1_zfmisc_1(sK12(sK17))
    | ~ spl26_100 ),
    inference(resolution,[],[f855,f292])).

fof(f2199,plain,
    ( spl26_292
    | ~ spl26_98 ),
    inference(avatar_split_clause,[],[f2192,f807,f2197])).

fof(f2197,plain,
    ( spl26_292
  <=> v1_relat_1(sK10(sK6(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_292])])).

fof(f2192,plain,
    ( v1_relat_1(sK10(sK6(sK17)))
    | ~ spl26_98 ),
    inference(resolution,[],[f812,f289])).

fof(f812,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK6(sK17))
        | v1_relat_1(X2) )
    | ~ spl26_98 ),
    inference(resolution,[],[f808,f246])).

fof(f2190,plain,
    ( spl26_290
    | ~ spl26_98 ),
    inference(avatar_split_clause,[],[f2183,f807,f2188])).

fof(f2188,plain,
    ( spl26_290
  <=> v1_funct_1(sK10(sK6(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_290])])).

fof(f2183,plain,
    ( v1_funct_1(sK10(sK6(sK17)))
    | ~ spl26_98 ),
    inference(resolution,[],[f811,f289])).

fof(f811,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK6(sK17))
        | v1_funct_1(X1) )
    | ~ spl26_98 ),
    inference(resolution,[],[f808,f247])).

fof(f2181,plain,
    ( spl26_288
    | ~ spl26_96 ),
    inference(avatar_split_clause,[],[f2174,f797,f2179])).

fof(f2179,plain,
    ( spl26_288
  <=> v1_relat_1(sK10(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_288])])).

fof(f2174,plain,
    ( v1_relat_1(sK10(sK5(sK17)))
    | ~ spl26_96 ),
    inference(resolution,[],[f802,f289])).

fof(f802,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK5(sK17))
        | v1_relat_1(X2) )
    | ~ spl26_96 ),
    inference(resolution,[],[f798,f246])).

fof(f2170,plain,
    ( spl26_286
    | ~ spl26_96 ),
    inference(avatar_split_clause,[],[f2153,f797,f2168])).

fof(f2168,plain,
    ( spl26_286
  <=> v1_funct_1(sK10(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_286])])).

fof(f2153,plain,
    ( v1_funct_1(sK10(sK5(sK17)))
    | ~ spl26_96 ),
    inference(resolution,[],[f801,f289])).

fof(f801,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK5(sK17))
        | v1_funct_1(X1) )
    | ~ spl26_96 ),
    inference(resolution,[],[f798,f247])).

fof(f2151,plain,
    ( spl26_284
    | ~ spl26_94 ),
    inference(avatar_split_clause,[],[f2144,f787,f2149])).

fof(f2149,plain,
    ( spl26_284
  <=> v1_relat_1(sK10(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_284])])).

fof(f2144,plain,
    ( v1_relat_1(sK10(sK4(sK17)))
    | ~ spl26_94 ),
    inference(resolution,[],[f792,f289])).

fof(f792,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK17))
        | v1_relat_1(X2) )
    | ~ spl26_94 ),
    inference(resolution,[],[f788,f246])).

fof(f2142,plain,
    ( spl26_282
    | ~ spl26_94 ),
    inference(avatar_split_clause,[],[f2135,f787,f2140])).

fof(f2140,plain,
    ( spl26_282
  <=> v1_funct_1(sK10(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_282])])).

fof(f2135,plain,
    ( v1_funct_1(sK10(sK4(sK17)))
    | ~ spl26_94 ),
    inference(resolution,[],[f791,f289])).

fof(f791,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK17))
        | v1_funct_1(X1) )
    | ~ spl26_94 ),
    inference(resolution,[],[f788,f247])).

fof(f2133,plain,
    ( spl26_280
    | ~ spl26_92 ),
    inference(avatar_split_clause,[],[f2126,f777,f2131])).

fof(f2131,plain,
    ( spl26_280
  <=> v1_relat_1(sK10(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_280])])).

fof(f2126,plain,
    ( v1_relat_1(sK10(sK3(sK17)))
    | ~ spl26_92 ),
    inference(resolution,[],[f782,f289])).

fof(f782,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK17))
        | v1_relat_1(X2) )
    | ~ spl26_92 ),
    inference(resolution,[],[f778,f246])).

fof(f2124,plain,
    ( spl26_278
    | ~ spl26_92 ),
    inference(avatar_split_clause,[],[f2117,f777,f2122])).

fof(f2122,plain,
    ( spl26_278
  <=> v1_funct_1(sK10(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_278])])).

fof(f2117,plain,
    ( v1_funct_1(sK10(sK3(sK17)))
    | ~ spl26_92 ),
    inference(resolution,[],[f781,f289])).

fof(f781,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK17))
        | v1_funct_1(X1) )
    | ~ spl26_92 ),
    inference(resolution,[],[f778,f247])).

fof(f2115,plain,
    ( spl26_276
    | ~ spl26_88 ),
    inference(avatar_split_clause,[],[f2108,f760,f2113])).

fof(f2113,plain,
    ( spl26_276
  <=> v1_relat_1(sK10(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_276])])).

fof(f2108,plain,
    ( v1_relat_1(sK10(sK12(sK17)))
    | ~ spl26_88 ),
    inference(resolution,[],[f765,f289])).

fof(f765,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK12(sK17))
        | v1_relat_1(X2) )
    | ~ spl26_88 ),
    inference(resolution,[],[f761,f246])).

fof(f2106,plain,
    ( spl26_274
    | ~ spl26_88 ),
    inference(avatar_split_clause,[],[f2099,f760,f2104])).

fof(f2104,plain,
    ( spl26_274
  <=> v1_funct_1(sK10(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_274])])).

fof(f2099,plain,
    ( v1_funct_1(sK10(sK12(sK17)))
    | ~ spl26_88 ),
    inference(resolution,[],[f764,f289])).

fof(f764,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK12(sK17))
        | v1_funct_1(X1) )
    | ~ spl26_88 ),
    inference(resolution,[],[f761,f247])).

fof(f2039,plain,
    ( spl26_268
    | spl26_272
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1937,f521,f2037,f2022])).

fof(f2037,plain,
    ( spl26_272
  <=> v1_relat_1(sK9(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_272])])).

fof(f1937,plain,
    ( v1_relat_1(sK9(sK25))
    | v1_zfmisc_1(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f345])).

fof(f912,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(sK25))
        | v1_relat_1(X17) )
    | ~ spl26_48 ),
    inference(resolution,[],[f250,f522])).

fof(f2030,plain,
    ( spl26_268
    | spl26_270
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1936,f521,f2028,f2022])).

fof(f2028,plain,
    ( spl26_270
  <=> v1_relat_1(sK8(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_270])])).

fof(f1936,plain,
    ( v1_relat_1(sK8(sK25))
    | v1_zfmisc_1(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f341])).

fof(f2016,plain,
    ( spl26_258
    | spl26_266
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1935,f521,f2014,f1984])).

fof(f2014,plain,
    ( spl26_266
  <=> v1_relat_1(sK6(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_266])])).

fof(f1935,plain,
    ( v1_relat_1(sK6(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f242])).

fof(f2008,plain,
    ( spl26_258
    | spl26_264
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1934,f521,f2006,f1984])).

fof(f2006,plain,
    ( spl26_264
  <=> v1_relat_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_264])])).

fof(f1934,plain,
    ( v1_relat_1(sK5(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f239])).

fof(f2000,plain,
    ( spl26_258
    | spl26_262
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1933,f521,f1998,f1984])).

fof(f1998,plain,
    ( spl26_262
  <=> v1_relat_1(sK4(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_262])])).

fof(f1933,plain,
    ( v1_relat_1(sK4(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f236])).

fof(f1992,plain,
    ( spl26_258
    | spl26_260
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1932,f521,f1990,f1984])).

fof(f1990,plain,
    ( spl26_260
  <=> v1_relat_1(sK3(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_260])])).

fof(f1932,plain,
    ( v1_relat_1(sK3(sK25))
    | v1_xboole_0(sK25)
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f234])).

fof(f1956,plain,
    ( spl26_256
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1938,f521,f1954])).

fof(f1954,plain,
    ( spl26_256
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_256])])).

fof(f1938,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f289])).

fof(f1948,plain,
    ( spl26_254
    | ~ spl26_48 ),
    inference(avatar_split_clause,[],[f1940,f521,f1946])).

fof(f1946,plain,
    ( spl26_254
  <=> v1_relat_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_254])])).

fof(f1940,plain,
    ( v1_relat_1(sK12(sK25))
    | ~ spl26_48 ),
    inference(resolution,[],[f912,f292])).

fof(f1891,plain,
    ( spl26_252
    | ~ spl26_42
    | spl26_155 ),
    inference(avatar_split_clause,[],[f1828,f1203,f500,f1889])).

fof(f1889,plain,
    ( spl26_252
  <=> v1_relat_1(sK9(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_252])])).

fof(f1828,plain,
    ( v1_relat_1(sK9(sK24))
    | ~ spl26_42
    | ~ spl26_155 ),
    inference(subsumption_resolution,[],[f1819,f1204])).

fof(f1819,plain,
    ( v1_relat_1(sK9(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f345])).

fof(f911,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(sK24))
        | v1_relat_1(X16) )
    | ~ spl26_42 ),
    inference(resolution,[],[f250,f501])).

fof(f1883,plain,
    ( spl26_250
    | ~ spl26_42
    | spl26_155 ),
    inference(avatar_split_clause,[],[f1827,f1203,f500,f1881])).

fof(f1881,plain,
    ( spl26_250
  <=> v1_relat_1(sK8(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_250])])).

fof(f1827,plain,
    ( v1_relat_1(sK8(sK24))
    | ~ spl26_42
    | ~ spl26_155 ),
    inference(subsumption_resolution,[],[f1818,f1204])).

fof(f1818,plain,
    ( v1_relat_1(sK8(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f341])).

fof(f1875,plain,
    ( spl26_248
    | ~ spl26_42
    | spl26_63 ),
    inference(avatar_split_clause,[],[f1826,f575,f500,f1873])).

fof(f1873,plain,
    ( spl26_248
  <=> v1_relat_1(sK6(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_248])])).

fof(f1826,plain,
    ( v1_relat_1(sK6(sK24))
    | ~ spl26_42
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f1817,f576])).

fof(f1817,plain,
    ( v1_relat_1(sK6(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f242])).

fof(f1867,plain,
    ( spl26_246
    | ~ spl26_42
    | spl26_63 ),
    inference(avatar_split_clause,[],[f1825,f575,f500,f1865])).

fof(f1865,plain,
    ( spl26_246
  <=> v1_relat_1(sK5(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_246])])).

fof(f1825,plain,
    ( v1_relat_1(sK5(sK24))
    | ~ spl26_42
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f1816,f576])).

fof(f1816,plain,
    ( v1_relat_1(sK5(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f239])).

fof(f1859,plain,
    ( spl26_244
    | ~ spl26_42
    | spl26_63 ),
    inference(avatar_split_clause,[],[f1824,f575,f500,f1857])).

fof(f1857,plain,
    ( spl26_244
  <=> v1_relat_1(sK4(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_244])])).

fof(f1824,plain,
    ( v1_relat_1(sK4(sK24))
    | ~ spl26_42
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f1815,f576])).

fof(f1815,plain,
    ( v1_relat_1(sK4(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f236])).

fof(f1851,plain,
    ( spl26_242
    | ~ spl26_42
    | spl26_63 ),
    inference(avatar_split_clause,[],[f1823,f575,f500,f1849])).

fof(f1849,plain,
    ( spl26_242
  <=> v1_relat_1(sK3(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_242])])).

fof(f1823,plain,
    ( v1_relat_1(sK3(sK24))
    | ~ spl26_42
    | ~ spl26_63 ),
    inference(subsumption_resolution,[],[f1814,f576])).

fof(f1814,plain,
    ( v1_relat_1(sK3(sK24))
    | v1_xboole_0(sK24)
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f234])).

fof(f1844,plain,
    ( spl26_240
    | ~ spl26_42 ),
    inference(avatar_split_clause,[],[f1820,f500,f1842])).

fof(f1842,plain,
    ( spl26_240
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_240])])).

fof(f1820,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK24)))
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f289])).

fof(f1836,plain,
    ( spl26_238
    | ~ spl26_42 ),
    inference(avatar_split_clause,[],[f1822,f500,f1834])).

fof(f1834,plain,
    ( spl26_238
  <=> v1_relat_1(sK12(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_238])])).

fof(f1822,plain,
    ( v1_relat_1(sK12(sK24))
    | ~ spl26_42 ),
    inference(resolution,[],[f911,f292])).

fof(f1810,plain,
    ( spl26_232
    | spl26_236
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1680,f486,f1808,f1794])).

fof(f1808,plain,
    ( spl26_236
  <=> v1_relat_1(sK9(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_236])])).

fof(f1680,plain,
    ( v1_relat_1(sK9(sK23))
    | v1_zfmisc_1(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f345])).

fof(f910,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(sK23))
        | v1_relat_1(X15) )
    | ~ spl26_38 ),
    inference(resolution,[],[f250,f487])).

fof(f1802,plain,
    ( spl26_232
    | spl26_234
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1679,f486,f1800,f1794])).

fof(f1800,plain,
    ( spl26_234
  <=> v1_relat_1(sK8(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_234])])).

fof(f1679,plain,
    ( v1_relat_1(sK8(sK23))
    | v1_zfmisc_1(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f341])).

fof(f1788,plain,
    ( spl26_220
    | spl26_230
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1678,f486,f1786,f1727])).

fof(f1727,plain,
    ( spl26_220
  <=> v1_xboole_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_220])])).

fof(f1786,plain,
    ( spl26_230
  <=> v1_relat_1(sK6(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_230])])).

fof(f1678,plain,
    ( v1_relat_1(sK6(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f242])).

fof(f1780,plain,
    ( spl26_228
    | ~ spl26_220 ),
    inference(avatar_split_clause,[],[f1754,f1727,f1778])).

fof(f1778,plain,
    ( spl26_228
  <=> k1_xboole_0 = sK23 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_228])])).

fof(f1754,plain,
    ( k1_xboole_0 = sK23
    | ~ spl26_220 ),
    inference(resolution,[],[f1728,f256])).

fof(f1728,plain,
    ( v1_xboole_0(sK23)
    | ~ spl26_220 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f1751,plain,
    ( spl26_220
    | spl26_226
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1677,f486,f1749,f1727])).

fof(f1749,plain,
    ( spl26_226
  <=> v1_relat_1(sK5(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_226])])).

fof(f1677,plain,
    ( v1_relat_1(sK5(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f239])).

fof(f1743,plain,
    ( spl26_220
    | spl26_224
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1676,f486,f1741,f1727])).

fof(f1741,plain,
    ( spl26_224
  <=> v1_relat_1(sK4(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_224])])).

fof(f1676,plain,
    ( v1_relat_1(sK4(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f236])).

fof(f1735,plain,
    ( spl26_220
    | spl26_222
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1675,f486,f1733,f1727])).

fof(f1733,plain,
    ( spl26_222
  <=> v1_relat_1(sK3(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_222])])).

fof(f1675,plain,
    ( v1_relat_1(sK3(sK23))
    | v1_xboole_0(sK23)
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f234])).

fof(f1699,plain,
    ( spl26_218
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1681,f486,f1697])).

fof(f1697,plain,
    ( spl26_218
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_218])])).

fof(f1681,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK23)))
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f289])).

fof(f1691,plain,
    ( spl26_216
    | ~ spl26_38 ),
    inference(avatar_split_clause,[],[f1683,f486,f1689])).

fof(f1689,plain,
    ( spl26_216
  <=> v1_relat_1(sK12(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_216])])).

fof(f1683,plain,
    ( v1_relat_1(sK12(sK23))
    | ~ spl26_38 ),
    inference(resolution,[],[f910,f292])).

fof(f1671,plain,
    ( spl26_210
    | spl26_214
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1417,f472,f1669,f1565])).

fof(f1669,plain,
    ( spl26_214
  <=> v1_relat_1(sK9(sK22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_214])])).

fof(f1417,plain,
    ( v1_relat_1(sK9(sK22))
    | v1_zfmisc_1(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f345])).

fof(f909,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(sK22))
        | v1_relat_1(X14) )
    | ~ spl26_34 ),
    inference(resolution,[],[f250,f473])).

fof(f1660,plain,
    ( spl26_74
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1459,f472,f625])).

fof(f625,plain,
    ( spl26_74
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_74])])).

fof(f1459,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl26_34 ),
    inference(superposition,[],[f1449,f672])).

fof(f672,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f296,f230])).

fof(f1449,plain,
    ( ! [X1] : v1_relat_1(k3_xboole_0(X1,sK22))
    | ~ spl26_34 ),
    inference(resolution,[],[f1410,f676])).

fof(f676,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X5,X4),X4) ),
    inference(superposition,[],[f295,f296])).

fof(f1410,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK22)
        | v1_relat_1(X0) )
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f302])).

fof(f1659,plain,
    ( ~ spl26_24
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1578])).

fof(f1578,plain,
    ( $false
    | ~ spl26_24
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1027])).

fof(f1027,plain,
    ( ! [X1] : v1_relat_1(k3_xboole_0(X1,sK19))
    | ~ spl26_24 ),
    inference(resolution,[],[f952,f676])).

fof(f952,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK19)
        | v1_relat_1(X0) )
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f302])).

fof(f906,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK19))
        | v1_relat_1(X11) )
    | ~ spl26_24 ),
    inference(resolution,[],[f250,f438])).

fof(f438,plain,
    ( v1_relat_1(sK19)
    | ~ spl26_24 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl26_24
  <=> v1_relat_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_24])])).

fof(f620,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl26_72 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl26_72
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_72])])).

fof(f1658,plain,
    ( ~ spl26_28
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1579])).

fof(f1579,plain,
    ( $false
    | ~ spl26_28
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1227])).

fof(f1227,plain,
    ( ! [X1] : v1_relat_1(k3_xboole_0(X1,sK20))
    | ~ spl26_28 ),
    inference(resolution,[],[f1141,f676])).

fof(f1141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK20)
        | v1_relat_1(X0) )
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f302])).

fof(f907,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(sK20))
        | v1_relat_1(X12) )
    | ~ spl26_28 ),
    inference(resolution,[],[f250,f452])).

fof(f1657,plain,
    ( ~ spl26_32
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1580])).

fof(f1580,plain,
    ( $false
    | ~ spl26_32
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1298])).

fof(f1298,plain,
    ( ! [X1] : v1_relat_1(k3_xboole_0(X1,sK21))
    | ~ spl26_32 ),
    inference(resolution,[],[f1259,f676])).

fof(f1259,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK21)
        | v1_relat_1(X0) )
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f302])).

fof(f908,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(sK21))
        | v1_relat_1(X13) )
    | ~ spl26_32 ),
    inference(resolution,[],[f250,f466])).

fof(f466,plain,
    ( v1_relat_1(sK21)
    | ~ spl26_32 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl26_32
  <=> v1_relat_1(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_32])])).

fof(f1656,plain,
    ( ~ spl26_34
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl26_34
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1449])).

fof(f1655,plain,
    ( ~ spl26_24
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1582])).

fof(f1582,plain,
    ( $false
    | ~ spl26_24
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1017])).

fof(f1017,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK19,X0))
    | ~ spl26_24 ),
    inference(resolution,[],[f952,f295])).

fof(f1654,plain,
    ( ~ spl26_28
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1583])).

fof(f1583,plain,
    ( $false
    | ~ spl26_28
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1217])).

fof(f1217,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK20,X0))
    | ~ spl26_28 ),
    inference(resolution,[],[f1141,f295])).

fof(f1653,plain,
    ( ~ spl26_32
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1584])).

fof(f1584,plain,
    ( $false
    | ~ spl26_32
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1288])).

fof(f1288,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK21,X0))
    | ~ spl26_32 ),
    inference(resolution,[],[f1259,f295])).

fof(f1652,plain,
    ( ~ spl26_34
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1585])).

fof(f1585,plain,
    ( $false
    | ~ spl26_34
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f1439])).

fof(f1439,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK22,X0))
    | ~ spl26_34 ),
    inference(resolution,[],[f1410,f295])).

fof(f1651,plain,
    ( ~ spl26_72
    | ~ spl26_176 ),
    inference(avatar_contradiction_clause,[],[f1586])).

fof(f1586,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_176 ),
    inference(resolution,[],[f620,f1363])).

fof(f1363,plain,
    ( v1_relat_1(sK3(k1_xboole_0))
    | ~ spl26_176 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f1362,plain,
    ( spl26_176
  <=> v1_relat_1(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_176])])).

fof(f1650,plain,
    ( ~ spl26_72
    | ~ spl26_120 ),
    inference(avatar_contradiction_clause,[],[f1587])).

fof(f1587,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_120 ),
    inference(resolution,[],[f620,f988])).

fof(f1649,plain,
    ( ~ spl26_72
    | ~ spl26_148 ),
    inference(avatar_contradiction_clause,[],[f1588])).

fof(f1588,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_148 ),
    inference(resolution,[],[f620,f1177])).

fof(f1648,plain,
    ( ~ spl26_72
    | ~ spl26_170 ),
    inference(avatar_contradiction_clause,[],[f1589])).

fof(f1589,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_170 ),
    inference(resolution,[],[f620,f1320])).

fof(f1647,plain,
    ( ~ spl26_72
    | ~ spl26_196 ),
    inference(avatar_contradiction_clause,[],[f1590])).

fof(f1590,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_196 ),
    inference(resolution,[],[f620,f1471])).

fof(f1646,plain,
    ( ~ spl26_72
    | ~ spl26_206 ),
    inference(avatar_contradiction_clause,[],[f1591])).

fof(f1591,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_206 ),
    inference(resolution,[],[f620,f1551])).

fof(f1551,plain,
    ( v1_relat_1(sK4(k1_xboole_0))
    | ~ spl26_206 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f1550,plain,
    ( spl26_206
  <=> v1_relat_1(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_206])])).

fof(f1645,plain,
    ( ~ spl26_72
    | ~ spl26_122 ),
    inference(avatar_contradiction_clause,[],[f1592])).

fof(f1592,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_122 ),
    inference(resolution,[],[f620,f996])).

fof(f1644,plain,
    ( ~ spl26_72
    | ~ spl26_150 ),
    inference(avatar_contradiction_clause,[],[f1593])).

fof(f1593,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_150 ),
    inference(resolution,[],[f620,f1185])).

fof(f1643,plain,
    ( ~ spl26_72
    | ~ spl26_174 ),
    inference(avatar_contradiction_clause,[],[f1594])).

fof(f1594,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_174 ),
    inference(resolution,[],[f620,f1343])).

fof(f1642,plain,
    ( ~ spl26_72
    | ~ spl26_200 ),
    inference(avatar_contradiction_clause,[],[f1595])).

fof(f1595,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_200 ),
    inference(resolution,[],[f620,f1493])).

fof(f1641,plain,
    ( ~ spl26_72
    | ~ spl26_124 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_124 ),
    inference(resolution,[],[f620,f1004])).

fof(f1640,plain,
    ( ~ spl26_72
    | ~ spl26_152 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_152 ),
    inference(resolution,[],[f620,f1193])).

fof(f1639,plain,
    ( ~ spl26_72
    | ~ spl26_180 ),
    inference(avatar_contradiction_clause,[],[f1598])).

fof(f1598,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_180 ),
    inference(resolution,[],[f620,f1380])).

fof(f1638,plain,
    ( ~ spl26_72
    | ~ spl26_126 ),
    inference(avatar_contradiction_clause,[],[f1599])).

fof(f1599,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_126 ),
    inference(resolution,[],[f620,f1012])).

fof(f1637,plain,
    ( ~ spl26_72
    | ~ spl26_156 ),
    inference(avatar_contradiction_clause,[],[f1600])).

fof(f1600,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_156 ),
    inference(resolution,[],[f620,f1212])).

fof(f1636,plain,
    ( ~ spl26_72
    | ~ spl26_182 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_182 ),
    inference(resolution,[],[f620,f1387])).

fof(f1635,plain,
    ( ~ spl26_72
    | ~ spl26_76 ),
    inference(avatar_contradiction_clause,[],[f1602])).

fof(f1602,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_76 ),
    inference(resolution,[],[f620,f640])).

fof(f1634,plain,
    ( ~ spl26_72
    | ~ spl26_78 ),
    inference(avatar_contradiction_clause,[],[f1603])).

fof(f1603,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_78 ),
    inference(resolution,[],[f620,f648])).

fof(f648,plain,
    ( v1_relat_1(sK10(k1_xboole_0))
    | ~ spl26_78 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl26_78
  <=> v1_relat_1(sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_78])])).

fof(f1633,plain,
    ( ~ spl26_72
    | ~ spl26_118 ),
    inference(avatar_contradiction_clause,[],[f1604])).

fof(f1604,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_118 ),
    inference(resolution,[],[f620,f981])).

fof(f981,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK19)))
    | ~ spl26_118 ),
    inference(avatar_component_clause,[],[f980])).

fof(f980,plain,
    ( spl26_118
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_118])])).

fof(f1632,plain,
    ( ~ spl26_72
    | ~ spl26_146 ),
    inference(avatar_contradiction_clause,[],[f1605])).

fof(f1605,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_146 ),
    inference(resolution,[],[f620,f1170])).

fof(f1170,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK20)))
    | ~ spl26_146 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f1169,plain,
    ( spl26_146
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_146])])).

fof(f1631,plain,
    ( ~ spl26_72
    | ~ spl26_166 ),
    inference(avatar_contradiction_clause,[],[f1606])).

fof(f1606,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_166 ),
    inference(resolution,[],[f620,f1284])).

fof(f1284,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK21)))
    | ~ spl26_166 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f1283,plain,
    ( spl26_166
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK21))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_166])])).

fof(f1630,plain,
    ( ~ spl26_72
    | ~ spl26_192 ),
    inference(avatar_contradiction_clause,[],[f1607])).

fof(f1607,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_192 ),
    inference(resolution,[],[f620,f1435])).

fof(f1435,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK22)))
    | ~ spl26_192 ),
    inference(avatar_component_clause,[],[f1434])).

fof(f1434,plain,
    ( spl26_192
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_192])])).

fof(f1629,plain,
    ( ~ spl26_72
    | ~ spl26_116 ),
    inference(avatar_contradiction_clause,[],[f1608])).

fof(f1608,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_116 ),
    inference(resolution,[],[f620,f973])).

fof(f1628,plain,
    ( ~ spl26_72
    | ~ spl26_144 ),
    inference(avatar_contradiction_clause,[],[f1609])).

fof(f1609,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_144 ),
    inference(resolution,[],[f620,f1162])).

fof(f1627,plain,
    ( ~ spl26_72
    | ~ spl26_164 ),
    inference(avatar_contradiction_clause,[],[f1610])).

fof(f1610,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_164 ),
    inference(resolution,[],[f620,f1276])).

fof(f1626,plain,
    ( ~ spl26_72
    | ~ spl26_190 ),
    inference(avatar_contradiction_clause,[],[f1611])).

fof(f1611,plain,
    ( $false
    | ~ spl26_72
    | ~ spl26_190 ),
    inference(resolution,[],[f620,f1427])).

fof(f1625,plain,
    ( ~ spl26_24
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1612])).

fof(f1612,plain,
    ( $false
    | ~ spl26_24
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f438])).

fof(f1624,plain,
    ( ~ spl26_28
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1613])).

fof(f1613,plain,
    ( $false
    | ~ spl26_28
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f452])).

fof(f1623,plain,
    ( ~ spl26_32
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1614])).

fof(f1614,plain,
    ( $false
    | ~ spl26_32
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f466])).

fof(f1622,plain,
    ( ~ spl26_34
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1615])).

fof(f1615,plain,
    ( $false
    | ~ spl26_34
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f473])).

fof(f1621,plain,
    ( ~ spl26_38
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1616])).

fof(f1616,plain,
    ( $false
    | ~ spl26_38
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f487])).

fof(f1620,plain,
    ( ~ spl26_42
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1617])).

fof(f1617,plain,
    ( $false
    | ~ spl26_42
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f501])).

fof(f1619,plain,
    ( ~ spl26_48
    | ~ spl26_72 ),
    inference(avatar_contradiction_clause,[],[f1618])).

fof(f1618,plain,
    ( $false
    | ~ spl26_48
    | ~ spl26_72 ),
    inference(resolution,[],[f620,f522])).

fof(f1573,plain,
    ( spl26_210
    | spl26_212
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1416,f472,f1571,f1565])).

fof(f1416,plain,
    ( v1_relat_1(sK8(sK22))
    | v1_zfmisc_1(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f341])).

fof(f1560,plain,
    ( spl26_194
    | spl26_208
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1415,f472,f1558,f1464])).

fof(f1464,plain,
    ( spl26_194
  <=> v1_xboole_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_194])])).

fof(f1415,plain,
    ( v1_relat_1(sK6(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f242])).

fof(f1552,plain,
    ( spl26_206
    | ~ spl26_198
    | ~ spl26_200 ),
    inference(avatar_split_clause,[],[f1539,f1492,f1482,f1550])).

fof(f1482,plain,
    ( spl26_198
  <=> k1_xboole_0 = sK22 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_198])])).

fof(f1539,plain,
    ( v1_relat_1(sK4(k1_xboole_0))
    | ~ spl26_198
    | ~ spl26_200 ),
    inference(superposition,[],[f1493,f1483])).

fof(f1483,plain,
    ( k1_xboole_0 = sK22
    | ~ spl26_198 ),
    inference(avatar_component_clause,[],[f1482])).

fof(f1544,plain,
    ( spl26_176
    | ~ spl26_196
    | ~ spl26_198 ),
    inference(avatar_split_clause,[],[f1538,f1482,f1470,f1362])).

fof(f1538,plain,
    ( v1_relat_1(sK3(k1_xboole_0))
    | ~ spl26_196
    | ~ spl26_198 ),
    inference(superposition,[],[f1471,f1483])).

fof(f1523,plain,
    ( spl26_194
    | spl26_204
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1414,f472,f1521,f1464])).

fof(f1414,plain,
    ( v1_relat_1(sK5(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f239])).

fof(f1514,plain,
    ( spl26_202
    | ~ spl26_36
    | ~ spl26_198 ),
    inference(avatar_split_clause,[],[f1497,f1482,f479,f1512])).

fof(f1497,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl26_36
    | ~ spl26_198 ),
    inference(superposition,[],[f480,f1483])).

fof(f1494,plain,
    ( spl26_194
    | spl26_200
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1413,f472,f1492,f1464])).

fof(f1413,plain,
    ( v1_relat_1(sK4(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f236])).

fof(f1484,plain,
    ( spl26_198
    | ~ spl26_194 ),
    inference(avatar_split_clause,[],[f1475,f1464,f1482])).

fof(f1475,plain,
    ( k1_xboole_0 = sK22
    | ~ spl26_194 ),
    inference(resolution,[],[f1465,f256])).

fof(f1465,plain,
    ( v1_xboole_0(sK22)
    | ~ spl26_194 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f1472,plain,
    ( spl26_194
    | spl26_196
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1412,f472,f1470,f1464])).

fof(f1412,plain,
    ( v1_relat_1(sK3(sK22))
    | v1_xboole_0(sK22)
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f234])).

fof(f1436,plain,
    ( spl26_192
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1418,f472,f1434])).

fof(f1418,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK22)))
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f289])).

fof(f1428,plain,
    ( spl26_190
    | ~ spl26_34 ),
    inference(avatar_split_clause,[],[f1420,f472,f1426])).

fof(f1420,plain,
    ( v1_relat_1(sK12(sK22))
    | ~ spl26_34 ),
    inference(resolution,[],[f909,f292])).

fof(f1409,plain,
    ( spl26_184
    | spl26_188
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1266,f465,f1407,f1393])).

fof(f1407,plain,
    ( spl26_188
  <=> v1_relat_1(sK9(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_188])])).

fof(f1266,plain,
    ( v1_relat_1(sK9(sK21))
    | v1_zfmisc_1(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f345])).

fof(f1401,plain,
    ( spl26_184
    | spl26_186
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1265,f465,f1399,f1393])).

fof(f1399,plain,
    ( spl26_186
  <=> v1_relat_1(sK8(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_186])])).

fof(f1265,plain,
    ( v1_relat_1(sK8(sK21))
    | v1_zfmisc_1(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f341])).

fof(f1388,plain,
    ( spl26_168
    | spl26_182
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1264,f465,f1386,f1313])).

fof(f1313,plain,
    ( spl26_168
  <=> v1_xboole_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_168])])).

fof(f1264,plain,
    ( v1_relat_1(sK6(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f242])).

fof(f1381,plain,
    ( spl26_168
    | spl26_180
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1263,f465,f1379,f1313])).

fof(f1263,plain,
    ( v1_relat_1(sK5(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f239])).

fof(f1374,plain,
    ( ~ spl26_179
    | spl26_177 ),
    inference(avatar_split_clause,[],[f1367,f1359,f1372])).

fof(f1372,plain,
    ( spl26_179
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_179])])).

fof(f1359,plain,
    ( spl26_177
  <=> ~ v1_relat_1(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_177])])).

fof(f1367,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl26_177 ),
    inference(resolution,[],[f1360,f255])).

fof(f1360,plain,
    ( ~ v1_relat_1(sK3(k1_xboole_0))
    | ~ spl26_177 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1366,plain,
    ( ~ spl26_177
    | spl26_171
    | ~ spl26_172 ),
    inference(avatar_split_clause,[],[f1365,f1331,f1316,f1359])).

fof(f1316,plain,
    ( spl26_171
  <=> ~ v1_relat_1(sK3(sK21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_171])])).

fof(f1331,plain,
    ( spl26_172
  <=> k1_xboole_0 = sK21 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_172])])).

fof(f1365,plain,
    ( ~ v1_relat_1(sK3(k1_xboole_0))
    | ~ spl26_171
    | ~ spl26_172 ),
    inference(forward_demodulation,[],[f1317,f1332])).

fof(f1332,plain,
    ( k1_xboole_0 = sK21
    | ~ spl26_172 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1317,plain,
    ( ~ v1_relat_1(sK3(sK21))
    | ~ spl26_171 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1364,plain,
    ( spl26_176
    | ~ spl26_170
    | ~ spl26_172 ),
    inference(avatar_split_clause,[],[f1353,f1331,f1319,f1362])).

fof(f1353,plain,
    ( v1_relat_1(sK3(k1_xboole_0))
    | ~ spl26_170
    | ~ spl26_172 ),
    inference(superposition,[],[f1320,f1332])).

fof(f1344,plain,
    ( spl26_168
    | spl26_174
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1262,f465,f1342,f1313])).

fof(f1262,plain,
    ( v1_relat_1(sK4(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f236])).

fof(f1333,plain,
    ( spl26_172
    | ~ spl26_168 ),
    inference(avatar_split_clause,[],[f1324,f1313,f1331])).

fof(f1324,plain,
    ( k1_xboole_0 = sK21
    | ~ spl26_168 ),
    inference(resolution,[],[f1314,f256])).

fof(f1314,plain,
    ( v1_xboole_0(sK21)
    | ~ spl26_168 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f1321,plain,
    ( spl26_168
    | spl26_170
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1261,f465,f1319,f1313])).

fof(f1261,plain,
    ( v1_relat_1(sK3(sK21))
    | v1_xboole_0(sK21)
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f234])).

fof(f1285,plain,
    ( spl26_166
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1267,f465,f1283])).

fof(f1267,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK21)))
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f289])).

fof(f1277,plain,
    ( spl26_164
    | ~ spl26_32 ),
    inference(avatar_split_clause,[],[f1269,f465,f1275])).

fof(f1269,plain,
    ( v1_relat_1(sK12(sK21))
    | ~ spl26_32 ),
    inference(resolution,[],[f908,f292])).

fof(f1258,plain,
    ( spl26_158
    | spl26_162
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1148,f451,f1256,f1242])).

fof(f1256,plain,
    ( spl26_162
  <=> v1_relat_1(sK9(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_162])])).

fof(f1148,plain,
    ( v1_relat_1(sK9(sK20))
    | v1_zfmisc_1(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f345])).

fof(f1250,plain,
    ( spl26_158
    | spl26_160
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1147,f451,f1248,f1242])).

fof(f1248,plain,
    ( spl26_160
  <=> v1_relat_1(sK8(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_160])])).

fof(f1147,plain,
    ( v1_relat_1(sK8(sK20))
    | v1_zfmisc_1(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f341])).

fof(f1213,plain,
    ( spl26_156
    | spl26_27
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1155,f451,f444,f1211])).

fof(f1155,plain,
    ( v1_relat_1(sK6(sK20))
    | ~ spl26_27
    | ~ spl26_28 ),
    inference(subsumption_resolution,[],[f1146,f445])).

fof(f1146,plain,
    ( v1_relat_1(sK6(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f242])).

fof(f1205,plain,
    ( ~ spl26_155
    | ~ spl26_42
    | ~ spl26_44
    | spl26_47 ),
    inference(avatar_split_clause,[],[f1197,f514,f507,f500,f1203])).

fof(f514,plain,
    ( spl26_47
  <=> ~ v3_funct_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_47])])).

fof(f1197,plain,
    ( ~ v1_zfmisc_1(sK24)
    | ~ spl26_42
    | ~ spl26_44
    | ~ spl26_47 ),
    inference(subsumption_resolution,[],[f1196,f501])).

fof(f1196,plain,
    ( ~ v1_relat_1(sK24)
    | ~ v1_zfmisc_1(sK24)
    | ~ spl26_44
    | ~ spl26_47 ),
    inference(subsumption_resolution,[],[f1195,f508])).

fof(f1195,plain,
    ( ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_zfmisc_1(sK24)
    | ~ spl26_47 ),
    inference(resolution,[],[f277,f515])).

fof(f515,plain,
    ( ~ v3_funct_1(sK24)
    | ~ spl26_47 ),
    inference(avatar_component_clause,[],[f514])).

fof(f277,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(flattening,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_zfmisc_1(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc7_funct_1)).

fof(f1194,plain,
    ( spl26_152
    | spl26_27
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1154,f451,f444,f1192])).

fof(f1154,plain,
    ( v1_relat_1(sK5(sK20))
    | ~ spl26_27
    | ~ spl26_28 ),
    inference(subsumption_resolution,[],[f1145,f445])).

fof(f1145,plain,
    ( v1_relat_1(sK5(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f239])).

fof(f1186,plain,
    ( spl26_150
    | spl26_27
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1153,f451,f444,f1184])).

fof(f1153,plain,
    ( v1_relat_1(sK4(sK20))
    | ~ spl26_27
    | ~ spl26_28 ),
    inference(subsumption_resolution,[],[f1144,f445])).

fof(f1144,plain,
    ( v1_relat_1(sK4(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f236])).

fof(f1178,plain,
    ( spl26_148
    | spl26_27
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1152,f451,f444,f1176])).

fof(f1152,plain,
    ( v1_relat_1(sK3(sK20))
    | ~ spl26_27
    | ~ spl26_28 ),
    inference(subsumption_resolution,[],[f1143,f445])).

fof(f1143,plain,
    ( v1_relat_1(sK3(sK20))
    | v1_xboole_0(sK20)
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f234])).

fof(f1171,plain,
    ( spl26_146
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1149,f451,f1169])).

fof(f1149,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK20)))
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f289])).

fof(f1163,plain,
    ( spl26_144
    | ~ spl26_28 ),
    inference(avatar_split_clause,[],[f1151,f451,f1161])).

fof(f1151,plain,
    ( v1_relat_1(sK12(sK20))
    | ~ spl26_28 ),
    inference(resolution,[],[f907,f292])).

fof(f1137,plain,
    ( spl26_142
    | ~ spl26_130 ),
    inference(avatar_split_clause,[],[f1089,f1065,f1135])).

fof(f1135,plain,
    ( spl26_142
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_142])])).

fof(f1065,plain,
    ( spl26_130
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_130])])).

fof(f1089,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl26_130 ),
    inference(resolution,[],[f1066,f256])).

fof(f1066,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl26_130 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1130,plain,
    ( spl26_136
    | spl26_140
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f959,f437,f1128,f1114])).

fof(f1128,plain,
    ( spl26_140
  <=> v1_relat_1(sK9(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_140])])).

fof(f959,plain,
    ( v1_relat_1(sK9(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f345])).

fof(f1122,plain,
    ( spl26_136
    | spl26_138
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f958,f437,f1120,f1114])).

fof(f1120,plain,
    ( spl26_138
  <=> v1_relat_1(sK8(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_138])])).

fof(f958,plain,
    ( v1_relat_1(sK8(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f341])).

fof(f1109,plain,
    ( ~ spl26_135
    | ~ spl26_132 ),
    inference(avatar_split_clause,[],[f1102,f1096,f1107])).

fof(f1107,plain,
    ( spl26_135
  <=> ~ v1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_135])])).

fof(f1096,plain,
    ( spl26_132
  <=> k1_xboole_0 = sK12(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_132])])).

fof(f1102,plain,
    ( ~ v1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl26_132 ),
    inference(superposition,[],[f293,f1097])).

fof(f1097,plain,
    ( k1_xboole_0 = sK12(k1_xboole_0)
    | ~ spl26_132 ),
    inference(avatar_component_clause,[],[f1096])).

fof(f293,plain,(
    ! [X0] : ~ v1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f193])).

fof(f1098,plain,
    ( spl26_132
    | ~ spl26_128 ),
    inference(avatar_split_clause,[],[f1070,f1058,f1096])).

fof(f1058,plain,
    ( spl26_128
  <=> v1_xboole_0(sK12(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_128])])).

fof(f1070,plain,
    ( k1_xboole_0 = sK12(k1_xboole_0)
    | ~ spl26_128 ),
    inference(resolution,[],[f1059,f256])).

fof(f1059,plain,
    ( v1_xboole_0(sK12(k1_xboole_0))
    | ~ spl26_128 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1067,plain,(
    spl26_130 ),
    inference(avatar_split_clause,[],[f1051,f1065])).

fof(f1051,plain,(
    v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f1041,f289])).

fof(f1060,plain,(
    spl26_128 ),
    inference(avatar_split_clause,[],[f1053,f1058])).

fof(f1053,plain,(
    v1_xboole_0(sK12(k1_xboole_0)) ),
    inference(resolution,[],[f1041,f292])).

fof(f1013,plain,
    ( spl26_126
    | spl26_23
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f966,f437,f430,f1011])).

fof(f966,plain,
    ( v1_relat_1(sK6(sK19))
    | ~ spl26_23
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f957,f431])).

fof(f957,plain,
    ( v1_relat_1(sK6(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f242])).

fof(f1005,plain,
    ( spl26_124
    | spl26_23
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f965,f437,f430,f1003])).

fof(f965,plain,
    ( v1_relat_1(sK5(sK19))
    | ~ spl26_23
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f956,f431])).

fof(f956,plain,
    ( v1_relat_1(sK5(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f239])).

fof(f997,plain,
    ( spl26_122
    | spl26_23
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f964,f437,f430,f995])).

fof(f964,plain,
    ( v1_relat_1(sK4(sK19))
    | ~ spl26_23
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f955,f431])).

fof(f955,plain,
    ( v1_relat_1(sK4(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f236])).

fof(f989,plain,
    ( spl26_120
    | spl26_23
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f963,f437,f430,f987])).

fof(f963,plain,
    ( v1_relat_1(sK3(sK19))
    | ~ spl26_23
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f954,f431])).

fof(f954,plain,
    ( v1_relat_1(sK3(sK19))
    | v1_xboole_0(sK19)
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f234])).

fof(f982,plain,
    ( spl26_118
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f960,f437,f980])).

fof(f960,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK19)))
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f289])).

fof(f974,plain,
    ( spl26_116
    | ~ spl26_24 ),
    inference(avatar_split_clause,[],[f962,f437,f972])).

fof(f962,plain,
    ( v1_relat_1(sK12(sK19))
    | ~ spl26_24 ),
    inference(resolution,[],[f906,f292])).

fof(f927,plain,
    ( spl26_114
    | spl26_19
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f875,f423,f416,f925])).

fof(f875,plain,
    ( v1_zfmisc_1(sK6(sK18))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(subsumption_resolution,[],[f868,f417])).

fof(f868,plain,
    ( v1_zfmisc_1(sK6(sK18))
    | v1_xboole_0(sK18)
    | ~ spl26_20 ),
    inference(resolution,[],[f755,f242])).

fof(f919,plain,
    ( spl26_112
    | spl26_19
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f874,f423,f416,f917])).

fof(f874,plain,
    ( v1_zfmisc_1(sK3(sK18))
    | ~ spl26_19
    | ~ spl26_20 ),
    inference(subsumption_resolution,[],[f865,f417])).

fof(f865,plain,
    ( v1_zfmisc_1(sK3(sK18))
    | v1_xboole_0(sK18)
    | ~ spl26_20 ),
    inference(resolution,[],[f755,f234])).

fof(f899,plain,
    ( spl26_110
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f871,f423,f897])).

fof(f897,plain,
    ( spl26_110
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_110])])).

fof(f871,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK18)))
    | ~ spl26_20 ),
    inference(resolution,[],[f755,f289])).

fof(f891,plain,
    ( spl26_108
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f873,f423,f889])).

fof(f873,plain,
    ( v1_zfmisc_1(sK12(sK18))
    | ~ spl26_20 ),
    inference(resolution,[],[f755,f292])).

fof(f883,plain,
    ( spl26_106
    | ~ spl26_20 ),
    inference(avatar_split_clause,[],[f864,f423,f881])).

fof(f881,plain,
    ( spl26_106
  <=> v1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_106])])).

fof(f864,plain,
    ( v1_zfmisc_1(k1_xboole_0)
    | ~ spl26_20 ),
    inference(resolution,[],[f755,f605])).

fof(f862,plain,
    ( spl26_100
    | spl26_104
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f743,f409,f860,f846])).

fof(f860,plain,
    ( spl26_104
  <=> v4_funct_1(sK9(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_104])])).

fof(f409,plain,
    ( spl26_16
  <=> v4_funct_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_16])])).

fof(f743,plain,
    ( v4_funct_1(sK9(sK17))
    | v1_zfmisc_1(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f345])).

fof(f733,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK17))
        | v4_funct_1(X4) )
    | ~ spl26_16 ),
    inference(resolution,[],[f248,f410])).

fof(f410,plain,
    ( v4_funct_1(sK17)
    | ~ spl26_16 ),
    inference(avatar_component_clause,[],[f409])).

fof(f854,plain,
    ( spl26_100
    | spl26_102
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f742,f409,f852,f846])).

fof(f852,plain,
    ( spl26_102
  <=> v4_funct_1(sK8(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_102])])).

fof(f742,plain,
    ( v4_funct_1(sK8(sK17))
    | v1_zfmisc_1(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f341])).

fof(f809,plain,
    ( spl26_98
    | spl26_15
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f750,f409,f402,f807])).

fof(f750,plain,
    ( v4_funct_1(sK6(sK17))
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f741,f403])).

fof(f741,plain,
    ( v4_funct_1(sK6(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f242])).

fof(f799,plain,
    ( spl26_96
    | spl26_15
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f749,f409,f402,f797])).

fof(f749,plain,
    ( v4_funct_1(sK5(sK17))
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f740,f403])).

fof(f740,plain,
    ( v4_funct_1(sK5(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f239])).

fof(f789,plain,
    ( spl26_94
    | spl26_15
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f748,f409,f402,f787])).

fof(f748,plain,
    ( v4_funct_1(sK4(sK17))
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f739,f403])).

fof(f739,plain,
    ( v4_funct_1(sK4(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f236])).

fof(f779,plain,
    ( spl26_92
    | spl26_15
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f747,f409,f402,f777])).

fof(f747,plain,
    ( v4_funct_1(sK3(sK17))
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f738,f403])).

fof(f738,plain,
    ( v4_funct_1(sK3(sK17))
    | v1_xboole_0(sK17)
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f234])).

fof(f772,plain,
    ( spl26_90
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f744,f409,f770])).

fof(f744,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f289])).

fof(f762,plain,
    ( spl26_88
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f746,f409,f760])).

fof(f746,plain,
    ( v4_funct_1(sK12(sK17))
    | ~ spl26_16 ),
    inference(resolution,[],[f733,f292])).

fof(f720,plain,
    ( spl26_86
    | ~ spl26_56 ),
    inference(avatar_split_clause,[],[f698,f549,f718])).

fof(f718,plain,
    ( spl26_86
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_86])])).

fof(f698,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl26_56 ),
    inference(resolution,[],[f301,f550])).

fof(f713,plain,
    ( spl26_84
    | ~ spl26_54 ),
    inference(avatar_split_clause,[],[f697,f542,f711])).

fof(f711,plain,
    ( spl26_84
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_84])])).

fof(f697,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl26_54 ),
    inference(resolution,[],[f301,f543])).

fof(f671,plain,
    ( spl26_82
    | ~ spl26_58 ),
    inference(avatar_split_clause,[],[f664,f560,f669])).

fof(f669,plain,
    ( spl26_82
  <=> v1_funct_1(sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_82])])).

fof(f560,plain,
    ( spl26_58
  <=> v4_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_58])])).

fof(f664,plain,
    ( v1_funct_1(sK10(k1_xboole_0))
    | ~ spl26_58 ),
    inference(resolution,[],[f650,f289])).

fof(f650,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_funct_1(X0) )
    | ~ spl26_58 ),
    inference(resolution,[],[f247,f561])).

fof(f561,plain,
    ( v4_funct_1(k1_xboole_0)
    | ~ spl26_58 ),
    inference(avatar_component_clause,[],[f560])).

fof(f663,plain,
    ( spl26_80
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f656,f409,f661])).

fof(f661,plain,
    ( spl26_80
  <=> v1_funct_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_80])])).

fof(f656,plain,
    ( v1_funct_1(sK10(sK17))
    | ~ spl26_16 ),
    inference(resolution,[],[f653,f289])).

fof(f653,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,sK17)
        | v1_funct_1(X4) )
    | ~ spl26_16 ),
    inference(resolution,[],[f247,f410])).

fof(f649,plain,
    ( spl26_78
    | ~ spl26_58 ),
    inference(avatar_split_clause,[],[f642,f560,f647])).

fof(f642,plain,
    ( v1_relat_1(sK10(k1_xboole_0))
    | ~ spl26_58 ),
    inference(resolution,[],[f628,f289])).

fof(f628,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_relat_1(X0) )
    | ~ spl26_58 ),
    inference(resolution,[],[f246,f561])).

fof(f641,plain,
    ( spl26_76
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f634,f409,f639])).

fof(f634,plain,
    ( v1_relat_1(sK10(sK17))
    | ~ spl26_16 ),
    inference(resolution,[],[f631,f289])).

fof(f631,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,sK17)
        | v1_relat_1(X4) )
    | ~ spl26_16 ),
    inference(resolution,[],[f246,f410])).

fof(f627,plain,
    ( spl26_72
    | spl26_74 ),
    inference(avatar_split_clause,[],[f616,f625,f619])).

fof(f616,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f297,f230])).

fof(f297,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',fc1_relat_1)).

fof(f615,plain,(
    ~ spl26_71 ),
    inference(avatar_split_clause,[],[f225,f613])).

fof(f225,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f103,f172,f171,f170])).

fof(f170,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f171,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',t29_tex_2)).

fof(f602,plain,
    ( spl26_68
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f593,f381,f600])).

fof(f600,plain,
    ( spl26_68
  <=> k1_xboole_0 = sK15 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_68])])).

fof(f381,plain,
    ( spl26_8
  <=> v1_xboole_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_8])])).

fof(f593,plain,
    ( k1_xboole_0 = sK15
    | ~ spl26_8 ),
    inference(resolution,[],[f256,f382])).

fof(f382,plain,
    ( v1_xboole_0(sK15)
    | ~ spl26_8 ),
    inference(avatar_component_clause,[],[f381])).

fof(f590,plain,
    ( spl26_64
    | spl26_66 ),
    inference(avatar_split_clause,[],[f224,f588,f582])).

fof(f224,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f173])).

fof(f577,plain,
    ( ~ spl26_63
    | spl26_47 ),
    inference(avatar_split_clause,[],[f570,f514,f575])).

fof(f570,plain,
    ( ~ v1_xboole_0(sK24)
    | ~ spl26_47 ),
    inference(resolution,[],[f348,f515])).

fof(f348,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f347,f255])).

fof(f347,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f286,f252])).

fof(f286,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f150])).

fof(f150,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc4_funct_1)).

fof(f569,plain,
    ( spl26_60
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f555,f381,f567])).

fof(f567,plain,
    ( spl26_60
  <=> v4_funct_1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_60])])).

fof(f555,plain,
    ( v4_funct_1(sK15)
    | ~ spl26_8 ),
    inference(resolution,[],[f251,f382])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v4_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v4_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',cc8_funct_1)).

fof(f562,plain,
    ( spl26_58
    | ~ spl26_2 ),
    inference(avatar_split_clause,[],[f554,f360,f560])).

fof(f360,plain,
    ( spl26_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_2])])).

fof(f554,plain,
    ( v4_funct_1(k1_xboole_0)
    | ~ spl26_2 ),
    inference(resolution,[],[f251,f361])).

fof(f361,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl26_2 ),
    inference(avatar_component_clause,[],[f360])).

fof(f551,plain,(
    spl26_56 ),
    inference(avatar_split_clause,[],[f223,f549])).

fof(f223,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f173])).

fof(f544,plain,(
    spl26_54 ),
    inference(avatar_split_clause,[],[f222,f542])).

fof(f222,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f173])).

fof(f537,plain,(
    spl26_52 ),
    inference(avatar_split_clause,[],[f228,f535])).

fof(f535,plain,
    ( spl26_52
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_52])])).

fof(f228,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',d2_xboole_0)).

fof(f530,plain,(
    spl26_50 ),
    inference(avatar_split_clause,[],[f334,f528])).

fof(f334,plain,(
    v1_funct_1(sK25) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,plain,
    ( v1_funct_1(sK25)
    & v1_relat_1(sK25) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f100,f219])).

fof(f219,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK25)
      & v1_relat_1(sK25) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f60])).

fof(f60,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_funct_1)).

fof(f523,plain,(
    spl26_48 ),
    inference(avatar_split_clause,[],[f333,f521])).

fof(f333,plain,(
    v1_relat_1(sK25) ),
    inference(cnf_transformation,[],[f220])).

fof(f516,plain,(
    ~ spl26_47 ),
    inference(avatar_split_clause,[],[f332,f514])).

fof(f332,plain,(
    ~ v3_funct_1(sK24) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,plain,
    ( ~ v3_funct_1(sK24)
    & v1_funct_1(sK24)
    & v1_relat_1(sK24) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f72,f217])).

fof(f217,plain,
    ( ? [X0] :
        ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v3_funct_1(sK24)
      & v1_funct_1(sK24)
      & v1_relat_1(sK24) ) ),
    introduced(choice_axiom,[])).

fof(f72,axiom,(
    ? [X0] :
      ( ~ v3_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc5_funct_1)).

fof(f509,plain,(
    spl26_44 ),
    inference(avatar_split_clause,[],[f331,f507])).

fof(f331,plain,(
    v1_funct_1(sK24) ),
    inference(cnf_transformation,[],[f218])).

fof(f502,plain,(
    spl26_42 ),
    inference(avatar_split_clause,[],[f330,f500])).

fof(f330,plain,(
    v1_relat_1(sK24) ),
    inference(cnf_transformation,[],[f218])).

fof(f495,plain,(
    spl26_40 ),
    inference(avatar_split_clause,[],[f329,f493])).

fof(f329,plain,(
    v1_funct_1(sK23) ),
    inference(cnf_transformation,[],[f216])).

fof(f216,plain,
    ( v1_funct_1(sK23)
    & v1_relat_1(sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f54,f215])).

fof(f215,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK23)
      & v1_relat_1(sK23) ) ),
    introduced(choice_axiom,[])).

fof(f54,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_funct_1)).

fof(f488,plain,(
    spl26_38 ),
    inference(avatar_split_clause,[],[f328,f486])).

fof(f328,plain,(
    v1_relat_1(sK23) ),
    inference(cnf_transformation,[],[f216])).

fof(f481,plain,(
    spl26_36 ),
    inference(avatar_split_clause,[],[f327,f479])).

fof(f327,plain,(
    v1_funct_1(sK22) ),
    inference(cnf_transformation,[],[f214])).

fof(f214,plain,
    ( v1_funct_1(sK22)
    & v1_relat_1(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f91,f213])).

fof(f213,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK22)
      & v1_relat_1(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f66])).

fof(f66,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc3_funct_1)).

fof(f474,plain,(
    spl26_34 ),
    inference(avatar_split_clause,[],[f326,f472])).

fof(f326,plain,(
    v1_relat_1(sK22) ),
    inference(cnf_transformation,[],[f214])).

fof(f467,plain,(
    spl26_32 ),
    inference(avatar_split_clause,[],[f325,f465])).

fof(f325,plain,(
    v1_relat_1(sK21) ),
    inference(cnf_transformation,[],[f212])).

fof(f212,plain,(
    v1_relat_1(sK21) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f92,f211])).

fof(f211,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK21) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f62])).

fof(f62,axiom,(
    ? [X0] :
      ( v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_relat_1)).

fof(f460,plain,(
    spl26_30 ),
    inference(avatar_split_clause,[],[f324,f458])).

fof(f324,plain,(
    v1_funct_1(sK20) ),
    inference(cnf_transformation,[],[f210])).

fof(f210,plain,
    ( v1_funct_1(sK20)
    & v1_relat_1(sK20)
    & ~ v1_xboole_0(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f90,f209])).

fof(f209,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_funct_1(sK20)
      & v1_relat_1(sK20)
      & ~ v1_xboole_0(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(pure_predicate_removal,[],[f70])).

fof(f70,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc4_funct_1)).

fof(f453,plain,(
    spl26_28 ),
    inference(avatar_split_clause,[],[f323,f451])).

fof(f323,plain,(
    v1_relat_1(sK20) ),
    inference(cnf_transformation,[],[f210])).

fof(f446,plain,(
    ~ spl26_27 ),
    inference(avatar_split_clause,[],[f322,f444])).

fof(f322,plain,(
    ~ v1_xboole_0(sK20) ),
    inference(cnf_transformation,[],[f210])).

fof(f439,plain,(
    spl26_24 ),
    inference(avatar_split_clause,[],[f321,f437])).

fof(f321,plain,(
    v1_relat_1(sK19) ),
    inference(cnf_transformation,[],[f208])).

fof(f208,plain,
    ( v1_relat_1(sK19)
    & ~ v1_xboole_0(sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f56,f207])).

fof(f207,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK19)
      & ~ v1_xboole_0(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f56,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_relat_1)).

fof(f432,plain,(
    ~ spl26_23 ),
    inference(avatar_split_clause,[],[f320,f430])).

fof(f320,plain,(
    ~ v1_xboole_0(sK19) ),
    inference(cnf_transformation,[],[f208])).

fof(f425,plain,(
    spl26_20 ),
    inference(avatar_split_clause,[],[f319,f423])).

fof(f319,plain,(
    v1_zfmisc_1(sK18) ),
    inference(cnf_transformation,[],[f206])).

fof(f206,plain,
    ( v1_zfmisc_1(sK18)
    & ~ v1_xboole_0(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f55,f205])).

fof(f205,plain,
    ( ? [X0] :
        ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_zfmisc_1(sK18)
      & ~ v1_xboole_0(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f55,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_realset1)).

fof(f418,plain,(
    ~ spl26_19 ),
    inference(avatar_split_clause,[],[f318,f416])).

fof(f318,plain,(
    ~ v1_xboole_0(sK18) ),
    inference(cnf_transformation,[],[f206])).

fof(f411,plain,(
    spl26_16 ),
    inference(avatar_split_clause,[],[f317,f409])).

fof(f317,plain,(
    v4_funct_1(sK17) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,
    ( v4_funct_1(sK17)
    & ~ v1_xboole_0(sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f74,f203])).

fof(f203,plain,
    ( ? [X0] :
        ( v4_funct_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v4_funct_1(sK17)
      & ~ v1_xboole_0(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f74,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc7_funct_1)).

fof(f404,plain,(
    ~ spl26_15 ),
    inference(avatar_split_clause,[],[f316,f402])).

fof(f316,plain,(
    ~ v1_xboole_0(sK17) ),
    inference(cnf_transformation,[],[f204])).

fof(f397,plain,(
    ~ spl26_13 ),
    inference(avatar_split_clause,[],[f315,f395])).

fof(f395,plain,
    ( spl26_13
  <=> ~ v1_zfmisc_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_13])])).

fof(f315,plain,(
    ~ v1_zfmisc_1(sK16) ),
    inference(cnf_transformation,[],[f202])).

fof(f202,plain,
    ( ~ v1_zfmisc_1(sK16)
    & ~ v1_xboole_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f61,f201])).

fof(f201,plain,
    ( ? [X0] :
        ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ~ v1_zfmisc_1(sK16)
      & ~ v1_xboole_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f61,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_realset1)).

fof(f390,plain,(
    ~ spl26_11 ),
    inference(avatar_split_clause,[],[f314,f388])).

fof(f388,plain,
    ( spl26_11
  <=> ~ v1_xboole_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_11])])).

fof(f314,plain,(
    ~ v1_xboole_0(sK16) ),
    inference(cnf_transformation,[],[f202])).

fof(f383,plain,(
    spl26_8 ),
    inference(avatar_split_clause,[],[f313,f381])).

fof(f313,plain,(
    v1_xboole_0(sK15) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    v1_xboole_0(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f59,f199])).

fof(f199,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK15) ),
    introduced(choice_axiom,[])).

fof(f59,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc1_xboole_0)).

fof(f376,plain,(
    spl26_6 ),
    inference(avatar_split_clause,[],[f312,f374])).

fof(f374,plain,
    ( spl26_6
  <=> l1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_6])])).

fof(f312,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,(
    l1_pre_topc(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f46,f197])).

fof(f197,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK14) ),
    introduced(choice_axiom,[])).

fof(f46,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',existence_l1_pre_topc)).

fof(f369,plain,(
    ~ spl26_5 ),
    inference(avatar_split_clause,[],[f311,f367])).

fof(f367,plain,
    ( spl26_5
  <=> ~ v1_xboole_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_5])])).

fof(f311,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f65,f195])).

fof(f195,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK13) ),
    introduced(choice_axiom,[])).

fof(f65,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',rc2_xboole_0)).

fof(f362,plain,(
    spl26_2 ),
    inference(avatar_split_clause,[],[f226,f360])).

fof(f226,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t29_tex_2.p',fc1_xboole_0)).

fof(f355,plain,(
    spl26_0 ),
    inference(avatar_split_clause,[],[f221,f353])).

fof(f221,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f173])).
%------------------------------------------------------------------------------
