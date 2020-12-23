%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  283 ( 627 expanded)
%              Number of leaves         :   58 ( 265 expanded)
%              Depth                    :   16
%              Number of atoms          : 1231 (2981 expanded)
%              Number of equality atoms :  231 ( 739 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f172,f177,f192,f215,f243,f266,f278,f315,f324,f345,f399,f453,f467,f506,f515,f655,f1179,f1214,f1379,f1639,f1651,f1702,f1705])).

fof(f1705,plain,
    ( sK3 != k5_relat_1(k6_relat_1(sK1),sK3)
    | k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) != k5_relat_1(k6_relat_1(sK1),sK3)
    | k4_relat_1(sK2) != k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))
    | sK3 = k4_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1702,plain,
    ( spl4_122
    | ~ spl4_14
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f1697,f1371,f169,f1699])).

fof(f1699,plain,
    ( spl4_122
  <=> sK3 = k5_relat_1(k6_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f169,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1371,plain,
    ( spl4_93
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1697,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl4_14
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f1691,f171])).

fof(f171,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1691,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_93 ),
    inference(superposition,[],[f89,f1373])).

fof(f1373,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1651,plain,
    ( spl4_121
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1646,f512,f312,f295,f174,f169,f1648])).

fof(f1648,plain,
    ( spl4_121
  <=> k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f174,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f295,plain,
    ( spl4_24
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f312,plain,
    ( spl4_26
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f512,plain,
    ( spl4_42
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1646,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1617,f171])).

fof(f1617,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_42 ),
    inference(superposition,[],[f425,f514])).

fof(f514,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f512])).

fof(f425,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f424,f296])).

fof(f296,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f295])).

fof(f424,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f415,f176])).

fof(f176,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f415,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_26 ),
    inference(superposition,[],[f86,f314])).

fof(f314,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f312])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1639,plain,
    ( spl4_119
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1634,f464,f438,f312,f295,f275,f174,f1636])).

fof(f1636,plain,
    ( spl4_119
  <=> k4_relat_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f275,plain,
    ( spl4_22
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f438,plain,
    ( spl4_35
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f464,plain,
    ( spl4_37
  <=> k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1634,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f1633,f466])).

fof(f466,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f464])).

fof(f1633,plain,
    ( k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f1614,f439])).

fof(f439,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f438])).

fof(f1614,plain,
    ( k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(superposition,[],[f425,f277])).

fof(f277,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f1379,plain,
    ( spl4_93
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1378,f396,f375,f169,f139,f1371])).

fof(f139,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f375,plain,
    ( spl4_30
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f396,plain,
    ( spl4_33
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1378,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1377,f90])).

fof(f90,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1377,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1376,f171])).

fof(f1376,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1375,f141])).

fof(f141,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1375,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1341,f377])).

fof(f377,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f375])).

fof(f1341,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33 ),
    inference(superposition,[],[f67,f398])).

fof(f398,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f396])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f1214,plain,
    ( spl4_30
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f1213,f503,f154,f149,f144,f139,f134,f129,f124,f109,f375])).

fof(f109,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f144,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f149,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f154,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f503,plain,
    ( spl4_40
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1213,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1212,f141])).

fof(f1212,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1211,f136])).

fof(f136,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1211,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1210,f131])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1210,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1197,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1197,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f1189,f76])).

fof(f76,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1189,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(superposition,[],[f410,f505])).

fof(f505,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f503])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f409,f156])).

fof(f156,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f408,f151])).

fof(f151,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f407,f146])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f74,f126])).

fof(f126,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1179,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f1178])).

fof(f1178,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(subsumption_resolution,[],[f1177,f156])).

fof(f1177,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_39 ),
    inference(subsumption_resolution,[],[f1176,f146])).

fof(f1176,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_39 ),
    inference(subsumption_resolution,[],[f1175,f141])).

fof(f1175,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_39 ),
    inference(subsumption_resolution,[],[f1172,f131])).

fof(f1172,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_39 ),
    inference(resolution,[],[f501,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f501,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_39
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f655,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f510,f248])).

fof(f248,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f83,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f510,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl4_41
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f515,plain,
    ( ~ spl4_41
    | spl4_42
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f496,f240,f512,f508])).

fof(f240,plain,
    ( spl4_20
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f496,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_20 ),
    inference(resolution,[],[f231,f242])).

fof(f242,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f77,f164])).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f506,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f495,f160,f503,f499])).

fof(f160,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f495,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f231,f162])).

fof(f162,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f467,plain,
    ( spl4_37
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f462,f210,f174,f464])).

fof(f210,plain,
    ( spl4_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f462,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2))
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f457,f176])).

fof(f457,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f180,f212])).

fof(f212,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f180,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f179,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f179,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f89,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f453,plain,
    ( ~ spl4_15
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl4_15
    | spl4_35 ),
    inference(subsumption_resolution,[],[f450,f176])).

fof(f450,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_35 ),
    inference(resolution,[],[f440,f93])).

fof(f440,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f438])).

fof(f399,plain,
    ( spl4_33
    | ~ spl4_30
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f394,f342,f139,f134,f129,f109,f375,f396])).

fof(f342,plain,
    ( spl4_27
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f394,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f393,f141])).

fof(f393,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f392,f136])).

fof(f392,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f391,f131])).

fof(f391,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f362,f111])).

fof(f362,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_27 ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_27 ),
    inference(superposition,[],[f249,f344])).

fof(f344,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f342])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f65,f81])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f345,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f340,f160,f154,f149,f144,f139,f134,f129,f342])).

fof(f340,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f339,f141])).

fof(f339,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f338,f136])).

fof(f338,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f337,f131])).

fof(f337,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f336,f156])).

fof(f336,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f335,f151])).

fof(f335,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f332,f146])).

fof(f332,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f331,f162])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f79,f81])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f324,plain,
    ( ~ spl4_12
    | ~ spl4_15
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_15
    | spl4_24 ),
    inference(subsumption_resolution,[],[f322,f176])).

fof(f322,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_24 ),
    inference(subsumption_resolution,[],[f319,f156])).

fof(f319,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_24 ),
    inference(resolution,[],[f297,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f297,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f295])).

fof(f315,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f310,f154,f149,f144,f124,f114,f104,f312])).

fof(f104,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f114,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f310,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f309,f156])).

fof(f309,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f308,f151])).

fof(f308,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f307,f146])).

fof(f307,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f306,f116])).

fof(f116,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f306,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f305,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f305,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f302])).

fof(f302,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f250,f126])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f66,f81])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f273,f263,f174,f154,f114,f275])).

fof(f263,plain,
    ( spl4_21
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f273,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f272,f176])).

fof(f272,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f271,f156])).

fof(f271,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f267,f116])).

fof(f267,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(superposition,[],[f265,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f265,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f263])).

fof(f266,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f261,f154,f149,f144,f124,f114,f104,f263])).

fof(f261,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f260,f156])).

fof(f260,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f259,f151])).

fof(f259,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f258,f146])).

fof(f258,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f257,f116])).

fof(f257,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f256,f106])).

fof(f256,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f249,f126])).

fof(f243,plain,
    ( spl4_20
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f238,f160,f154,f144,f139,f129,f240])).

fof(f238,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f237,f156])).

fof(f237,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f236,f146])).

fof(f236,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f235,f141])).

fof(f235,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f232,f131])).

fof(f232,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f162,f84])).

fof(f215,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f214,f144,f124,f210])).

fof(f214,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f207,f146])).

fof(f207,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f126,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f192,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f187,f154,f114,f99,f189,f174])).

fof(f189,plain,
    ( spl4_16
  <=> sK3 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f99,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f187,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f186,f156])).

fof(f186,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f181,f116])).

fof(f181,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(superposition,[],[f101,f69])).

fof(f101,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f177,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f166,f144,f174])).

fof(f166,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f92,f146])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f172,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f165,f129,f169])).

fof(f165,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f92,f131])).

fof(f163,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f119,f160])).

fof(f119,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f121,f81])).

fof(f121,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f53,f154])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f152,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f54,f149])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f55,f144])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f142,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f56,f139])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f57,f134])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f132,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f58,f129])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f127,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f59,f124])).

fof(f59,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f60,f119])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f61,f114])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f112,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f63,f104])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f64,f99])).

fof(f64,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (13107)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (13128)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (13111)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (13136)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (13110)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (13123)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (13120)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (13109)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13124)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (13129)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (13113)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13112)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (13108)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (13125)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (13117)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (13119)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (13121)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (13116)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (13118)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (13127)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (13115)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (13130)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (13122)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (13126)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (13133)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13132)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (13135)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (13123)Refutation not found, incomplete strategy% (13123)------------------------------
% 0.21/0.55  % (13123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13123)Memory used [KB]: 10746
% 0.21/0.55  % (13123)Time elapsed: 0.138 s
% 0.21/0.55  % (13123)------------------------------
% 0.21/0.55  % (13123)------------------------------
% 0.21/0.56  % (13131)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (13114)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (13134)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.62  % (13128)Refutation found. Thanks to Tanya!
% 0.21/0.62  % SZS status Theorem for theBenchmark
% 1.96/0.63  % SZS output start Proof for theBenchmark
% 1.96/0.64  fof(f1706,plain,(
% 1.96/0.64    $false),
% 1.96/0.64    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f172,f177,f192,f215,f243,f266,f278,f315,f324,f345,f399,f453,f467,f506,f515,f655,f1179,f1214,f1379,f1639,f1651,f1702,f1705])).
% 1.96/0.64  fof(f1705,plain,(
% 1.96/0.64    sK3 != k5_relat_1(k6_relat_1(sK1),sK3) | k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) != k5_relat_1(k6_relat_1(sK1),sK3) | k4_relat_1(sK2) != k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) | sK3 = k4_relat_1(sK2)),
% 1.96/0.64    introduced(theory_tautology_sat_conflict,[])).
% 1.96/0.64  fof(f1702,plain,(
% 1.96/0.64    spl4_122 | ~spl4_14 | ~spl4_93),
% 1.96/0.64    inference(avatar_split_clause,[],[f1697,f1371,f169,f1699])).
% 1.96/0.64  fof(f1699,plain,(
% 1.96/0.64    spl4_122 <=> sK3 = k5_relat_1(k6_relat_1(sK1),sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).
% 1.96/0.64  fof(f169,plain,(
% 1.96/0.64    spl4_14 <=> v1_relat_1(sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.96/0.64  fof(f1371,plain,(
% 1.96/0.64    spl4_93 <=> sK1 = k1_relat_1(sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 1.96/0.64  fof(f1697,plain,(
% 1.96/0.64    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | (~spl4_14 | ~spl4_93)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1691,f171])).
% 1.96/0.64  fof(f171,plain,(
% 1.96/0.64    v1_relat_1(sK3) | ~spl4_14),
% 1.96/0.64    inference(avatar_component_clause,[],[f169])).
% 1.96/0.64  fof(f1691,plain,(
% 1.96/0.64    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | ~v1_relat_1(sK3) | ~spl4_93),
% 1.96/0.64    inference(superposition,[],[f89,f1373])).
% 1.96/0.64  fof(f1373,plain,(
% 1.96/0.64    sK1 = k1_relat_1(sK3) | ~spl4_93),
% 1.96/0.64    inference(avatar_component_clause,[],[f1371])).
% 1.96/0.64  fof(f89,plain,(
% 1.96/0.64    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f46])).
% 1.96/0.64  fof(f46,plain,(
% 1.96/0.64    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.96/0.64    inference(ennf_transformation,[],[f5])).
% 1.96/0.64  fof(f5,axiom,(
% 1.96/0.64    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.96/0.64  fof(f1651,plain,(
% 1.96/0.64    spl4_121 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_26 | ~spl4_42),
% 1.96/0.64    inference(avatar_split_clause,[],[f1646,f512,f312,f295,f174,f169,f1648])).
% 1.96/0.64  fof(f1648,plain,(
% 1.96/0.64    spl4_121 <=> k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 1.96/0.64  fof(f174,plain,(
% 1.96/0.64    spl4_15 <=> v1_relat_1(sK2)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.96/0.64  fof(f295,plain,(
% 1.96/0.64    spl4_24 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.96/0.64  fof(f312,plain,(
% 1.96/0.64    spl4_26 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.96/0.64  fof(f512,plain,(
% 1.96/0.64    spl4_42 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.96/0.64  fof(f1646,plain,(
% 1.96/0.64    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3) | (~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_26 | ~spl4_42)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1617,f171])).
% 1.96/0.64  fof(f1617,plain,(
% 1.96/0.64    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3) | ~v1_relat_1(sK3) | (~spl4_15 | ~spl4_24 | ~spl4_26 | ~spl4_42)),
% 1.96/0.64    inference(superposition,[],[f425,f514])).
% 1.96/0.64  fof(f514,plain,(
% 1.96/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_42),
% 1.96/0.64    inference(avatar_component_clause,[],[f512])).
% 1.96/0.64  fof(f425,plain,(
% 1.96/0.64    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0) | ~v1_relat_1(X0)) ) | (~spl4_15 | ~spl4_24 | ~spl4_26)),
% 1.96/0.64    inference(subsumption_resolution,[],[f424,f296])).
% 1.96/0.64  fof(f296,plain,(
% 1.96/0.64    v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 1.96/0.64    inference(avatar_component_clause,[],[f295])).
% 1.96/0.64  fof(f424,plain,(
% 1.96/0.64    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl4_15 | ~spl4_26)),
% 1.96/0.64    inference(subsumption_resolution,[],[f415,f176])).
% 1.96/0.64  fof(f176,plain,(
% 1.96/0.64    v1_relat_1(sK2) | ~spl4_15),
% 1.96/0.64    inference(avatar_component_clause,[],[f174])).
% 1.96/0.64  fof(f415,plain,(
% 1.96/0.64    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_relat_1(sK1),X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl4_26),
% 1.96/0.64    inference(superposition,[],[f86,f314])).
% 1.96/0.64  fof(f314,plain,(
% 1.96/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_26),
% 1.96/0.64    inference(avatar_component_clause,[],[f312])).
% 1.96/0.64  fof(f86,plain,(
% 1.96/0.64    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f44])).
% 1.96/0.64  fof(f44,plain,(
% 1.96/0.64    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.96/0.64    inference(ennf_transformation,[],[f3])).
% 1.96/0.64  fof(f3,axiom,(
% 1.96/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.96/0.64  fof(f1639,plain,(
% 1.96/0.64    spl4_119 | ~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26 | ~spl4_35 | ~spl4_37),
% 1.96/0.64    inference(avatar_split_clause,[],[f1634,f464,f438,f312,f295,f275,f174,f1636])).
% 1.96/0.64  fof(f1636,plain,(
% 1.96/0.64    spl4_119 <=> k4_relat_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 1.96/0.64  fof(f275,plain,(
% 1.96/0.64    spl4_22 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.96/0.64  fof(f438,plain,(
% 1.96/0.64    spl4_35 <=> v1_relat_1(k4_relat_1(sK2))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.96/0.64  fof(f464,plain,(
% 1.96/0.64    spl4_37 <=> k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.96/0.64  fof(f1634,plain,(
% 1.96/0.64    k4_relat_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) | (~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26 | ~spl4_35 | ~spl4_37)),
% 1.96/0.64    inference(forward_demodulation,[],[f1633,f466])).
% 1.96/0.64  fof(f466,plain,(
% 1.96/0.64    k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) | ~spl4_37),
% 1.96/0.64    inference(avatar_component_clause,[],[f464])).
% 1.96/0.64  fof(f1633,plain,(
% 1.96/0.64    k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) | (~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26 | ~spl4_35)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1614,f439])).
% 1.96/0.64  fof(f439,plain,(
% 1.96/0.64    v1_relat_1(k4_relat_1(sK2)) | ~spl4_35),
% 1.96/0.64    inference(avatar_component_clause,[],[f438])).
% 1.96/0.64  fof(f1614,plain,(
% 1.96/0.64    k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26)),
% 1.96/0.64    inference(superposition,[],[f425,f277])).
% 1.96/0.64  fof(f277,plain,(
% 1.96/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~spl4_22),
% 1.96/0.64    inference(avatar_component_clause,[],[f275])).
% 1.96/0.64  fof(f1379,plain,(
% 1.96/0.64    spl4_93 | ~spl4_9 | ~spl4_14 | ~spl4_30 | ~spl4_33),
% 1.96/0.64    inference(avatar_split_clause,[],[f1378,f396,f375,f169,f139,f1371])).
% 1.96/0.64  fof(f139,plain,(
% 1.96/0.64    spl4_9 <=> v1_funct_1(sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.96/0.64  fof(f375,plain,(
% 1.96/0.64    spl4_30 <=> v2_funct_1(sK3)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.96/0.64  fof(f396,plain,(
% 1.96/0.64    spl4_33 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.96/0.64  fof(f1378,plain,(
% 1.96/0.64    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_30 | ~spl4_33)),
% 1.96/0.64    inference(forward_demodulation,[],[f1377,f90])).
% 1.96/0.64  fof(f90,plain,(
% 1.96/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.96/0.64    inference(cnf_transformation,[],[f4])).
% 1.96/0.64  fof(f4,axiom,(
% 1.96/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.96/0.64  fof(f1377,plain,(
% 1.96/0.64    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_9 | ~spl4_14 | ~spl4_30 | ~spl4_33)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1376,f171])).
% 1.96/0.64  fof(f1376,plain,(
% 1.96/0.64    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_30 | ~spl4_33)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1375,f141])).
% 1.96/0.64  fof(f141,plain,(
% 1.96/0.64    v1_funct_1(sK3) | ~spl4_9),
% 1.96/0.64    inference(avatar_component_clause,[],[f139])).
% 1.96/0.64  fof(f1375,plain,(
% 1.96/0.64    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_30 | ~spl4_33)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1341,f377])).
% 1.96/0.64  fof(f377,plain,(
% 1.96/0.64    v2_funct_1(sK3) | ~spl4_30),
% 1.96/0.64    inference(avatar_component_clause,[],[f375])).
% 1.96/0.64  fof(f1341,plain,(
% 1.96/0.64    k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_33),
% 1.96/0.64    inference(superposition,[],[f67,f398])).
% 1.96/0.64  fof(f398,plain,(
% 1.96/0.64    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_33),
% 1.96/0.64    inference(avatar_component_clause,[],[f396])).
% 1.96/0.64  fof(f67,plain,(
% 1.96/0.64    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f28])).
% 1.96/0.64  fof(f28,plain,(
% 1.96/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/0.64    inference(flattening,[],[f27])).
% 1.96/0.64  fof(f27,plain,(
% 1.96/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.96/0.64    inference(ennf_transformation,[],[f9])).
% 1.96/0.64  fof(f9,axiom,(
% 1.96/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.96/0.64  fof(f1214,plain,(
% 1.96/0.64    spl4_30 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40),
% 1.96/0.64    inference(avatar_split_clause,[],[f1213,f503,f154,f149,f144,f139,f134,f129,f124,f109,f375])).
% 1.96/0.64  fof(f109,plain,(
% 1.96/0.64    spl4_3 <=> k1_xboole_0 = sK0),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.96/0.64  fof(f124,plain,(
% 1.96/0.64    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.96/0.64  fof(f129,plain,(
% 1.96/0.64    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.96/0.64  fof(f134,plain,(
% 1.96/0.64    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.96/0.64  fof(f144,plain,(
% 1.96/0.64    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.96/0.64  fof(f149,plain,(
% 1.96/0.64    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.96/0.64  fof(f154,plain,(
% 1.96/0.64    spl4_12 <=> v1_funct_1(sK2)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.96/0.64  fof(f503,plain,(
% 1.96/0.64    spl4_40 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.96/0.64  fof(f1213,plain,(
% 1.96/0.64    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1212,f141])).
% 1.96/0.64  fof(f1212,plain,(
% 1.96/0.64    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1211,f136])).
% 1.96/0.64  fof(f136,plain,(
% 1.96/0.64    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.96/0.64    inference(avatar_component_clause,[],[f134])).
% 1.96/0.64  fof(f1211,plain,(
% 1.96/0.64    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1210,f131])).
% 1.96/0.64  fof(f131,plain,(
% 1.96/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.96/0.64    inference(avatar_component_clause,[],[f129])).
% 1.96/0.64  fof(f1210,plain,(
% 1.96/0.64    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1197,f111])).
% 1.96/0.64  fof(f111,plain,(
% 1.96/0.64    k1_xboole_0 != sK0 | spl4_3),
% 1.96/0.64    inference(avatar_component_clause,[],[f109])).
% 1.96/0.64  fof(f1197,plain,(
% 1.96/0.64    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1189,f76])).
% 1.96/0.64  fof(f76,plain,(
% 1.96/0.64    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.96/0.64    inference(cnf_transformation,[],[f8])).
% 1.96/0.64  fof(f8,axiom,(
% 1.96/0.64    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.96/0.64  fof(f1189,plain,(
% 1.96/0.64    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.96/0.64    inference(superposition,[],[f410,f505])).
% 1.96/0.64  fof(f505,plain,(
% 1.96/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_40),
% 1.96/0.64    inference(avatar_component_clause,[],[f503])).
% 1.96/0.64  fof(f410,plain,(
% 1.96/0.64    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.96/0.64    inference(subsumption_resolution,[],[f409,f156])).
% 1.96/0.64  fof(f156,plain,(
% 1.96/0.64    v1_funct_1(sK2) | ~spl4_12),
% 1.96/0.64    inference(avatar_component_clause,[],[f154])).
% 1.96/0.64  fof(f409,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.96/0.64    inference(subsumption_resolution,[],[f408,f151])).
% 1.96/0.64  fof(f151,plain,(
% 1.96/0.64    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.96/0.64    inference(avatar_component_clause,[],[f149])).
% 1.96/0.64  fof(f408,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.96/0.64    inference(subsumption_resolution,[],[f407,f146])).
% 1.96/0.64  fof(f146,plain,(
% 1.96/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.96/0.64    inference(avatar_component_clause,[],[f144])).
% 1.96/0.64  fof(f407,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.96/0.64    inference(trivial_inequality_removal,[],[f402])).
% 1.96/0.64  fof(f402,plain,(
% 1.96/0.64    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.96/0.64    inference(superposition,[],[f74,f126])).
% 1.96/0.64  fof(f126,plain,(
% 1.96/0.64    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.96/0.64    inference(avatar_component_clause,[],[f124])).
% 1.96/0.64  fof(f74,plain,(
% 1.96/0.64    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f34])).
% 1.96/0.64  fof(f34,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.96/0.64    inference(flattening,[],[f33])).
% 1.96/0.64  fof(f33,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.96/0.64    inference(ennf_transformation,[],[f18])).
% 1.96/0.64  fof(f18,axiom,(
% 1.96/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.96/0.64  fof(f1179,plain,(
% 1.96/0.64    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39),
% 1.96/0.64    inference(avatar_contradiction_clause,[],[f1178])).
% 1.96/0.64  fof(f1178,plain,(
% 1.96/0.64    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1177,f156])).
% 1.96/0.64  fof(f1177,plain,(
% 1.96/0.64    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_39)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1176,f146])).
% 1.96/0.64  fof(f1176,plain,(
% 1.96/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_39)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1175,f141])).
% 1.96/0.64  fof(f1175,plain,(
% 1.96/0.64    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_39)),
% 1.96/0.64    inference(subsumption_resolution,[],[f1172,f131])).
% 1.96/0.64  fof(f1172,plain,(
% 1.96/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_39),
% 1.96/0.64    inference(resolution,[],[f501,f83])).
% 1.96/0.64  fof(f83,plain,(
% 1.96/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f40])).
% 1.96/0.64  fof(f40,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.96/0.64    inference(flattening,[],[f39])).
% 1.96/0.64  fof(f39,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.96/0.64    inference(ennf_transformation,[],[f13])).
% 1.96/0.64  fof(f13,axiom,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.96/0.64  fof(f501,plain,(
% 1.96/0.64    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_39),
% 1.96/0.64    inference(avatar_component_clause,[],[f499])).
% 1.96/0.64  fof(f499,plain,(
% 1.96/0.64    spl4_39 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.96/0.64  fof(f655,plain,(
% 1.96/0.64    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41),
% 1.96/0.64    inference(avatar_contradiction_clause,[],[f633])).
% 1.96/0.64  fof(f633,plain,(
% 1.96/0.64    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41)),
% 1.96/0.64    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f510,f248])).
% 1.96/0.64  fof(f248,plain,(
% 1.96/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.96/0.64    inference(duplicate_literal_removal,[],[f247])).
% 1.96/0.64  fof(f247,plain,(
% 1.96/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.96/0.64    inference(superposition,[],[f83,f84])).
% 1.96/0.64  fof(f84,plain,(
% 1.96/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f42])).
% 1.96/0.64  fof(f42,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.96/0.64    inference(flattening,[],[f41])).
% 1.96/0.64  fof(f41,plain,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.96/0.64    inference(ennf_transformation,[],[f15])).
% 1.96/0.64  fof(f15,axiom,(
% 1.96/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.96/0.64  fof(f510,plain,(
% 1.96/0.64    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_41),
% 1.96/0.64    inference(avatar_component_clause,[],[f508])).
% 1.96/0.64  fof(f508,plain,(
% 1.96/0.64    spl4_41 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.96/0.64  fof(f515,plain,(
% 1.96/0.64    ~spl4_41 | spl4_42 | ~spl4_20),
% 1.96/0.64    inference(avatar_split_clause,[],[f496,f240,f512,f508])).
% 1.96/0.64  fof(f240,plain,(
% 1.96/0.64    spl4_20 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.96/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.96/0.64  fof(f496,plain,(
% 1.96/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_20),
% 1.96/0.64    inference(resolution,[],[f231,f242])).
% 1.96/0.64  fof(f242,plain,(
% 1.96/0.64    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_20),
% 1.96/0.64    inference(avatar_component_clause,[],[f240])).
% 2.13/0.64  fof(f231,plain,(
% 2.13/0.64    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.13/0.64    inference(resolution,[],[f77,f164])).
% 2.13/0.64  fof(f164,plain,(
% 2.13/0.64    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.13/0.64    inference(forward_demodulation,[],[f80,f81])).
% 2.13/0.64  fof(f81,plain,(
% 2.13/0.64    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f16])).
% 2.13/0.64  fof(f16,axiom,(
% 2.13/0.64    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.13/0.64  fof(f80,plain,(
% 2.13/0.64    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f22])).
% 2.13/0.64  fof(f22,plain,(
% 2.13/0.64    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.13/0.64    inference(pure_predicate_removal,[],[f14])).
% 2.13/0.64  fof(f14,axiom,(
% 2.13/0.64    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.13/0.64  fof(f77,plain,(
% 2.13/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f52])).
% 2.13/0.64  fof(f52,plain,(
% 2.13/0.64    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.64    inference(nnf_transformation,[],[f36])).
% 2.13/0.64  fof(f36,plain,(
% 2.13/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.64    inference(flattening,[],[f35])).
% 2.13/0.64  fof(f35,plain,(
% 2.13/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.13/0.64    inference(ennf_transformation,[],[f12])).
% 2.13/0.64  fof(f12,axiom,(
% 2.13/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.13/0.64  fof(f506,plain,(
% 2.13/0.64    ~spl4_39 | spl4_40 | ~spl4_13),
% 2.13/0.64    inference(avatar_split_clause,[],[f495,f160,f503,f499])).
% 2.13/0.64  fof(f160,plain,(
% 2.13/0.64    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.13/0.64  fof(f495,plain,(
% 2.13/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 2.13/0.64    inference(resolution,[],[f231,f162])).
% 2.13/0.64  fof(f162,plain,(
% 2.13/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.13/0.64    inference(avatar_component_clause,[],[f160])).
% 2.13/0.64  fof(f467,plain,(
% 2.13/0.64    spl4_37 | ~spl4_15 | ~spl4_19),
% 2.13/0.64    inference(avatar_split_clause,[],[f462,f210,f174,f464])).
% 2.13/0.64  fof(f210,plain,(
% 2.13/0.64    spl4_19 <=> sK1 = k2_relat_1(sK2)),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.13/0.64  fof(f462,plain,(
% 2.13/0.64    k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) | (~spl4_15 | ~spl4_19)),
% 2.13/0.64    inference(subsumption_resolution,[],[f457,f176])).
% 2.13/0.64  fof(f457,plain,(
% 2.13/0.64    k4_relat_1(sK2) = k5_relat_1(k6_relat_1(sK1),k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_19),
% 2.13/0.64    inference(superposition,[],[f180,f212])).
% 2.13/0.64  fof(f212,plain,(
% 2.13/0.64    sK1 = k2_relat_1(sK2) | ~spl4_19),
% 2.13/0.64    inference(avatar_component_clause,[],[f210])).
% 2.13/0.64  fof(f180,plain,(
% 2.13/0.64    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.13/0.64    inference(subsumption_resolution,[],[f179,f93])).
% 2.13/0.64  fof(f93,plain,(
% 2.13/0.64    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f48])).
% 2.13/0.64  fof(f48,plain,(
% 2.13/0.64    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.13/0.64    inference(ennf_transformation,[],[f1])).
% 2.13/0.64  fof(f1,axiom,(
% 2.13/0.64    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.13/0.64  fof(f179,plain,(
% 2.13/0.64    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.13/0.64    inference(superposition,[],[f89,f87])).
% 2.13/0.64  fof(f87,plain,(
% 2.13/0.64    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f45])).
% 2.13/0.64  fof(f45,plain,(
% 2.13/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.13/0.64    inference(ennf_transformation,[],[f2])).
% 2.13/0.64  fof(f2,axiom,(
% 2.13/0.64    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 2.13/0.64  fof(f453,plain,(
% 2.13/0.64    ~spl4_15 | spl4_35),
% 2.13/0.64    inference(avatar_contradiction_clause,[],[f452])).
% 2.13/0.64  fof(f452,plain,(
% 2.13/0.64    $false | (~spl4_15 | spl4_35)),
% 2.13/0.64    inference(subsumption_resolution,[],[f450,f176])).
% 2.13/0.64  fof(f450,plain,(
% 2.13/0.64    ~v1_relat_1(sK2) | spl4_35),
% 2.13/0.64    inference(resolution,[],[f440,f93])).
% 2.13/0.64  fof(f440,plain,(
% 2.13/0.64    ~v1_relat_1(k4_relat_1(sK2)) | spl4_35),
% 2.13/0.64    inference(avatar_component_clause,[],[f438])).
% 2.13/0.64  fof(f399,plain,(
% 2.13/0.64    spl4_33 | ~spl4_30 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_27),
% 2.13/0.64    inference(avatar_split_clause,[],[f394,f342,f139,f134,f129,f109,f375,f396])).
% 2.13/0.64  fof(f342,plain,(
% 2.13/0.64    spl4_27 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.13/0.64  fof(f394,plain,(
% 2.13/0.64    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_27)),
% 2.13/0.64    inference(subsumption_resolution,[],[f393,f141])).
% 2.13/0.64  fof(f393,plain,(
% 2.13/0.64    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_27)),
% 2.13/0.64    inference(subsumption_resolution,[],[f392,f136])).
% 2.13/0.64  fof(f392,plain,(
% 2.13/0.64    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_27)),
% 2.13/0.64    inference(subsumption_resolution,[],[f391,f131])).
% 2.13/0.64  fof(f391,plain,(
% 2.13/0.64    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_27)),
% 2.13/0.64    inference(subsumption_resolution,[],[f362,f111])).
% 2.13/0.64  fof(f362,plain,(
% 2.13/0.64    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_27),
% 2.13/0.64    inference(trivial_inequality_removal,[],[f360])).
% 2.13/0.64  fof(f360,plain,(
% 2.13/0.64    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_27),
% 2.13/0.64    inference(superposition,[],[f249,f344])).
% 2.13/0.64  fof(f344,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_27),
% 2.13/0.64    inference(avatar_component_clause,[],[f342])).
% 2.13/0.64  fof(f249,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.64    inference(forward_demodulation,[],[f65,f81])).
% 2.13/0.64  fof(f65,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f26])).
% 2.13/0.64  fof(f26,plain,(
% 2.13/0.64    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.13/0.64    inference(flattening,[],[f25])).
% 2.13/0.64  fof(f25,plain,(
% 2.13/0.64    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.13/0.64    inference(ennf_transformation,[],[f19])).
% 2.13/0.64  fof(f19,axiom,(
% 2.13/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.13/0.64  fof(f345,plain,(
% 2.13/0.64    spl4_27 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 2.13/0.64    inference(avatar_split_clause,[],[f340,f160,f154,f149,f144,f139,f134,f129,f342])).
% 2.13/0.64  fof(f340,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f339,f141])).
% 2.13/0.64  fof(f339,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f338,f136])).
% 2.13/0.64  fof(f338,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f337,f131])).
% 2.13/0.64  fof(f337,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f336,f156])).
% 2.13/0.64  fof(f336,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f335,f151])).
% 2.13/0.64  fof(f335,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 2.13/0.64    inference(subsumption_resolution,[],[f332,f146])).
% 2.13/0.64  fof(f332,plain,(
% 2.13/0.64    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 2.13/0.64    inference(resolution,[],[f331,f162])).
% 2.13/0.64  fof(f331,plain,(
% 2.13/0.64    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.64    inference(forward_demodulation,[],[f79,f81])).
% 2.13/0.64  fof(f79,plain,(
% 2.13/0.64    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f38])).
% 2.13/0.64  fof(f38,plain,(
% 2.13/0.64    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.13/0.64    inference(flattening,[],[f37])).
% 2.13/0.64  fof(f37,plain,(
% 2.13/0.64    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.13/0.64    inference(ennf_transformation,[],[f17])).
% 2.13/0.64  fof(f17,axiom,(
% 2.13/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.13/0.65  fof(f324,plain,(
% 2.13/0.65    ~spl4_12 | ~spl4_15 | spl4_24),
% 2.13/0.65    inference(avatar_contradiction_clause,[],[f323])).
% 2.13/0.65  fof(f323,plain,(
% 2.13/0.65    $false | (~spl4_12 | ~spl4_15 | spl4_24)),
% 2.13/0.65    inference(subsumption_resolution,[],[f322,f176])).
% 2.13/0.65  fof(f322,plain,(
% 2.13/0.65    ~v1_relat_1(sK2) | (~spl4_12 | spl4_24)),
% 2.13/0.65    inference(subsumption_resolution,[],[f319,f156])).
% 2.13/0.65  fof(f319,plain,(
% 2.13/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_24),
% 2.13/0.65    inference(resolution,[],[f297,f70])).
% 2.13/0.65  fof(f70,plain,(
% 2.13/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f32])).
% 2.13/0.65  fof(f32,plain,(
% 2.13/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.13/0.65    inference(flattening,[],[f31])).
% 2.13/0.65  fof(f31,plain,(
% 2.13/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f7])).
% 2.13/0.65  fof(f7,axiom,(
% 2.13/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.13/0.65  fof(f297,plain,(
% 2.13/0.65    ~v1_relat_1(k2_funct_1(sK2)) | spl4_24),
% 2.13/0.65    inference(avatar_component_clause,[],[f295])).
% 2.13/0.65  fof(f315,plain,(
% 2.13/0.65    spl4_26 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.13/0.65    inference(avatar_split_clause,[],[f310,f154,f149,f144,f124,f114,f104,f312])).
% 2.13/0.65  fof(f104,plain,(
% 2.13/0.65    spl4_2 <=> k1_xboole_0 = sK1),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.13/0.65  fof(f114,plain,(
% 2.13/0.65    spl4_4 <=> v2_funct_1(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.13/0.65  fof(f310,plain,(
% 2.13/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.13/0.65    inference(subsumption_resolution,[],[f309,f156])).
% 2.13/0.65  fof(f309,plain,(
% 2.13/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.13/0.65    inference(subsumption_resolution,[],[f308,f151])).
% 2.13/0.65  fof(f308,plain,(
% 2.13/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.13/0.65    inference(subsumption_resolution,[],[f307,f146])).
% 2.13/0.65  fof(f307,plain,(
% 2.13/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.13/0.65    inference(subsumption_resolution,[],[f306,f116])).
% 2.13/0.65  fof(f116,plain,(
% 2.13/0.65    v2_funct_1(sK2) | ~spl4_4),
% 2.13/0.65    inference(avatar_component_clause,[],[f114])).
% 2.13/0.65  fof(f306,plain,(
% 2.13/0.65    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.13/0.65    inference(subsumption_resolution,[],[f305,f106])).
% 2.13/0.65  fof(f106,plain,(
% 2.13/0.65    k1_xboole_0 != sK1 | spl4_2),
% 2.13/0.65    inference(avatar_component_clause,[],[f104])).
% 2.13/0.65  fof(f305,plain,(
% 2.13/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.13/0.65    inference(trivial_inequality_removal,[],[f302])).
% 2.13/0.65  fof(f302,plain,(
% 2.13/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.13/0.65    inference(superposition,[],[f250,f126])).
% 2.13/0.65  fof(f250,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f66,f81])).
% 2.13/0.65  fof(f66,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f26])).
% 2.13/0.65  fof(f278,plain,(
% 2.13/0.65    spl4_22 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21),
% 2.13/0.65    inference(avatar_split_clause,[],[f273,f263,f174,f154,f114,f275])).
% 2.13/0.65  fof(f263,plain,(
% 2.13/0.65    spl4_21 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.13/0.65  fof(f273,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21)),
% 2.13/0.65    inference(subsumption_resolution,[],[f272,f176])).
% 2.13/0.65  fof(f272,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_21)),
% 2.13/0.65    inference(subsumption_resolution,[],[f271,f156])).
% 2.13/0.65  fof(f271,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_21)),
% 2.13/0.65    inference(subsumption_resolution,[],[f267,f116])).
% 2.13/0.65  fof(f267,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_21),
% 2.13/0.65    inference(superposition,[],[f265,f69])).
% 2.13/0.65  fof(f69,plain,(
% 2.13/0.65    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f30])).
% 2.13/0.65  fof(f30,plain,(
% 2.13/0.65    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.13/0.65    inference(flattening,[],[f29])).
% 2.13/0.65  fof(f29,plain,(
% 2.13/0.65    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f6])).
% 2.13/0.65  fof(f6,axiom,(
% 2.13/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.13/0.65  fof(f265,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_21),
% 2.13/0.65    inference(avatar_component_clause,[],[f263])).
% 2.13/0.65  fof(f266,plain,(
% 2.13/0.65    spl4_21 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.13/0.65    inference(avatar_split_clause,[],[f261,f154,f149,f144,f124,f114,f104,f263])).
% 2.13/0.65  fof(f261,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.13/0.65    inference(subsumption_resolution,[],[f260,f156])).
% 2.13/0.65  fof(f260,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.13/0.65    inference(subsumption_resolution,[],[f259,f151])).
% 2.13/0.65  fof(f259,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.13/0.65    inference(subsumption_resolution,[],[f258,f146])).
% 2.13/0.65  fof(f258,plain,(
% 2.13/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.13/0.65    inference(subsumption_resolution,[],[f257,f116])).
% 2.13/0.65  fof(f257,plain,(
% 2.13/0.65    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.13/0.65    inference(subsumption_resolution,[],[f256,f106])).
% 2.13/0.65  fof(f256,plain,(
% 2.13/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.13/0.65    inference(trivial_inequality_removal,[],[f253])).
% 2.13/0.65  fof(f253,plain,(
% 2.13/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.13/0.65    inference(superposition,[],[f249,f126])).
% 2.13/0.65  fof(f243,plain,(
% 2.13/0.65    spl4_20 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.13/0.65    inference(avatar_split_clause,[],[f238,f160,f154,f144,f139,f129,f240])).
% 2.13/0.65  fof(f238,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.13/0.65    inference(subsumption_resolution,[],[f237,f156])).
% 2.13/0.65  fof(f237,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.13/0.65    inference(subsumption_resolution,[],[f236,f146])).
% 2.13/0.65  fof(f236,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.13/0.65    inference(subsumption_resolution,[],[f235,f141])).
% 2.13/0.65  fof(f235,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.13/0.65    inference(subsumption_resolution,[],[f232,f131])).
% 2.13/0.65  fof(f232,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.13/0.65    inference(superposition,[],[f162,f84])).
% 2.13/0.65  fof(f215,plain,(
% 2.13/0.65    spl4_19 | ~spl4_6 | ~spl4_10),
% 2.13/0.65    inference(avatar_split_clause,[],[f214,f144,f124,f210])).
% 2.13/0.65  fof(f214,plain,(
% 2.13/0.65    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 2.13/0.65    inference(subsumption_resolution,[],[f207,f146])).
% 2.13/0.65  fof(f207,plain,(
% 2.13/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 2.13/0.65    inference(superposition,[],[f126,f85])).
% 2.13/0.65  fof(f85,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f43])).
% 2.13/0.65  fof(f43,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.65    inference(ennf_transformation,[],[f11])).
% 2.13/0.65  fof(f11,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.13/0.65  fof(f192,plain,(
% 2.13/0.65    ~spl4_15 | ~spl4_16 | spl4_1 | ~spl4_4 | ~spl4_12),
% 2.13/0.65    inference(avatar_split_clause,[],[f187,f154,f114,f99,f189,f174])).
% 2.13/0.65  fof(f189,plain,(
% 2.13/0.65    spl4_16 <=> sK3 = k4_relat_1(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.13/0.65  fof(f99,plain,(
% 2.13/0.65    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.13/0.65  fof(f187,plain,(
% 2.13/0.65    sK3 != k4_relat_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_12)),
% 2.13/0.65    inference(subsumption_resolution,[],[f186,f156])).
% 2.13/0.65  fof(f186,plain,(
% 2.13/0.65    sK3 != k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4)),
% 2.13/0.65    inference(subsumption_resolution,[],[f181,f116])).
% 2.13/0.65  fof(f181,plain,(
% 2.13/0.65    sK3 != k4_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 2.13/0.65    inference(superposition,[],[f101,f69])).
% 2.13/0.65  fof(f101,plain,(
% 2.13/0.65    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.13/0.65    inference(avatar_component_clause,[],[f99])).
% 2.13/0.65  fof(f177,plain,(
% 2.13/0.65    spl4_15 | ~spl4_10),
% 2.13/0.65    inference(avatar_split_clause,[],[f166,f144,f174])).
% 2.13/0.65  fof(f166,plain,(
% 2.13/0.65    v1_relat_1(sK2) | ~spl4_10),
% 2.13/0.65    inference(resolution,[],[f92,f146])).
% 2.13/0.65  fof(f92,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f47])).
% 2.13/0.65  fof(f47,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.65    inference(ennf_transformation,[],[f10])).
% 2.13/0.65  fof(f10,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.13/0.65  fof(f172,plain,(
% 2.13/0.65    spl4_14 | ~spl4_7),
% 2.13/0.65    inference(avatar_split_clause,[],[f165,f129,f169])).
% 2.13/0.65  fof(f165,plain,(
% 2.13/0.65    v1_relat_1(sK3) | ~spl4_7),
% 2.13/0.65    inference(resolution,[],[f92,f131])).
% 2.13/0.65  fof(f163,plain,(
% 2.13/0.65    spl4_13 | ~spl4_5),
% 2.13/0.65    inference(avatar_split_clause,[],[f158,f119,f160])).
% 2.13/0.65  fof(f119,plain,(
% 2.13/0.65    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.13/0.65  fof(f158,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.13/0.65    inference(backward_demodulation,[],[f121,f81])).
% 2.13/0.65  fof(f121,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.13/0.65    inference(avatar_component_clause,[],[f119])).
% 2.13/0.65  fof(f157,plain,(
% 2.13/0.65    spl4_12),
% 2.13/0.65    inference(avatar_split_clause,[],[f53,f154])).
% 2.13/0.65  fof(f53,plain,(
% 2.13/0.65    v1_funct_1(sK2)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f51,plain,(
% 2.13/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.13/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f50,f49])).
% 2.13/0.65  fof(f49,plain,(
% 2.13/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.13/0.65    introduced(choice_axiom,[])).
% 2.13/0.65  fof(f50,plain,(
% 2.13/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.13/0.65    introduced(choice_axiom,[])).
% 2.13/0.65  fof(f24,plain,(
% 2.13/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.13/0.65    inference(flattening,[],[f23])).
% 2.13/0.65  fof(f23,plain,(
% 2.13/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.13/0.65    inference(ennf_transformation,[],[f21])).
% 2.13/0.65  fof(f21,negated_conjecture,(
% 2.13/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.13/0.65    inference(negated_conjecture,[],[f20])).
% 2.13/0.65  fof(f20,conjecture,(
% 2.13/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.13/0.65  fof(f152,plain,(
% 2.13/0.65    spl4_11),
% 2.13/0.65    inference(avatar_split_clause,[],[f54,f149])).
% 2.13/0.65  fof(f54,plain,(
% 2.13/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f147,plain,(
% 2.13/0.65    spl4_10),
% 2.13/0.65    inference(avatar_split_clause,[],[f55,f144])).
% 2.13/0.65  fof(f55,plain,(
% 2.13/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f142,plain,(
% 2.13/0.65    spl4_9),
% 2.13/0.65    inference(avatar_split_clause,[],[f56,f139])).
% 2.13/0.65  fof(f56,plain,(
% 2.13/0.65    v1_funct_1(sK3)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f137,plain,(
% 2.13/0.65    spl4_8),
% 2.13/0.65    inference(avatar_split_clause,[],[f57,f134])).
% 2.13/0.65  fof(f57,plain,(
% 2.13/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f132,plain,(
% 2.13/0.65    spl4_7),
% 2.13/0.65    inference(avatar_split_clause,[],[f58,f129])).
% 2.13/0.65  fof(f58,plain,(
% 2.13/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f127,plain,(
% 2.13/0.65    spl4_6),
% 2.13/0.65    inference(avatar_split_clause,[],[f59,f124])).
% 2.13/0.65  fof(f59,plain,(
% 2.13/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f122,plain,(
% 2.13/0.65    spl4_5),
% 2.13/0.65    inference(avatar_split_clause,[],[f60,f119])).
% 2.13/0.65  fof(f60,plain,(
% 2.13/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f117,plain,(
% 2.13/0.65    spl4_4),
% 2.13/0.65    inference(avatar_split_clause,[],[f61,f114])).
% 2.13/0.65  fof(f61,plain,(
% 2.13/0.65    v2_funct_1(sK2)),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f112,plain,(
% 2.13/0.65    ~spl4_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f62,f109])).
% 2.13/0.65  fof(f62,plain,(
% 2.13/0.65    k1_xboole_0 != sK0),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f107,plain,(
% 2.13/0.65    ~spl4_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f63,f104])).
% 2.13/0.65  fof(f63,plain,(
% 2.13/0.65    k1_xboole_0 != sK1),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  fof(f102,plain,(
% 2.13/0.65    ~spl4_1),
% 2.13/0.65    inference(avatar_split_clause,[],[f64,f99])).
% 2.13/0.65  fof(f64,plain,(
% 2.13/0.65    k2_funct_1(sK2) != sK3),
% 2.13/0.65    inference(cnf_transformation,[],[f51])).
% 2.13/0.65  % SZS output end Proof for theBenchmark
% 2.13/0.65  % (13128)------------------------------
% 2.13/0.65  % (13128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (13128)Termination reason: Refutation
% 2.13/0.65  
% 2.13/0.65  % (13128)Memory used [KB]: 7675
% 2.13/0.65  % (13128)Time elapsed: 0.210 s
% 2.13/0.65  % (13128)------------------------------
% 2.13/0.65  % (13128)------------------------------
% 2.13/0.65  % (13106)Success in time 0.283 s
%------------------------------------------------------------------------------
