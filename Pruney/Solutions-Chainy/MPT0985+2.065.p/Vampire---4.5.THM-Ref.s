%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:09 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 370 expanded)
%              Number of leaves         :   53 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  544 (1062 expanded)
%              Number of equality atoms :  110 ( 222 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f127,f132,f140,f150,f165,f170,f182,f183,f274,f286,f324,f342,f353,f361,f408,f421,f438,f533,f535,f536,f550,f589,f591,f693,f769,f1065,f1075,f1091,f1148,f1181,f1192])).

fof(f1192,plain,
    ( ~ spl3_53
    | spl3_6
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_137 ),
    inference(avatar_split_clause,[],[f1191,f1088,f547,f530,f116,f434])).

fof(f434,plain,
    ( spl3_53
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f116,plain,
    ( spl3_6
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f530,plain,
    ( spl3_65
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f547,plain,
    ( spl3_67
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f1088,plain,
    ( spl3_137
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).

fof(f1191,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_65
    | ~ spl3_67
    | ~ spl3_137 ),
    inference(forward_demodulation,[],[f1190,f1090])).

fof(f1090,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_137 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f1190,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_65
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f1189,f549])).

fof(f549,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f547])).

fof(f1189,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f1188,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1188,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_6
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f118,f532])).

fof(f532,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f530])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1181,plain,
    ( ~ spl3_36
    | spl3_140 ),
    inference(avatar_contradiction_clause,[],[f1180])).

fof(f1180,plain,
    ( $false
    | ~ spl3_36
    | spl3_140 ),
    inference(resolution,[],[f1147,f463])).

fof(f463,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_36 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f461,f403])).

fof(f403,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f398,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl3_36
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f398,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f461,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f454,f52])).

fof(f454,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f86,f84])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1147,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_140 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1145,plain,
    ( spl3_140
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).

fof(f1148,plain,
    ( ~ spl3_140
    | spl3_97
    | ~ spl3_137 ),
    inference(avatar_split_clause,[],[f1121,f1088,f766,f1145])).

fof(f766,plain,
    ( spl3_97
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f1121,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_97
    | ~ spl3_137 ),
    inference(backward_demodulation,[],[f768,f1090])).

fof(f768,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_97 ),
    inference(avatar_component_clause,[],[f766])).

fof(f1091,plain,
    ( spl3_137
    | ~ spl3_9
    | ~ spl3_135 ),
    inference(avatar_split_clause,[],[f1080,f1071,f129,f1088])).

fof(f129,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1071,plain,
    ( spl3_135
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).

fof(f1080,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_135 ),
    inference(resolution,[],[f1073,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f131])).

fof(f131,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f1073,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_135 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f1075,plain,
    ( spl3_135
    | ~ spl3_9
    | ~ spl3_118 ),
    inference(avatar_split_clause,[],[f1069,f949,f129,f1071])).

fof(f949,plain,
    ( spl3_118
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f1069,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_118 ),
    inference(resolution,[],[f950,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f950,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_118 ),
    inference(avatar_component_clause,[],[f949])).

fof(f1065,plain,
    ( spl3_118
    | ~ spl3_39
    | ~ spl3_67
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f1064,f690,f547,f339,f949])).

fof(f339,plain,
    ( spl3_39
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f690,plain,
    ( spl3_87
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f1064,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_39
    | ~ spl3_67
    | ~ spl3_87 ),
    inference(forward_demodulation,[],[f1063,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1063,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ spl3_39
    | ~ spl3_67
    | ~ spl3_87 ),
    inference(forward_demodulation,[],[f1062,f692])).

fof(f692,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f690])).

fof(f1062,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl3_39
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f341,f549])).

fof(f341,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f339])).

fof(f769,plain,
    ( ~ spl3_97
    | ~ spl3_67
    | spl3_72 ),
    inference(avatar_split_clause,[],[f764,f586,f547,f766])).

fof(f586,plain,
    ( spl3_72
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f764,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl3_67
    | spl3_72 ),
    inference(forward_demodulation,[],[f588,f549])).

fof(f588,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_72 ),
    inference(avatar_component_clause,[],[f586])).

fof(f693,plain,
    ( spl3_87
    | ~ spl3_36
    | ~ spl3_42
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f688,f547,f358,f321,f690])).

fof(f358,plain,
    ( spl3_42
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f688,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_36
    | ~ spl3_42
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f642,f323])).

fof(f642,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_42
    | ~ spl3_67 ),
    inference(backward_demodulation,[],[f360,f549])).

fof(f360,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f358])).

fof(f591,plain,
    ( ~ spl3_9
    | spl3_14
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f590,f530,f162,f129])).

fof(f162,plain,
    ( spl3_14
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f590,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_14
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f564,f83])).

fof(f564,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl3_14
    | ~ spl3_65 ),
    inference(backward_demodulation,[],[f164,f532])).

fof(f164,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f589,plain,
    ( ~ spl3_72
    | spl3_7
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f563,f530,f120,f586])).

fof(f120,plain,
    ( spl3_7
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f563,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_7
    | ~ spl3_65 ),
    inference(backward_demodulation,[],[f122,f532])).

fof(f122,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f550,plain,
    ( spl3_67
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f539,f158,f129,f547])).

fof(f158,plain,
    ( spl3_13
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f539,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(resolution,[],[f160,f152])).

fof(f160,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f536,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f535,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f533,plain,
    ( ~ spl3_4
    | spl3_64
    | spl3_65
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f520,f101,f530,f526,f106])).

fof(f106,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f526,plain,
    ( spl3_64
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f101,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f520,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f80,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f438,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f421,plain,
    ( spl3_50
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f416,f101,f91,f418])).

fof(f418,plain,
    ( spl3_50
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f91,plain,
    ( spl3_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f416,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f411,f93])).

fof(f93,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f411,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f74,f103])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f408,plain,
    ( spl3_49
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f399,f101,f405])).

fof(f405,plain,
    ( spl3_49
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f399,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f103])).

fof(f361,plain,
    ( spl3_42
    | ~ spl3_12
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f356,f96,f111,f147,f358])).

fof(f147,plain,
    ( spl3_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f96,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f356,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f65,f98])).

fof(f98,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f353,plain,
    ( spl3_41
    | ~ spl3_12
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f348,f96,f111,f147,f350])).

fof(f350,plain,
    ( spl3_41
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f348,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f98])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f342,plain,
    ( spl3_39
    | ~ spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f331,f124,f143,f339])).

fof(f143,plain,
    ( spl3_11
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f124,plain,
    ( spl3_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f331,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f125])).

fof(f125,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f324,plain,
    ( spl3_36
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f318,f283,f321])).

fof(f283,plain,
    ( spl3_32
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f318,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_32 ),
    inference(superposition,[],[f82,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f283])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f286,plain,
    ( spl3_32
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f281,f167,f129,f283])).

fof(f167,plain,
    ( spl3_15
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f281,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(resolution,[],[f152,f169])).

fof(f169,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f274,plain,
    ( spl3_30
    | ~ spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f263,f124,f143,f271])).

fof(f271,plain,
    ( spl3_30
  <=> v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f263,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f125])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f183,plain,
    ( spl3_8
    | ~ spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f151,f111,f147,f124])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f63,f113])).

fof(f113,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f182,plain,
    ( spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f173,f101,f147])).

fof(f173,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f103])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f170,plain,
    ( spl3_15
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f156,f136,f129,f167])).

fof(f136,plain,
    ( spl3_10
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f156,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(resolution,[],[f59,f138])).

fof(f138,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f165,plain,
    ( spl3_13
    | ~ spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f154,f101,f162,f158])).

fof(f154,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f103])).

fof(f150,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f141,f111,f147,f143])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f62,f113])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f140,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f134,f136])).

fof(f134,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f54,f84])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f132,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f127,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f45,f124,f120,f116])).

fof(f45,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f114,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (17038)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (17037)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (17035)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (17047)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (17036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (17063)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (17056)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (17046)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (17058)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (17048)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (17044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (17057)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (17034)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (17033)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (17050)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (17039)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (17059)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (17055)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (17062)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (17060)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (17049)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (17043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (17051)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (17051)Refutation not found, incomplete strategy% (17051)------------------------------
% 1.43/0.55  % (17051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (17051)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (17051)Memory used [KB]: 10618
% 1.43/0.55  % (17051)Time elapsed: 0.139 s
% 1.43/0.55  % (17051)------------------------------
% 1.43/0.55  % (17051)------------------------------
% 1.43/0.55  % (17054)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (17052)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (17043)Refutation not found, incomplete strategy% (17043)------------------------------
% 1.43/0.55  % (17043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (17040)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.55  % (17061)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (17042)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (17050)Refutation found. Thanks to Tanya!
% 1.43/0.55  % SZS status Theorem for theBenchmark
% 1.43/0.56  % (17035)Refutation not found, incomplete strategy% (17035)------------------------------
% 1.43/0.56  % (17035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (17035)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (17035)Memory used [KB]: 10874
% 1.43/0.56  % (17035)Time elapsed: 0.130 s
% 1.43/0.56  % (17035)------------------------------
% 1.43/0.56  % (17035)------------------------------
% 1.43/0.56  % (17041)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.56  % (17043)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (17043)Memory used [KB]: 10618
% 1.43/0.56  % (17043)Time elapsed: 0.150 s
% 1.43/0.56  % (17043)------------------------------
% 1.43/0.56  % (17043)------------------------------
% 1.43/0.56  % (17056)Refutation not found, incomplete strategy% (17056)------------------------------
% 1.43/0.56  % (17056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (17056)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (17056)Memory used [KB]: 10874
% 1.43/0.56  % (17056)Time elapsed: 0.099 s
% 1.43/0.56  % (17056)------------------------------
% 1.43/0.56  % (17056)------------------------------
% 1.43/0.56  % (17053)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.56  % (17041)Refutation not found, incomplete strategy% (17041)------------------------------
% 1.43/0.56  % (17041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (17041)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (17041)Memory used [KB]: 10746
% 1.43/0.56  % (17041)Time elapsed: 0.151 s
% 1.43/0.56  % (17041)------------------------------
% 1.43/0.56  % (17041)------------------------------
% 1.65/0.57  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f1193,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f127,f132,f140,f150,f165,f170,f182,f183,f274,f286,f324,f342,f353,f361,f408,f421,f438,f533,f535,f536,f550,f589,f591,f693,f769,f1065,f1075,f1091,f1148,f1181,f1192])).
% 1.65/0.58  fof(f1192,plain,(
% 1.65/0.58    ~spl3_53 | spl3_6 | ~spl3_65 | ~spl3_67 | ~spl3_137),
% 1.65/0.58    inference(avatar_split_clause,[],[f1191,f1088,f547,f530,f116,f434])).
% 1.65/0.58  fof(f434,plain,(
% 1.65/0.58    spl3_53 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 1.65/0.58  fof(f116,plain,(
% 1.65/0.58    spl3_6 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.65/0.58  fof(f530,plain,(
% 1.65/0.58    spl3_65 <=> k1_xboole_0 = sK1),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.65/0.58  fof(f547,plain,(
% 1.65/0.58    spl3_67 <=> k1_xboole_0 = sK2),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 1.65/0.58  fof(f1088,plain,(
% 1.65/0.58    spl3_137 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).
% 1.65/0.58  fof(f1191,plain,(
% 1.65/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_65 | ~spl3_67 | ~spl3_137)),
% 1.65/0.58    inference(forward_demodulation,[],[f1190,f1090])).
% 1.65/0.58  fof(f1090,plain,(
% 1.65/0.58    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_137),
% 1.65/0.58    inference(avatar_component_clause,[],[f1088])).
% 1.65/0.58  fof(f1190,plain,(
% 1.65/0.58    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_65 | ~spl3_67)),
% 1.65/0.58    inference(forward_demodulation,[],[f1189,f549])).
% 1.65/0.58  fof(f549,plain,(
% 1.65/0.58    k1_xboole_0 = sK2 | ~spl3_67),
% 1.65/0.58    inference(avatar_component_clause,[],[f547])).
% 1.65/0.58  fof(f1189,plain,(
% 1.65/0.58    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_65)),
% 1.65/0.58    inference(forward_demodulation,[],[f1188,f84])).
% 1.65/0.58  fof(f84,plain,(
% 1.65/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f69])).
% 1.65/0.58  fof(f69,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.65/0.58  fof(f1188,plain,(
% 1.65/0.58    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_6 | ~spl3_65)),
% 1.65/0.58    inference(forward_demodulation,[],[f118,f532])).
% 1.65/0.58  fof(f532,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | ~spl3_65),
% 1.65/0.58    inference(avatar_component_clause,[],[f530])).
% 1.65/0.58  fof(f118,plain,(
% 1.65/0.58    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_6),
% 1.65/0.58    inference(avatar_component_clause,[],[f116])).
% 1.65/0.58  fof(f1181,plain,(
% 1.65/0.58    ~spl3_36 | spl3_140),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1180])).
% 1.65/0.58  fof(f1180,plain,(
% 1.65/0.58    $false | (~spl3_36 | spl3_140)),
% 1.65/0.58    inference(resolution,[],[f1147,f463])).
% 1.65/0.58  fof(f463,plain,(
% 1.65/0.58    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_36),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f462])).
% 1.65/0.58  fof(f462,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_36),
% 1.65/0.58    inference(forward_demodulation,[],[f461,f403])).
% 1.65/0.58  fof(f403,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl3_36),
% 1.65/0.58    inference(forward_demodulation,[],[f398,f323])).
% 1.65/0.58  fof(f323,plain,(
% 1.65/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_36),
% 1.65/0.58    inference(avatar_component_clause,[],[f321])).
% 1.65/0.58  fof(f321,plain,(
% 1.65/0.58    spl3_36 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.65/0.58  fof(f398,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.65/0.58    inference(resolution,[],[f73,f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f41,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.58  fof(f461,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.65/0.58    inference(resolution,[],[f454,f52])).
% 1.65/0.58  fof(f454,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.65/0.58    inference(forward_demodulation,[],[f86,f84])).
% 1.65/0.58  fof(f86,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f77])).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(flattening,[],[f43])).
% 1.65/0.58  fof(f43,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.65/0.58  fof(f1147,plain,(
% 1.65/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl3_140),
% 1.65/0.58    inference(avatar_component_clause,[],[f1145])).
% 1.65/0.58  fof(f1145,plain,(
% 1.65/0.58    spl3_140 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).
% 1.65/0.58  fof(f1148,plain,(
% 1.65/0.58    ~spl3_140 | spl3_97 | ~spl3_137),
% 1.65/0.58    inference(avatar_split_clause,[],[f1121,f1088,f766,f1145])).
% 1.65/0.58  fof(f766,plain,(
% 1.65/0.58    spl3_97 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 1.65/0.58  fof(f1121,plain,(
% 1.65/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_97 | ~spl3_137)),
% 1.65/0.58    inference(backward_demodulation,[],[f768,f1090])).
% 1.65/0.58  fof(f768,plain,(
% 1.65/0.58    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | spl3_97),
% 1.65/0.58    inference(avatar_component_clause,[],[f766])).
% 1.65/0.58  fof(f1091,plain,(
% 1.65/0.58    spl3_137 | ~spl3_9 | ~spl3_135),
% 1.65/0.58    inference(avatar_split_clause,[],[f1080,f1071,f129,f1088])).
% 1.65/0.58  fof(f129,plain,(
% 1.65/0.58    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.65/0.58  fof(f1071,plain,(
% 1.65/0.58    spl3_135 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).
% 1.65/0.58  fof(f1080,plain,(
% 1.65/0.58    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_9 | ~spl3_135)),
% 1.65/0.58    inference(resolution,[],[f1073,f152])).
% 1.65/0.58  fof(f152,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 1.65/0.58    inference(resolution,[],[f71,f131])).
% 1.65/0.58  fof(f131,plain,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 1.65/0.58    inference(avatar_component_clause,[],[f129])).
% 1.65/0.58  fof(f71,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f39])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.65/0.58  fof(f1073,plain,(
% 1.65/0.58    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_135),
% 1.65/0.58    inference(avatar_component_clause,[],[f1071])).
% 1.65/0.58  fof(f1075,plain,(
% 1.65/0.58    spl3_135 | ~spl3_9 | ~spl3_118),
% 1.65/0.58    inference(avatar_split_clause,[],[f1069,f949,f129,f1071])).
% 1.65/0.58  fof(f949,plain,(
% 1.65/0.58    spl3_118 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 1.65/0.58  fof(f1069,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_118),
% 1.65/0.58    inference(resolution,[],[f950,f59])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.65/0.58  fof(f950,plain,(
% 1.65/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_118),
% 1.65/0.58    inference(avatar_component_clause,[],[f949])).
% 1.65/0.58  fof(f1065,plain,(
% 1.65/0.58    spl3_118 | ~spl3_39 | ~spl3_67 | ~spl3_87),
% 1.65/0.58    inference(avatar_split_clause,[],[f1064,f690,f547,f339,f949])).
% 1.65/0.58  fof(f339,plain,(
% 1.65/0.58    spl3_39 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.65/0.58  fof(f690,plain,(
% 1.65/0.58    spl3_87 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 1.65/0.58  fof(f1064,plain,(
% 1.65/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_39 | ~spl3_67 | ~spl3_87)),
% 1.65/0.58    inference(forward_demodulation,[],[f1063,f83])).
% 1.65/0.58  fof(f83,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.65/0.58    inference(equality_resolution,[],[f70])).
% 1.65/0.58  fof(f70,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f3])).
% 1.65/0.58  fof(f1063,plain,(
% 1.65/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | (~spl3_39 | ~spl3_67 | ~spl3_87)),
% 1.65/0.58    inference(forward_demodulation,[],[f1062,f692])).
% 1.65/0.58  fof(f692,plain,(
% 1.65/0.58    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_87),
% 1.65/0.58    inference(avatar_component_clause,[],[f690])).
% 1.65/0.58  fof(f1062,plain,(
% 1.65/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl3_39 | ~spl3_67)),
% 1.65/0.58    inference(forward_demodulation,[],[f341,f549])).
% 1.65/0.58  fof(f341,plain,(
% 1.65/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_39),
% 1.65/0.58    inference(avatar_component_clause,[],[f339])).
% 1.65/0.58  fof(f769,plain,(
% 1.65/0.58    ~spl3_97 | ~spl3_67 | spl3_72),
% 1.65/0.58    inference(avatar_split_clause,[],[f764,f586,f547,f766])).
% 1.65/0.58  fof(f586,plain,(
% 1.65/0.58    spl3_72 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 1.65/0.58  fof(f764,plain,(
% 1.65/0.58    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (~spl3_67 | spl3_72)),
% 1.65/0.58    inference(forward_demodulation,[],[f588,f549])).
% 1.65/0.58  fof(f588,plain,(
% 1.65/0.58    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl3_72),
% 1.65/0.58    inference(avatar_component_clause,[],[f586])).
% 1.65/0.58  fof(f693,plain,(
% 1.65/0.58    spl3_87 | ~spl3_36 | ~spl3_42 | ~spl3_67),
% 1.65/0.58    inference(avatar_split_clause,[],[f688,f547,f358,f321,f690])).
% 1.65/0.58  fof(f358,plain,(
% 1.65/0.58    spl3_42 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.65/0.58  fof(f688,plain,(
% 1.65/0.58    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_36 | ~spl3_42 | ~spl3_67)),
% 1.65/0.58    inference(forward_demodulation,[],[f642,f323])).
% 1.65/0.58  fof(f642,plain,(
% 1.65/0.58    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_42 | ~spl3_67)),
% 1.65/0.58    inference(backward_demodulation,[],[f360,f549])).
% 1.65/0.58  fof(f360,plain,(
% 1.65/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_42),
% 1.65/0.58    inference(avatar_component_clause,[],[f358])).
% 1.65/0.58  fof(f591,plain,(
% 1.65/0.58    ~spl3_9 | spl3_14 | ~spl3_65),
% 1.65/0.58    inference(avatar_split_clause,[],[f590,f530,f162,f129])).
% 1.65/0.58  fof(f162,plain,(
% 1.65/0.58    spl3_14 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.65/0.58  fof(f590,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | (spl3_14 | ~spl3_65)),
% 1.65/0.58    inference(forward_demodulation,[],[f564,f83])).
% 1.65/0.58  fof(f564,plain,(
% 1.65/0.58    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl3_14 | ~spl3_65)),
% 1.65/0.58    inference(backward_demodulation,[],[f164,f532])).
% 1.65/0.58  fof(f164,plain,(
% 1.65/0.58    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl3_14),
% 1.65/0.58    inference(avatar_component_clause,[],[f162])).
% 1.65/0.58  fof(f589,plain,(
% 1.65/0.58    ~spl3_72 | spl3_7 | ~spl3_65),
% 1.65/0.58    inference(avatar_split_clause,[],[f563,f530,f120,f586])).
% 1.65/0.58  fof(f120,plain,(
% 1.65/0.58    spl3_7 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.65/0.58  fof(f563,plain,(
% 1.65/0.58    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_7 | ~spl3_65)),
% 1.65/0.58    inference(backward_demodulation,[],[f122,f532])).
% 1.65/0.58  fof(f122,plain,(
% 1.65/0.58    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_7),
% 1.65/0.58    inference(avatar_component_clause,[],[f120])).
% 1.65/0.58  fof(f550,plain,(
% 1.65/0.58    spl3_67 | ~spl3_9 | ~spl3_13),
% 1.65/0.58    inference(avatar_split_clause,[],[f539,f158,f129,f547])).
% 1.65/0.58  fof(f158,plain,(
% 1.65/0.58    spl3_13 <=> v1_xboole_0(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.65/0.58  fof(f539,plain,(
% 1.65/0.58    k1_xboole_0 = sK2 | (~spl3_9 | ~spl3_13)),
% 1.65/0.58    inference(resolution,[],[f160,f152])).
% 1.65/0.58  fof(f160,plain,(
% 1.65/0.58    v1_xboole_0(sK2) | ~spl3_13),
% 1.65/0.58    inference(avatar_component_clause,[],[f158])).
% 1.65/0.58  fof(f536,plain,(
% 1.65/0.58    sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 1.65/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.58  fof(f535,plain,(
% 1.65/0.58    sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 1.65/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.58  fof(f533,plain,(
% 1.65/0.58    ~spl3_4 | spl3_64 | spl3_65 | ~spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f520,f101,f530,f526,f106])).
% 1.65/0.58  fof(f106,plain,(
% 1.65/0.58    spl3_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.65/0.58  fof(f526,plain,(
% 1.65/0.58    spl3_64 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.65/0.58  fof(f101,plain,(
% 1.65/0.58    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.65/0.58  fof(f520,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 1.65/0.58    inference(resolution,[],[f80,f103])).
% 1.65/0.58  fof(f103,plain,(
% 1.65/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 1.65/0.58    inference(avatar_component_clause,[],[f101])).
% 1.65/0.58  fof(f80,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f44])).
% 1.65/0.58  fof(f438,plain,(
% 1.65/0.58    k1_xboole_0 != k6_partfun1(k1_xboole_0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.58  fof(f421,plain,(
% 1.65/0.58    spl3_50 | ~spl3_1 | ~spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f416,f101,f91,f418])).
% 1.65/0.58  fof(f418,plain,(
% 1.65/0.58    spl3_50 <=> sK1 = k2_relat_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.65/0.58  fof(f91,plain,(
% 1.65/0.58    spl3_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.65/0.58  fof(f416,plain,(
% 1.65/0.58    sK1 = k2_relat_1(sK2) | (~spl3_1 | ~spl3_3)),
% 1.65/0.58    inference(forward_demodulation,[],[f411,f93])).
% 1.65/0.58  fof(f93,plain,(
% 1.65/0.58    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f91])).
% 1.65/0.58  fof(f411,plain,(
% 1.65/0.58    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_3),
% 1.65/0.58    inference(resolution,[],[f74,f103])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f16])).
% 1.65/0.58  fof(f16,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.65/0.58  fof(f408,plain,(
% 1.65/0.58    spl3_49 | ~spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f399,f101,f405])).
% 1.65/0.58  fof(f405,plain,(
% 1.65/0.58    spl3_49 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.65/0.58  fof(f399,plain,(
% 1.65/0.58    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_3),
% 1.65/0.58    inference(resolution,[],[f73,f103])).
% 1.65/0.58  fof(f361,plain,(
% 1.65/0.58    spl3_42 | ~spl3_12 | ~spl3_5 | ~spl3_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f356,f96,f111,f147,f358])).
% 1.65/0.58  fof(f147,plain,(
% 1.65/0.58    spl3_12 <=> v1_relat_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.65/0.58  fof(f111,plain,(
% 1.65/0.58    spl3_5 <=> v1_funct_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.65/0.58  fof(f96,plain,(
% 1.65/0.58    spl3_2 <=> v2_funct_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.65/0.58  fof(f356,plain,(
% 1.65/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 1.65/0.58    inference(resolution,[],[f65,f98])).
% 1.65/0.58  fof(f98,plain,(
% 1.65/0.58    v2_funct_1(sK2) | ~spl3_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f96])).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f12])).
% 1.65/0.58  fof(f12,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.65/0.58  fof(f353,plain,(
% 1.65/0.58    spl3_41 | ~spl3_12 | ~spl3_5 | ~spl3_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f348,f96,f111,f147,f350])).
% 1.65/0.58  fof(f350,plain,(
% 1.65/0.58    spl3_41 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.65/0.58  fof(f348,plain,(
% 1.65/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 1.65/0.58    inference(resolution,[],[f64,f98])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f35])).
% 1.65/0.58  fof(f342,plain,(
% 1.65/0.58    spl3_39 | ~spl3_11 | ~spl3_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f331,f124,f143,f339])).
% 1.65/0.58  fof(f143,plain,(
% 1.65/0.58    spl3_11 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.65/0.58  fof(f124,plain,(
% 1.65/0.58    spl3_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.65/0.58  fof(f331,plain,(
% 1.65/0.58    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_8),
% 1.65/0.58    inference(resolution,[],[f61,f125])).
% 1.65/0.58  fof(f125,plain,(
% 1.65/0.58    v1_funct_1(k2_funct_1(sK2)) | ~spl3_8),
% 1.65/0.58    inference(avatar_component_clause,[],[f124])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f30])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f20])).
% 1.65/0.58  fof(f20,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.65/0.58  fof(f324,plain,(
% 1.65/0.58    spl3_36 | ~spl3_32),
% 1.65/0.58    inference(avatar_split_clause,[],[f318,f283,f321])).
% 1.65/0.58  fof(f283,plain,(
% 1.65/0.58    spl3_32 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.65/0.58  fof(f318,plain,(
% 1.65/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_32),
% 1.65/0.58    inference(superposition,[],[f82,f285])).
% 1.65/0.58  fof(f285,plain,(
% 1.65/0.58    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl3_32),
% 1.65/0.58    inference(avatar_component_clause,[],[f283])).
% 1.65/0.58  fof(f82,plain,(
% 1.65/0.58    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.65/0.58    inference(definition_unfolding,[],[f55,f53])).
% 1.65/0.58  fof(f53,plain,(
% 1.65/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,axiom,(
% 1.65/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.65/0.58    inference(cnf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.65/0.58  fof(f286,plain,(
% 1.65/0.58    spl3_32 | ~spl3_9 | ~spl3_15),
% 1.65/0.58    inference(avatar_split_clause,[],[f281,f167,f129,f283])).
% 1.65/0.58  fof(f167,plain,(
% 1.65/0.58    spl3_15 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.65/0.58  fof(f281,plain,(
% 1.65/0.58    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl3_9 | ~spl3_15)),
% 1.65/0.58    inference(resolution,[],[f152,f169])).
% 1.65/0.58  fof(f169,plain,(
% 1.65/0.58    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl3_15),
% 1.65/0.58    inference(avatar_component_clause,[],[f167])).
% 1.65/0.58  fof(f274,plain,(
% 1.65/0.58    spl3_30 | ~spl3_11 | ~spl3_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f263,f124,f143,f271])).
% 1.65/0.58  fof(f271,plain,(
% 1.65/0.58    spl3_30 <=> v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.65/0.58  fof(f263,plain,(
% 1.65/0.58    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_8),
% 1.65/0.58    inference(resolution,[],[f60,f125])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f31])).
% 1.65/0.58  fof(f183,plain,(
% 1.65/0.58    spl3_8 | ~spl3_12 | ~spl3_5),
% 1.65/0.58    inference(avatar_split_clause,[],[f151,f111,f147,f124])).
% 1.65/0.58  fof(f151,plain,(
% 1.65/0.58    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.65/0.58    inference(resolution,[],[f63,f113])).
% 1.65/0.58  fof(f113,plain,(
% 1.65/0.58    v1_funct_1(sK2) | ~spl3_5),
% 1.65/0.58    inference(avatar_component_clause,[],[f111])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.65/0.58  fof(f182,plain,(
% 1.65/0.58    spl3_12 | ~spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f173,f101,f147])).
% 1.65/0.58  fof(f173,plain,(
% 1.65/0.58    v1_relat_1(sK2) | ~spl3_3),
% 1.65/0.58    inference(resolution,[],[f72,f103])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f40])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.58  fof(f170,plain,(
% 1.65/0.58    spl3_15 | ~spl3_9 | ~spl3_10),
% 1.65/0.58    inference(avatar_split_clause,[],[f156,f136,f129,f167])).
% 1.65/0.58  fof(f136,plain,(
% 1.65/0.58    spl3_10 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.65/0.58  fof(f156,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl3_10),
% 1.65/0.58    inference(resolution,[],[f59,f138])).
% 1.65/0.58  fof(f138,plain,(
% 1.65/0.58    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f136])).
% 1.65/0.58  fof(f165,plain,(
% 1.65/0.58    spl3_13 | ~spl3_14 | ~spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f154,f101,f162,f158])).
% 1.65/0.58  fof(f154,plain,(
% 1.65/0.58    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2) | ~spl3_3),
% 1.65/0.58    inference(resolution,[],[f59,f103])).
% 1.65/0.58  fof(f150,plain,(
% 1.65/0.58    spl3_11 | ~spl3_12 | ~spl3_5),
% 1.65/0.58    inference(avatar_split_clause,[],[f141,f111,f147,f143])).
% 1.65/0.58  fof(f141,plain,(
% 1.65/0.58    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.65/0.58    inference(resolution,[],[f62,f113])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f140,plain,(
% 1.65/0.58    spl3_10),
% 1.65/0.58    inference(avatar_split_clause,[],[f134,f136])).
% 1.65/0.58  fof(f134,plain,(
% 1.65/0.58    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.58    inference(superposition,[],[f54,f84])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.65/0.58    inference(pure_predicate_removal,[],[f18])).
% 1.65/0.58  fof(f18,axiom,(
% 1.65/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.65/0.58  fof(f132,plain,(
% 1.65/0.58    spl3_9),
% 1.65/0.58    inference(avatar_split_clause,[],[f51,f129])).
% 1.65/0.58  fof(f51,plain,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    inference(cnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.65/0.58  fof(f127,plain,(
% 1.65/0.58    ~spl3_6 | ~spl3_7 | ~spl3_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f45,f124,f120,f116])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f22])).
% 1.65/0.58  fof(f22,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.65/0.58    inference(negated_conjecture,[],[f21])).
% 1.65/0.58  fof(f21,conjecture,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.65/0.58  fof(f114,plain,(
% 1.65/0.58    spl3_5),
% 1.65/0.58    inference(avatar_split_clause,[],[f46,f111])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    v1_funct_1(sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f109,plain,(
% 1.65/0.58    spl3_4),
% 1.65/0.58    inference(avatar_split_clause,[],[f47,f106])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f104,plain,(
% 1.65/0.58    spl3_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f48,f101])).
% 1.65/0.58  fof(f48,plain,(
% 1.65/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f99,plain,(
% 1.65/0.58    spl3_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f49,f96])).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    v2_funct_1(sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f94,plain,(
% 1.65/0.58    spl3_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f50,f91])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (17050)------------------------------
% 1.65/0.58  % (17050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (17050)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (17050)Memory used [KB]: 11513
% 1.65/0.58  % (17050)Time elapsed: 0.146 s
% 1.65/0.58  % (17050)------------------------------
% 1.65/0.58  % (17050)------------------------------
% 1.65/0.58  % (17032)Success in time 0.217 s
%------------------------------------------------------------------------------
