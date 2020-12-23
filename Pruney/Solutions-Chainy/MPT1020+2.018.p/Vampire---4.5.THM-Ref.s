%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:42 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 474 expanded)
%              Number of leaves         :   56 ( 212 expanded)
%              Depth                    :   13
%              Number of atoms          :  814 (1956 expanded)
%              Number of equality atoms :  117 ( 219 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f311,f321,f428,f429,f430,f431,f434,f437,f446,f477,f535,f538,f572,f577,f583,f605,f606,f642,f681,f831,f857,f862,f1003,f1016,f1078,f1095,f1114,f1195,f1296])).

fof(f1296,plain,
    ( spl4_93
    | ~ spl4_61
    | ~ spl4_70
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1295,f1165,f859,f854,f828,f646,f1111])).

fof(f1111,plain,
    ( spl4_93
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f646,plain,
    ( spl4_61
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f828,plain,
    ( spl4_70
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f854,plain,
    ( spl4_75
  <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f859,plain,
    ( spl4_76
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1165,plain,
    ( spl4_96
  <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1295,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_61
    | ~ spl4_70
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(subsumption_resolution,[],[f1294,f648])).

fof(f648,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f646])).

fof(f1294,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_70
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1293,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1293,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_70
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1292,f94])).

fof(f1292,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_70
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(subsumption_resolution,[],[f1291,f830])).

fof(f830,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f828])).

fof(f1291,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_96 ),
    inference(subsumption_resolution,[],[f1290,f861])).

fof(f861,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1290,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl4_75
    | ~ spl4_96 ),
    inference(subsumption_resolution,[],[f1259,f856])).

fof(f856,plain,
    ( v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f854])).

fof(f1259,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl4_96 ),
    inference(superposition,[],[f72,f1167])).

fof(f1167,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f1195,plain,
    ( spl4_96
    | ~ spl4_26
    | ~ spl4_39
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f1194,f676,f470,f370,f1165])).

fof(f370,plain,
    ( spl4_26
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f470,plain,
    ( spl4_39
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f676,plain,
    ( spl4_63
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f1194,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ spl4_26
    | ~ spl4_39
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f1193,f472])).

fof(f472,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f470])).

fof(f1193,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0)
    | ~ spl4_26
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f372,f678])).

fof(f678,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f676])).

fof(f372,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1114,plain,
    ( ~ spl4_93
    | spl4_91 ),
    inference(avatar_split_clause,[],[f1109,f1091,f1111])).

fof(f1091,plain,
    ( spl4_91
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1109,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_91 ),
    inference(forward_demodulation,[],[f1102,f94])).

fof(f1102,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl4_91 ),
    inference(unit_resulting_resolution,[],[f64,f1093,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f1093,plain,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1095,plain,
    ( ~ spl4_91
    | spl4_90 ),
    inference(avatar_split_clause,[],[f1083,f1075,f1091])).

fof(f1075,plain,
    ( spl4_90
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1083,plain,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0))
    | spl4_90 ),
    inference(unit_resulting_resolution,[],[f64,f1077,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f1077,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | spl4_90 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f1078,plain,
    ( ~ spl4_90
    | ~ spl4_63
    | spl4_85 ),
    inference(avatar_split_clause,[],[f1073,f1000,f676,f1075])).

fof(f1000,plain,
    ( spl4_85
  <=> k1_xboole_0 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f1073,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | ~ spl4_63
    | spl4_85 ),
    inference(forward_demodulation,[],[f1002,f678])).

fof(f1002,plain,
    ( k1_xboole_0 != k2_funct_1(sK1)
    | spl4_85 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1016,plain,
    ( spl4_61
    | ~ spl4_52
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f1008,f676,f580,f646])).

fof(f580,plain,
    ( spl4_52
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1008,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_52
    | ~ spl4_63 ),
    inference(backward_demodulation,[],[f582,f678])).

fof(f582,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f580])).

fof(f1003,plain,
    ( ~ spl4_85
    | spl4_40
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f998,f638,f474,f1000])).

fof(f474,plain,
    ( spl4_40
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f638,plain,
    ( spl4_60
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f998,plain,
    ( k1_xboole_0 != k2_funct_1(sK1)
    | spl4_40
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f475,f640])).

fof(f640,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f638])).

fof(f475,plain,
    ( sK2 != k2_funct_1(sK1)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f474])).

fof(f862,plain,
    ( spl4_76
    | ~ spl4_51
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f823,f638,f574,f859])).

fof(f574,plain,
    ( spl4_51
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f823,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_51
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f576,f640])).

fof(f576,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f574])).

fof(f857,plain,
    ( spl4_75
    | ~ spl4_50
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f822,f638,f569,f854])).

fof(f569,plain,
    ( spl4_50
  <=> v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f822,plain,
    ( v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_50
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f571,f640])).

fof(f571,plain,
    ( v3_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f569])).

fof(f831,plain,
    ( spl4_70
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f815,f638,f124,f828])).

fof(f124,plain,
    ( spl4_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f815,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f126,f640])).

fof(f126,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f681,plain,
    ( spl4_63
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f661,f425,f676])).

fof(f425,plain,
    ( spl4_37
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f661,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f64,f427,f81])).

fof(f427,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f425])).

fof(f642,plain,
    ( spl4_60
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f630,f308,f638])).

fof(f308,plain,
    ( spl4_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f630,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f64,f310,f81])).

fof(f310,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f308])).

fof(f606,plain,
    ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | sK2 != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f605,plain,
    ( spl4_23
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | spl4_23
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f549,f64])).

fof(f549,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_23
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f306,f472])).

fof(f306,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_23
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f583,plain,
    ( spl4_52
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f578,f470,f129,f580])).

fof(f129,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f578,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f544,f94])).

fof(f544,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f131,f472])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f577,plain,
    ( spl4_51
    | ~ spl4_5
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f543,f470,f119,f574])).

fof(f119,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f543,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f121,f472])).

fof(f121,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f572,plain,
    ( spl4_50
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f542,f470,f114,f569])).

fof(f114,plain,
    ( spl4_4
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f542,plain,
    ( v3_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f116,f472])).

fof(f116,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f538,plain,
    ( spl4_46
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f536,f420,f410,f400,f531])).

fof(f531,plain,
    ( spl4_46
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f400,plain,
    ( spl4_32
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f410,plain,
    ( spl4_34
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f420,plain,
    ( spl4_36
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f536,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f422,f402,f412,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f412,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f410])).

fof(f402,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f400])).

fof(f422,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f420])).

fof(f535,plain,
    ( k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1)
    | sK0 != k2_relat_1(sK1)
    | sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f477,plain,
    ( ~ spl4_38
    | ~ spl4_33
    | spl4_39
    | spl4_40
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f464,f144,f139,f129,f124,f119,f109,f104,f474,f470,f405,f466])).

fof(f466,plain,
    ( spl4_38
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f405,plain,
    ( spl4_33
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f104,plain,
    ( spl4_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f139,plain,
    ( spl4_9
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f144,plain,
    ( spl4_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f464,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f463,f146])).

fof(f146,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f463,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f462,f141])).

fof(f141,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f462,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f461,f131])).

fof(f461,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f460,f126])).

fof(f460,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f459,f121])).

fof(f459,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f456,f111])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f456,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f106,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f446,plain,
    ( spl4_26
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f445,f144,f139,f134,f129,f370])).

fof(f134,plain,
    ( spl4_8
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f445,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f444,f146])).

fof(f444,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f443,f141])).

fof(f443,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f362,f136])).

fof(f136,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f362,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f437,plain,
    ( spl4_32
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f436,f144,f134,f129,f400])).

fof(f436,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f435,f146])).

fof(f435,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f348,f136])).

fof(f348,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f434,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f433,f144,f134,f129,f405])).

fof(f433,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f432,f146])).

fof(f432,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f347,f136])).

fof(f347,plain,
    ( v2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f431,plain,
    ( spl4_34
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f346,f129,f410])).

fof(f346,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f430,plain,
    ( spl4_35
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f345,f129,f415])).

fof(f415,plain,
    ( spl4_35
  <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f345,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f429,plain,
    ( spl4_36
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f344,f129,f420])).

fof(f344,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f428,plain,
    ( ~ spl4_23
    | spl4_37
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f343,f129,f425,f304])).

fof(f343,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f131,f65])).

fof(f321,plain,
    ( spl4_17
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f236,f109,f274])).

fof(f274,plain,
    ( spl4_17
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f236,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f311,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f222,f109,f308,f304])).

fof(f222,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f65])).

fof(f147,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f54,f144])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f142,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f55,f139])).

fof(f55,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f57,f129])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f124])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f59,f119])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f62,f104])).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f99])).

fof(f99,plain,
    ( spl4_1
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:04:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (9633)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (9628)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9651)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (9652)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (9641)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (9654)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (9653)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (9649)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (9650)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (9643)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (9630)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (9632)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9627)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9628)Refutation not found, incomplete strategy% (9628)------------------------------
% 0.22/0.54  % (9628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9629)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (9626)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9635)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (9647)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (9636)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (9646)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (9645)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (9628)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9628)Memory used [KB]: 10874
% 0.22/0.55  % (9628)Time elapsed: 0.127 s
% 0.22/0.55  % (9628)------------------------------
% 0.22/0.55  % (9628)------------------------------
% 0.22/0.55  % (9639)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (9642)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (9640)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (9644)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (9638)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (9648)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (9637)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9634)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (9631)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (9634)Refutation not found, incomplete strategy% (9634)------------------------------
% 0.22/0.56  % (9634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9634)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9634)Memory used [KB]: 10746
% 0.22/0.56  % (9634)Time elapsed: 0.149 s
% 0.22/0.56  % (9634)------------------------------
% 0.22/0.56  % (9634)------------------------------
% 0.22/0.57  % (9655)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.58  % (9651)Refutation found. Thanks to Tanya!
% 1.69/0.58  % SZS status Theorem for theBenchmark
% 1.69/0.59  % (9648)Refutation not found, incomplete strategy% (9648)------------------------------
% 1.69/0.59  % (9648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (9648)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (9648)Memory used [KB]: 11257
% 1.69/0.59  % (9648)Time elapsed: 0.178 s
% 1.69/0.59  % (9648)------------------------------
% 1.69/0.59  % (9648)------------------------------
% 1.69/0.59  % SZS output start Proof for theBenchmark
% 1.69/0.59  fof(f1297,plain,(
% 1.69/0.59    $false),
% 1.69/0.59    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f311,f321,f428,f429,f430,f431,f434,f437,f446,f477,f535,f538,f572,f577,f583,f605,f606,f642,f681,f831,f857,f862,f1003,f1016,f1078,f1095,f1114,f1195,f1296])).
% 1.69/0.59  fof(f1296,plain,(
% 1.69/0.59    spl4_93 | ~spl4_61 | ~spl4_70 | ~spl4_75 | ~spl4_76 | ~spl4_96),
% 1.69/0.59    inference(avatar_split_clause,[],[f1295,f1165,f859,f854,f828,f646,f1111])).
% 1.69/0.59  fof(f1111,plain,(
% 1.69/0.59    spl4_93 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 1.69/0.59  fof(f646,plain,(
% 1.69/0.59    spl4_61 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.69/0.59  fof(f828,plain,(
% 1.69/0.59    spl4_70 <=> v1_funct_1(k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.69/0.59  fof(f854,plain,(
% 1.69/0.59    spl4_75 <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.69/0.59  fof(f859,plain,(
% 1.69/0.59    spl4_76 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.69/0.59  fof(f1165,plain,(
% 1.69/0.59    spl4_96 <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 1.69/0.59  fof(f1295,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_61 | ~spl4_70 | ~spl4_75 | ~spl4_76 | ~spl4_96)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1294,f648])).
% 1.69/0.59  fof(f648,plain,(
% 1.69/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_61),
% 1.69/0.59    inference(avatar_component_clause,[],[f646])).
% 1.69/0.59  fof(f1294,plain,(
% 1.69/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_70 | ~spl4_75 | ~spl4_76 | ~spl4_96)),
% 1.69/0.59    inference(forward_demodulation,[],[f1293,f94])).
% 1.69/0.59  fof(f94,plain,(
% 1.69/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.69/0.59    inference(equality_resolution,[],[f80])).
% 1.69/0.59  fof(f80,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f52])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.69/0.59    inference(flattening,[],[f51])).
% 1.69/0.59  fof(f51,plain,(
% 1.69/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.69/0.59    inference(nnf_transformation,[],[f4])).
% 1.69/0.59  fof(f4,axiom,(
% 1.69/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.69/0.59  fof(f1293,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_70 | ~spl4_75 | ~spl4_76 | ~spl4_96)),
% 1.69/0.59    inference(forward_demodulation,[],[f1292,f94])).
% 1.69/0.59  fof(f1292,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_70 | ~spl4_75 | ~spl4_76 | ~spl4_96)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1291,f830])).
% 1.69/0.59  fof(f830,plain,(
% 1.69/0.59    v1_funct_1(k1_xboole_0) | ~spl4_70),
% 1.69/0.59    inference(avatar_component_clause,[],[f828])).
% 1.69/0.59  fof(f1291,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl4_75 | ~spl4_76 | ~spl4_96)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1290,f861])).
% 1.69/0.59  fof(f861,plain,(
% 1.69/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_76),
% 1.69/0.59    inference(avatar_component_clause,[],[f859])).
% 1.69/0.59  fof(f1290,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl4_75 | ~spl4_96)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1259,f856])).
% 1.69/0.59  fof(f856,plain,(
% 1.69/0.59    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_75),
% 1.69/0.59    inference(avatar_component_clause,[],[f854])).
% 1.69/0.59  fof(f1259,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl4_96),
% 1.69/0.59    inference(superposition,[],[f72,f1167])).
% 1.69/0.59  fof(f1167,plain,(
% 1.69/0.59    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | ~spl4_96),
% 1.69/0.59    inference(avatar_component_clause,[],[f1165])).
% 1.69/0.59  fof(f72,plain,(
% 1.69/0.59    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f28])).
% 1.69/0.59  fof(f28,plain,(
% 1.69/0.59    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.69/0.59    inference(flattening,[],[f27])).
% 1.69/0.59  fof(f27,plain,(
% 1.69/0.59    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f13])).
% 1.69/0.59  fof(f13,axiom,(
% 1.69/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.69/0.59  fof(f1195,plain,(
% 1.69/0.59    spl4_96 | ~spl4_26 | ~spl4_39 | ~spl4_63),
% 1.69/0.59    inference(avatar_split_clause,[],[f1194,f676,f470,f370,f1165])).
% 1.69/0.59  fof(f370,plain,(
% 1.69/0.59    spl4_26 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.69/0.59  fof(f470,plain,(
% 1.69/0.59    spl4_39 <=> k1_xboole_0 = sK0),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.69/0.59  fof(f676,plain,(
% 1.69/0.59    spl4_63 <=> k1_xboole_0 = sK1),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 1.69/0.59  fof(f1194,plain,(
% 1.69/0.59    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | (~spl4_26 | ~spl4_39 | ~spl4_63)),
% 1.69/0.59    inference(forward_demodulation,[],[f1193,f472])).
% 1.69/0.59  fof(f472,plain,(
% 1.69/0.59    k1_xboole_0 = sK0 | ~spl4_39),
% 1.69/0.59    inference(avatar_component_clause,[],[f470])).
% 1.69/0.59  fof(f1193,plain,(
% 1.69/0.59    k2_funct_1(k1_xboole_0) = k2_funct_2(sK0,k1_xboole_0) | (~spl4_26 | ~spl4_63)),
% 1.69/0.59    inference(forward_demodulation,[],[f372,f678])).
% 1.69/0.59  fof(f678,plain,(
% 1.69/0.59    k1_xboole_0 = sK1 | ~spl4_63),
% 1.69/0.59    inference(avatar_component_clause,[],[f676])).
% 1.69/0.59  fof(f372,plain,(
% 1.69/0.59    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_26),
% 1.69/0.59    inference(avatar_component_clause,[],[f370])).
% 1.69/0.59  fof(f1114,plain,(
% 1.69/0.59    ~spl4_93 | spl4_91),
% 1.69/0.59    inference(avatar_split_clause,[],[f1109,f1091,f1111])).
% 1.69/0.59  fof(f1091,plain,(
% 1.69/0.59    spl4_91 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 1.69/0.59  fof(f1109,plain,(
% 1.69/0.59    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_91),
% 1.69/0.59    inference(forward_demodulation,[],[f1102,f94])).
% 1.69/0.59  fof(f1102,plain,(
% 1.69/0.59    ( ! [X0] : (~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl4_91),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f64,f1093,f65])).
% 1.69/0.59  fof(f65,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f22,plain,(
% 1.69/0.59    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f8])).
% 1.69/0.59  fof(f8,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.69/0.59  fof(f1093,plain,(
% 1.69/0.59    ~v1_xboole_0(k2_funct_1(k1_xboole_0)) | spl4_91),
% 1.69/0.59    inference(avatar_component_clause,[],[f1091])).
% 1.69/0.59  fof(f64,plain,(
% 1.69/0.59    v1_xboole_0(k1_xboole_0)),
% 1.69/0.59    inference(cnf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    v1_xboole_0(k1_xboole_0)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.69/0.59  fof(f1095,plain,(
% 1.69/0.59    ~spl4_91 | spl4_90),
% 1.69/0.59    inference(avatar_split_clause,[],[f1083,f1075,f1091])).
% 1.69/0.59  fof(f1075,plain,(
% 1.69/0.59    spl4_90 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.69/0.59  fof(f1083,plain,(
% 1.69/0.59    ~v1_xboole_0(k2_funct_1(k1_xboole_0)) | spl4_90),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f64,f1077,f81])).
% 1.69/0.59  fof(f81,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f30])).
% 1.69/0.59  fof(f30,plain,(
% 1.69/0.59    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f3])).
% 1.69/0.59  fof(f3,axiom,(
% 1.69/0.59    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.69/0.59  fof(f1077,plain,(
% 1.69/0.59    k1_xboole_0 != k2_funct_1(k1_xboole_0) | spl4_90),
% 1.69/0.59    inference(avatar_component_clause,[],[f1075])).
% 1.69/0.59  fof(f1078,plain,(
% 1.69/0.59    ~spl4_90 | ~spl4_63 | spl4_85),
% 1.69/0.59    inference(avatar_split_clause,[],[f1073,f1000,f676,f1075])).
% 1.69/0.59  fof(f1000,plain,(
% 1.69/0.59    spl4_85 <=> k1_xboole_0 = k2_funct_1(sK1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.69/0.59  fof(f1073,plain,(
% 1.69/0.59    k1_xboole_0 != k2_funct_1(k1_xboole_0) | (~spl4_63 | spl4_85)),
% 1.69/0.59    inference(forward_demodulation,[],[f1002,f678])).
% 1.69/0.59  fof(f1002,plain,(
% 1.69/0.59    k1_xboole_0 != k2_funct_1(sK1) | spl4_85),
% 1.69/0.59    inference(avatar_component_clause,[],[f1000])).
% 1.69/0.59  fof(f1016,plain,(
% 1.69/0.59    spl4_61 | ~spl4_52 | ~spl4_63),
% 1.69/0.59    inference(avatar_split_clause,[],[f1008,f676,f580,f646])).
% 1.69/0.59  fof(f580,plain,(
% 1.69/0.59    spl4_52 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.69/0.59  fof(f1008,plain,(
% 1.69/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_52 | ~spl4_63)),
% 1.69/0.59    inference(backward_demodulation,[],[f582,f678])).
% 1.69/0.59  fof(f582,plain,(
% 1.69/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl4_52),
% 1.69/0.59    inference(avatar_component_clause,[],[f580])).
% 1.69/0.59  fof(f1003,plain,(
% 1.69/0.59    ~spl4_85 | spl4_40 | ~spl4_60),
% 1.69/0.59    inference(avatar_split_clause,[],[f998,f638,f474,f1000])).
% 1.69/0.59  fof(f474,plain,(
% 1.69/0.59    spl4_40 <=> sK2 = k2_funct_1(sK1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.69/0.59  fof(f638,plain,(
% 1.69/0.59    spl4_60 <=> k1_xboole_0 = sK2),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.69/0.59  fof(f998,plain,(
% 1.69/0.59    k1_xboole_0 != k2_funct_1(sK1) | (spl4_40 | ~spl4_60)),
% 1.69/0.59    inference(forward_demodulation,[],[f475,f640])).
% 1.69/0.59  fof(f640,plain,(
% 1.69/0.59    k1_xboole_0 = sK2 | ~spl4_60),
% 1.69/0.59    inference(avatar_component_clause,[],[f638])).
% 1.69/0.59  fof(f475,plain,(
% 1.69/0.59    sK2 != k2_funct_1(sK1) | spl4_40),
% 1.69/0.59    inference(avatar_component_clause,[],[f474])).
% 1.69/0.59  fof(f862,plain,(
% 1.69/0.59    spl4_76 | ~spl4_51 | ~spl4_60),
% 1.69/0.59    inference(avatar_split_clause,[],[f823,f638,f574,f859])).
% 1.69/0.59  fof(f574,plain,(
% 1.69/0.59    spl4_51 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.69/0.59  fof(f823,plain,(
% 1.69/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_51 | ~spl4_60)),
% 1.69/0.59    inference(backward_demodulation,[],[f576,f640])).
% 1.69/0.59  fof(f576,plain,(
% 1.69/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl4_51),
% 1.69/0.59    inference(avatar_component_clause,[],[f574])).
% 1.69/0.59  fof(f857,plain,(
% 1.69/0.59    spl4_75 | ~spl4_50 | ~spl4_60),
% 1.69/0.59    inference(avatar_split_clause,[],[f822,f638,f569,f854])).
% 1.69/0.59  fof(f569,plain,(
% 1.69/0.59    spl4_50 <=> v3_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.69/0.59  fof(f822,plain,(
% 1.69/0.59    v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_50 | ~spl4_60)),
% 1.69/0.59    inference(backward_demodulation,[],[f571,f640])).
% 1.69/0.59  fof(f571,plain,(
% 1.69/0.59    v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl4_50),
% 1.69/0.59    inference(avatar_component_clause,[],[f569])).
% 1.69/0.59  fof(f831,plain,(
% 1.69/0.59    spl4_70 | ~spl4_6 | ~spl4_60),
% 1.69/0.59    inference(avatar_split_clause,[],[f815,f638,f124,f828])).
% 1.69/0.60  fof(f124,plain,(
% 1.69/0.60    spl4_6 <=> v1_funct_1(sK2)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.69/0.60  fof(f815,plain,(
% 1.69/0.60    v1_funct_1(k1_xboole_0) | (~spl4_6 | ~spl4_60)),
% 1.69/0.60    inference(backward_demodulation,[],[f126,f640])).
% 1.69/0.60  fof(f126,plain,(
% 1.69/0.60    v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.60    inference(avatar_component_clause,[],[f124])).
% 1.69/0.60  fof(f681,plain,(
% 1.69/0.60    spl4_63 | ~spl4_37),
% 1.69/0.60    inference(avatar_split_clause,[],[f661,f425,f676])).
% 1.69/0.60  fof(f425,plain,(
% 1.69/0.60    spl4_37 <=> v1_xboole_0(sK1)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.69/0.60  fof(f661,plain,(
% 1.69/0.60    k1_xboole_0 = sK1 | ~spl4_37),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f64,f427,f81])).
% 1.69/0.60  fof(f427,plain,(
% 1.69/0.60    v1_xboole_0(sK1) | ~spl4_37),
% 1.69/0.60    inference(avatar_component_clause,[],[f425])).
% 1.69/0.60  fof(f642,plain,(
% 1.69/0.60    spl4_60 | ~spl4_24),
% 1.69/0.60    inference(avatar_split_clause,[],[f630,f308,f638])).
% 1.69/0.60  fof(f308,plain,(
% 1.69/0.60    spl4_24 <=> v1_xboole_0(sK2)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.69/0.60  fof(f630,plain,(
% 1.69/0.60    k1_xboole_0 = sK2 | ~spl4_24),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f64,f310,f81])).
% 1.69/0.60  fof(f310,plain,(
% 1.69/0.60    v1_xboole_0(sK2) | ~spl4_24),
% 1.69/0.60    inference(avatar_component_clause,[],[f308])).
% 1.69/0.60  fof(f606,plain,(
% 1.69/0.60    k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | sK2 != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.69/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.60  fof(f605,plain,(
% 1.69/0.60    spl4_23 | ~spl4_39),
% 1.69/0.60    inference(avatar_contradiction_clause,[],[f604])).
% 1.69/0.60  fof(f604,plain,(
% 1.69/0.60    $false | (spl4_23 | ~spl4_39)),
% 1.69/0.60    inference(subsumption_resolution,[],[f549,f64])).
% 1.69/0.60  fof(f549,plain,(
% 1.69/0.60    ~v1_xboole_0(k1_xboole_0) | (spl4_23 | ~spl4_39)),
% 1.69/0.60    inference(backward_demodulation,[],[f306,f472])).
% 1.69/0.60  fof(f306,plain,(
% 1.69/0.60    ~v1_xboole_0(sK0) | spl4_23),
% 1.69/0.60    inference(avatar_component_clause,[],[f304])).
% 1.69/0.60  fof(f304,plain,(
% 1.69/0.60    spl4_23 <=> v1_xboole_0(sK0)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.69/0.60  fof(f583,plain,(
% 1.69/0.60    spl4_52 | ~spl4_7 | ~spl4_39),
% 1.69/0.60    inference(avatar_split_clause,[],[f578,f470,f129,f580])).
% 1.69/0.60  fof(f129,plain,(
% 1.69/0.60    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.69/0.60  fof(f578,plain,(
% 1.69/0.60    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl4_7 | ~spl4_39)),
% 1.69/0.60    inference(forward_demodulation,[],[f544,f94])).
% 1.69/0.60  fof(f544,plain,(
% 1.69/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_7 | ~spl4_39)),
% 1.69/0.60    inference(backward_demodulation,[],[f131,f472])).
% 1.69/0.60  fof(f131,plain,(
% 1.69/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_7),
% 1.69/0.60    inference(avatar_component_clause,[],[f129])).
% 1.69/0.60  fof(f577,plain,(
% 1.69/0.60    spl4_51 | ~spl4_5 | ~spl4_39),
% 1.69/0.60    inference(avatar_split_clause,[],[f543,f470,f119,f574])).
% 1.69/0.60  fof(f119,plain,(
% 1.69/0.60    spl4_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.69/0.60  fof(f543,plain,(
% 1.69/0.60    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl4_5 | ~spl4_39)),
% 1.69/0.60    inference(backward_demodulation,[],[f121,f472])).
% 1.69/0.60  fof(f121,plain,(
% 1.69/0.60    v1_funct_2(sK2,sK0,sK0) | ~spl4_5),
% 1.69/0.60    inference(avatar_component_clause,[],[f119])).
% 1.91/0.60  fof(f572,plain,(
% 1.91/0.60    spl4_50 | ~spl4_4 | ~spl4_39),
% 1.91/0.60    inference(avatar_split_clause,[],[f542,f470,f114,f569])).
% 1.91/0.60  fof(f114,plain,(
% 1.91/0.60    spl4_4 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.91/0.60  fof(f542,plain,(
% 1.91/0.60    v3_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_39)),
% 1.91/0.60    inference(backward_demodulation,[],[f116,f472])).
% 1.91/0.60  fof(f116,plain,(
% 1.91/0.60    v3_funct_2(sK2,sK0,sK0) | ~spl4_4),
% 1.91/0.60    inference(avatar_component_clause,[],[f114])).
% 1.91/0.60  fof(f538,plain,(
% 1.91/0.60    spl4_46 | ~spl4_32 | ~spl4_34 | ~spl4_36),
% 1.91/0.60    inference(avatar_split_clause,[],[f536,f420,f410,f400,f531])).
% 1.91/0.60  fof(f531,plain,(
% 1.91/0.60    spl4_46 <=> sK0 = k2_relat_1(sK1)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.91/0.60  fof(f400,plain,(
% 1.91/0.60    spl4_32 <=> v2_funct_2(sK1,sK0)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.91/0.60  fof(f410,plain,(
% 1.91/0.60    spl4_34 <=> v5_relat_1(sK1,sK0)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.91/0.60  fof(f420,plain,(
% 1.91/0.60    spl4_36 <=> v1_relat_1(sK1)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.91/0.60  fof(f536,plain,(
% 1.91/0.60    sK0 = k2_relat_1(sK1) | (~spl4_32 | ~spl4_34 | ~spl4_36)),
% 1.91/0.60    inference(unit_resulting_resolution,[],[f422,f402,f412,f66])).
% 1.91/0.60  fof(f66,plain,(
% 1.91/0.60    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f45])).
% 1.91/0.60  fof(f45,plain,(
% 1.91/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.91/0.60    inference(nnf_transformation,[],[f24])).
% 1.91/0.60  fof(f24,plain,(
% 1.91/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.91/0.60    inference(flattening,[],[f23])).
% 1.91/0.60  fof(f23,plain,(
% 1.91/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.91/0.60    inference(ennf_transformation,[],[f12])).
% 1.91/0.60  fof(f12,axiom,(
% 1.91/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.91/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.91/0.60  fof(f412,plain,(
% 1.91/0.60    v5_relat_1(sK1,sK0) | ~spl4_34),
% 1.91/0.60    inference(avatar_component_clause,[],[f410])).
% 1.91/0.60  fof(f402,plain,(
% 1.91/0.60    v2_funct_2(sK1,sK0) | ~spl4_32),
% 1.91/0.60    inference(avatar_component_clause,[],[f400])).
% 1.91/0.60  fof(f422,plain,(
% 1.91/0.60    v1_relat_1(sK1) | ~spl4_36),
% 1.91/0.60    inference(avatar_component_clause,[],[f420])).
% 1.91/0.60  fof(f535,plain,(
% 1.91/0.60    k2_relset_1(sK0,sK0,sK1) != k2_relat_1(sK1) | sK0 != k2_relat_1(sK1) | sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.91/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.91/0.60  fof(f477,plain,(
% 1.91/0.60    ~spl4_38 | ~spl4_33 | spl4_39 | spl4_40 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_10),
% 1.91/0.60    inference(avatar_split_clause,[],[f464,f144,f139,f129,f124,f119,f109,f104,f474,f470,f405,f466])).
% 1.91/0.60  fof(f466,plain,(
% 1.91/0.60    spl4_38 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.91/0.60  fof(f405,plain,(
% 1.91/0.60    spl4_33 <=> v2_funct_1(sK1)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.91/0.60  fof(f104,plain,(
% 1.91/0.60    spl4_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.91/0.60  fof(f109,plain,(
% 1.91/0.60    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.91/0.60  fof(f139,plain,(
% 1.91/0.60    spl4_9 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.91/0.60  fof(f144,plain,(
% 1.91/0.60    spl4_10 <=> v1_funct_1(sK1)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.91/0.60  fof(f464,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_10)),
% 1.91/0.60    inference(subsumption_resolution,[],[f463,f146])).
% 1.91/0.60  fof(f146,plain,(
% 1.91/0.60    v1_funct_1(sK1) | ~spl4_10),
% 1.91/0.60    inference(avatar_component_clause,[],[f144])).
% 1.91/0.60  fof(f463,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9)),
% 1.91/0.60    inference(subsumption_resolution,[],[f462,f141])).
% 1.91/0.60  fof(f141,plain,(
% 1.91/0.60    v1_funct_2(sK1,sK0,sK0) | ~spl4_9),
% 1.91/0.60    inference(avatar_component_clause,[],[f139])).
% 1.91/0.60  fof(f462,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.91/0.60    inference(subsumption_resolution,[],[f461,f131])).
% 1.91/0.60  fof(f461,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6)),
% 1.91/0.60    inference(subsumption_resolution,[],[f460,f126])).
% 1.91/0.60  fof(f460,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.91/0.60    inference(subsumption_resolution,[],[f459,f121])).
% 1.91/0.60  fof(f459,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl4_2 | ~spl4_3)),
% 1.91/0.60    inference(subsumption_resolution,[],[f456,f111])).
% 1.91/0.60  fof(f111,plain,(
% 1.91/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_3),
% 1.91/0.60    inference(avatar_component_clause,[],[f109])).
% 1.91/0.60  fof(f456,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl4_2),
% 1.91/0.60    inference(duplicate_literal_removal,[],[f452])).
% 1.91/0.60  fof(f452,plain,(
% 1.91/0.60    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl4_2),
% 1.91/0.60    inference(resolution,[],[f106,f90])).
% 1.91/0.60  fof(f90,plain,(
% 1.91/0.60    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f39])).
% 1.91/0.60  fof(f39,plain,(
% 1.91/0.60    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.60    inference(flattening,[],[f38])).
% 1.91/0.60  fof(f38,plain,(
% 1.91/0.60    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.60    inference(ennf_transformation,[],[f16])).
% 1.91/0.60  fof(f16,axiom,(
% 1.91/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.91/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.91/0.60  fof(f106,plain,(
% 1.91/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl4_2),
% 1.91/0.60    inference(avatar_component_clause,[],[f104])).
% 1.91/0.60  fof(f446,plain,(
% 1.91/0.60    spl4_26 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10),
% 1.91/0.60    inference(avatar_split_clause,[],[f445,f144,f139,f134,f129,f370])).
% 1.91/0.60  fof(f134,plain,(
% 1.91/0.60    spl4_8 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.91/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.91/0.60  fof(f445,plain,(
% 1.91/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 1.91/0.60    inference(subsumption_resolution,[],[f444,f146])).
% 1.91/0.60  fof(f444,plain,(
% 1.91/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl4_7 | ~spl4_8 | ~spl4_9)),
% 1.91/0.60    inference(subsumption_resolution,[],[f443,f141])).
% 1.91/0.60  fof(f443,plain,(
% 1.91/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl4_7 | ~spl4_8)),
% 1.91/0.60    inference(subsumption_resolution,[],[f362,f136])).
% 1.91/0.60  fof(f136,plain,(
% 1.91/0.60    v3_funct_2(sK1,sK0,sK0) | ~spl4_8),
% 1.91/0.60    inference(avatar_component_clause,[],[f134])).
% 1.91/0.60  fof(f362,plain,(
% 1.91/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl4_7),
% 1.91/0.60    inference(resolution,[],[f131,f68])).
% 1.91/0.60  fof(f68,plain,(
% 1.91/0.60    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f26])).
% 1.91/0.61  fof(f26,plain,(
% 1.91/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.91/0.61    inference(flattening,[],[f25])).
% 1.91/0.61  fof(f25,plain,(
% 1.91/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.91/0.61    inference(ennf_transformation,[],[f14])).
% 1.91/0.61  fof(f14,axiom,(
% 1.91/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.91/0.61  fof(f437,plain,(
% 1.91/0.61    spl4_32 | ~spl4_7 | ~spl4_8 | ~spl4_10),
% 1.91/0.61    inference(avatar_split_clause,[],[f436,f144,f134,f129,f400])).
% 1.91/0.61  fof(f436,plain,(
% 1.91/0.61    v2_funct_2(sK1,sK0) | (~spl4_7 | ~spl4_8 | ~spl4_10)),
% 1.91/0.61    inference(subsumption_resolution,[],[f435,f146])).
% 1.91/0.61  fof(f435,plain,(
% 1.91/0.61    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | (~spl4_7 | ~spl4_8)),
% 1.91/0.61    inference(subsumption_resolution,[],[f348,f136])).
% 1.91/0.61  fof(f348,plain,(
% 1.91/0.61    v2_funct_2(sK1,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f87])).
% 1.91/0.61  fof(f87,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f35])).
% 1.91/0.61  fof(f35,plain,(
% 1.91/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(flattening,[],[f34])).
% 1.91/0.61  fof(f34,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(ennf_transformation,[],[f11])).
% 1.91/0.61  fof(f11,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.91/0.61  fof(f434,plain,(
% 1.91/0.61    spl4_33 | ~spl4_7 | ~spl4_8 | ~spl4_10),
% 1.91/0.61    inference(avatar_split_clause,[],[f433,f144,f134,f129,f405])).
% 1.91/0.61  fof(f433,plain,(
% 1.91/0.61    v2_funct_1(sK1) | (~spl4_7 | ~spl4_8 | ~spl4_10)),
% 1.91/0.61    inference(subsumption_resolution,[],[f432,f146])).
% 1.91/0.61  fof(f432,plain,(
% 1.91/0.61    v2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl4_7 | ~spl4_8)),
% 1.91/0.61    inference(subsumption_resolution,[],[f347,f136])).
% 1.91/0.61  fof(f347,plain,(
% 1.91/0.61    v2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f86])).
% 1.91/0.61  fof(f86,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f35])).
% 1.91/0.61  fof(f431,plain,(
% 1.91/0.61    spl4_34 | ~spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f346,f129,f410])).
% 1.91/0.61  fof(f346,plain,(
% 1.91/0.61    v5_relat_1(sK1,sK0) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f84])).
% 1.91/0.61  fof(f84,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f33])).
% 1.91/0.61  fof(f33,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(ennf_transformation,[],[f19])).
% 1.91/0.61  fof(f19,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.91/0.61    inference(pure_predicate_removal,[],[f7])).
% 1.91/0.61  fof(f7,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.91/0.61  fof(f430,plain,(
% 1.91/0.61    spl4_35 | ~spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f345,f129,f415])).
% 1.91/0.61  fof(f415,plain,(
% 1.91/0.61    spl4_35 <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.91/0.61  fof(f345,plain,(
% 1.91/0.61    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f83])).
% 1.91/0.61  fof(f83,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f32])).
% 1.91/0.61  fof(f32,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(ennf_transformation,[],[f9])).
% 1.91/0.61  fof(f9,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.91/0.61  fof(f429,plain,(
% 1.91/0.61    spl4_36 | ~spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f344,f129,f420])).
% 1.91/0.61  fof(f344,plain,(
% 1.91/0.61    v1_relat_1(sK1) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f82])).
% 1.91/0.61  fof(f82,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f31])).
% 1.91/0.61  fof(f31,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(ennf_transformation,[],[f6])).
% 1.91/0.61  fof(f6,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.91/0.61  fof(f428,plain,(
% 1.91/0.61    ~spl4_23 | spl4_37 | ~spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f343,f129,f425,f304])).
% 1.91/0.61  fof(f343,plain,(
% 1.91/0.61    v1_xboole_0(sK1) | ~v1_xboole_0(sK0) | ~spl4_7),
% 1.91/0.61    inference(resolution,[],[f131,f65])).
% 1.91/0.61  fof(f321,plain,(
% 1.91/0.61    spl4_17 | ~spl4_3),
% 1.91/0.61    inference(avatar_split_clause,[],[f236,f109,f274])).
% 1.91/0.61  fof(f274,plain,(
% 1.91/0.61    spl4_17 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.91/0.61  fof(f236,plain,(
% 1.91/0.61    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl4_3),
% 1.91/0.61    inference(resolution,[],[f111,f97])).
% 1.91/0.61  fof(f97,plain,(
% 1.91/0.61    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(duplicate_literal_removal,[],[f96])).
% 1.91/0.61  fof(f96,plain,(
% 1.91/0.61    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(equality_resolution,[],[f92])).
% 1.91/0.61  fof(f92,plain,(
% 1.91/0.61    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.61    inference(cnf_transformation,[],[f53])).
% 1.91/0.61  fof(f53,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(nnf_transformation,[],[f41])).
% 1.91/0.61  fof(f41,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(flattening,[],[f40])).
% 1.91/0.61  fof(f40,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.91/0.61    inference(ennf_transformation,[],[f10])).
% 1.91/0.61  fof(f10,axiom,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.91/0.61  fof(f311,plain,(
% 1.91/0.61    ~spl4_23 | spl4_24 | ~spl4_3),
% 1.91/0.61    inference(avatar_split_clause,[],[f222,f109,f308,f304])).
% 1.91/0.61  fof(f222,plain,(
% 1.91/0.61    v1_xboole_0(sK2) | ~v1_xboole_0(sK0) | ~spl4_3),
% 1.91/0.61    inference(resolution,[],[f111,f65])).
% 1.91/0.61  fof(f147,plain,(
% 1.91/0.61    spl4_10),
% 1.91/0.61    inference(avatar_split_clause,[],[f54,f144])).
% 1.91/0.61  fof(f54,plain,(
% 1.91/0.61    v1_funct_1(sK1)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f44,plain,(
% 1.91/0.61    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.91/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f43,f42])).
% 1.91/0.61  fof(f42,plain,(
% 1.91/0.61    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f43,plain,(
% 1.91/0.61    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.91/0.61    introduced(choice_axiom,[])).
% 1.91/0.61  fof(f21,plain,(
% 1.91/0.61    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.91/0.61    inference(flattening,[],[f20])).
% 1.91/0.61  fof(f20,plain,(
% 1.91/0.61    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.91/0.61    inference(ennf_transformation,[],[f18])).
% 1.91/0.61  fof(f18,negated_conjecture,(
% 1.91/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.91/0.61    inference(negated_conjecture,[],[f17])).
% 1.91/0.61  fof(f17,conjecture,(
% 1.91/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.91/0.61  fof(f142,plain,(
% 1.91/0.61    spl4_9),
% 1.91/0.61    inference(avatar_split_clause,[],[f55,f139])).
% 1.91/0.61  fof(f55,plain,(
% 1.91/0.61    v1_funct_2(sK1,sK0,sK0)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f137,plain,(
% 1.91/0.61    spl4_8),
% 1.91/0.61    inference(avatar_split_clause,[],[f56,f134])).
% 1.91/0.61  fof(f56,plain,(
% 1.91/0.61    v3_funct_2(sK1,sK0,sK0)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f132,plain,(
% 1.91/0.61    spl4_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f57,f129])).
% 1.91/0.61  fof(f57,plain,(
% 1.91/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f127,plain,(
% 1.91/0.61    spl4_6),
% 1.91/0.61    inference(avatar_split_clause,[],[f58,f124])).
% 1.91/0.61  fof(f58,plain,(
% 1.91/0.61    v1_funct_1(sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f122,plain,(
% 1.91/0.61    spl4_5),
% 1.91/0.61    inference(avatar_split_clause,[],[f59,f119])).
% 1.91/0.61  fof(f59,plain,(
% 1.91/0.61    v1_funct_2(sK2,sK0,sK0)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f117,plain,(
% 1.91/0.61    spl4_4),
% 1.91/0.61    inference(avatar_split_clause,[],[f60,f114])).
% 1.91/0.61  fof(f60,plain,(
% 1.91/0.61    v3_funct_2(sK2,sK0,sK0)),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f112,plain,(
% 1.91/0.61    spl4_3),
% 1.91/0.61    inference(avatar_split_clause,[],[f61,f109])).
% 1.91/0.61  fof(f61,plain,(
% 1.91/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f107,plain,(
% 1.91/0.61    spl4_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f62,f104])).
% 1.91/0.61  fof(f62,plain,(
% 1.91/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  fof(f102,plain,(
% 1.91/0.61    ~spl4_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f63,f99])).
% 1.91/0.61  fof(f99,plain,(
% 1.91/0.61    spl4_1 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.91/0.61  fof(f63,plain,(
% 1.91/0.61    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.91/0.61    inference(cnf_transformation,[],[f44])).
% 1.91/0.61  % SZS output end Proof for theBenchmark
% 1.91/0.61  % (9651)------------------------------
% 1.91/0.61  % (9651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (9651)Termination reason: Refutation
% 1.91/0.61  
% 1.91/0.61  % (9651)Memory used [KB]: 6908
% 1.91/0.61  % (9651)Time elapsed: 0.156 s
% 1.91/0.61  % (9651)------------------------------
% 1.91/0.61  % (9651)------------------------------
% 1.91/0.61  % (9625)Success in time 0.247 s
%------------------------------------------------------------------------------
