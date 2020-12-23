%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:35 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 463 expanded)
%              Number of leaves         :   49 ( 194 expanded)
%              Depth                    :   11
%              Number of atoms          :  603 (1389 expanded)
%              Number of equality atoms :   76 ( 186 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1536,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f127,f132,f272,f373,f376,f585,f740,f741,f894,f966,f970,f976,f1005,f1007,f1014,f1036,f1041,f1075,f1436,f1444,f1448,f1471,f1500,f1505,f1514,f1535])).

fof(f1535,plain,
    ( ~ spl5_95
    | ~ spl5_157
    | spl5_154
    | ~ spl5_31
    | ~ spl5_118
    | ~ spl5_151 ),
    inference(avatar_split_clause,[],[f1534,f1441,f1113,f357,f1468,f1497,f891])).

fof(f891,plain,
    ( spl5_95
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f1497,plain,
    ( spl5_157
  <=> v1_funct_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f1468,plain,
    ( spl5_154
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f357,plain,
    ( spl5_31
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1113,plain,
    ( spl5_118
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1441,plain,
    ( spl5_151
  <=> k1_xboole_0 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f1534,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_31
    | ~ spl5_118
    | ~ spl5_151 ),
    inference(forward_demodulation,[],[f1533,f1443])).

fof(f1443,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_151 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1533,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,k9_relat_1(sK4,sK1))
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_31
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f1528,f377])).

fof(f377,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))
    | ~ spl5_31 ),
    inference(resolution,[],[f358,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f358,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f1528,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,k2_relat_1(k7_relat_1(sK4,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_118 ),
    inference(superposition,[],[f52,f1114])).

fof(f1114,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1514,plain,
    ( spl5_100
    | ~ spl5_102
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1511,f1033,f934,f923])).

fof(f923,plain,
    ( spl5_100
  <=> v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f934,plain,
    ( spl5_102
  <=> v5_relat_1(k7_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1033,plain,
    ( spl5_110
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1511,plain,
    ( v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_102
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f935,f1035])).

fof(f1035,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f935,plain,
    ( v5_relat_1(k7_relat_1(sK4,sK1),sK2)
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f934])).

fof(f1505,plain,
    ( ~ spl5_113
    | spl5_157 ),
    inference(avatar_contradiction_clause,[],[f1502])).

fof(f1502,plain,
    ( $false
    | ~ spl5_113
    | spl5_157 ),
    inference(unit_resulting_resolution,[],[f1074,f1499])).

fof(f1499,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_157 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1074,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1073,plain,
    ( spl5_113
  <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f1500,plain,
    ( ~ spl5_157
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1495,f124,f111,f101,f1497])).

fof(f101,plain,
    ( spl5_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f111,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f124,plain,
    ( spl5_9
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1495,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(forward_demodulation,[],[f126,f857])).

fof(f857,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f557,f103])).

fof(f103,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f557,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2) )
    | ~ spl5_6 ),
    inference(resolution,[],[f75,f113])).

fof(f113,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f126,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1471,plain,
    ( ~ spl5_154
    | spl5_108
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1453,f1033,f1011,f1468])).

fof(f1011,plain,
    ( spl5_108
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1453,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_108
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f1013,f1035])).

fof(f1013,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_108 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1448,plain,
    ( spl5_109
    | ~ spl5_111
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f1445,f1113,f1038,f1029])).

fof(f1029,plain,
    ( spl5_109
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1038,plain,
    ( spl5_111
  <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f1445,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_111
    | ~ spl5_118 ),
    inference(backward_demodulation,[],[f1040,f1114])).

fof(f1040,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1444,plain,
    ( ~ spl5_100
    | spl5_151
    | ~ spl5_31
    | ~ spl5_95 ),
    inference(avatar_split_clause,[],[f1439,f891,f357,f1441,f923])).

fof(f1439,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_31
    | ~ spl5_95 ),
    inference(forward_demodulation,[],[f980,f377])).

fof(f980,plain,
    ( k1_xboole_0 = k2_relat_1(k7_relat_1(sK4,sK1))
    | ~ v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_95 ),
    inference(resolution,[],[f893,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f147,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f147,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f893,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f891])).

fof(f1436,plain,
    ( spl5_118
    | ~ spl5_3
    | ~ spl5_31
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1434,f737,f357,f96,f1113])).

fof(f96,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f737,plain,
    ( spl5_76
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1434,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_3
    | ~ spl5_31
    | ~ spl5_76 ),
    inference(resolution,[],[f744,f98])).

fof(f98,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f744,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_31
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f378,f739])).

fof(f739,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f737])).

fof(f378,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK4))
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_31 ),
    inference(resolution,[],[f358,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1075,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_113
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1067,f111,f101,f1073,f101,f111])).

fof(f1067,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(sK4,X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f76,f857])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1041,plain,
    ( spl5_111
    | ~ spl5_93 ),
    inference(avatar_split_clause,[],[f1026,f881,f1038])).

fof(f881,plain,
    ( spl5_93
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1026,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_93 ),
    inference(resolution,[],[f882,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f882,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1036,plain,
    ( spl5_108
    | ~ spl5_109
    | spl5_110
    | ~ spl5_93 ),
    inference(avatar_split_clause,[],[f1023,f881,f1033,f1029,f1011])).

fof(f1023,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_93 ),
    inference(resolution,[],[f882,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f1014,plain,
    ( ~ spl5_108
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f1009,f120,f111,f101,f1011])).

fof(f120,plain,
    ( spl5_8
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1009,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(forward_demodulation,[],[f122,f857])).

fof(f122,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1007,plain,
    ( ~ spl5_95
    | ~ spl5_107
    | ~ spl5_33
    | ~ spl5_31
    | spl5_93 ),
    inference(avatar_split_clause,[],[f1006,f881,f357,f370,f963,f891])).

fof(f963,plain,
    ( spl5_107
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f370,plain,
    ( spl5_33
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1006,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_31
    | spl5_93 ),
    inference(forward_demodulation,[],[f1000,f377])).

fof(f1000,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_93 ),
    inference(resolution,[],[f883,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f883,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_93 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1005,plain,
    ( ~ spl5_31
    | spl5_107 ),
    inference(avatar_split_clause,[],[f1003,f963,f357])).

fof(f1003,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_107 ),
    inference(resolution,[],[f965,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f965,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_107 ),
    inference(avatar_component_clause,[],[f963])).

fof(f976,plain,
    ( spl5_102
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f975,f629,f111,f101,f934])).

fof(f629,plain,
    ( spl5_63
  <=> v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f975,plain,
    ( v5_relat_1(k7_relat_1(sK4,sK1),sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f630,f857])).

fof(f630,plain,
    ( v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f629])).

fof(f970,plain,
    ( ~ spl5_33
    | ~ spl5_95
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_31
    | spl5_63 ),
    inference(avatar_split_clause,[],[f969,f629,f357,f111,f101,f891,f370])).

fof(f969,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_31
    | spl5_63 ),
    inference(forward_demodulation,[],[f968,f857])).

fof(f968,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_31
    | spl5_63 ),
    inference(forward_demodulation,[],[f967,f377])).

fof(f967,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_63 ),
    inference(forward_demodulation,[],[f633,f857])).

fof(f633,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_63 ),
    inference(resolution,[],[f631,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f631,plain,
    ( ~ v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2)
    | spl5_63 ),
    inference(avatar_component_clause,[],[f629])).

fof(f966,plain,
    ( ~ spl5_107
    | ~ spl5_33
    | ~ spl5_95
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f961,f357,f116,f111,f101,f891,f370,f963])).

fof(f116,plain,
    ( spl5_7
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f961,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f960,f857])).

fof(f960,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f959,f377])).

fof(f959,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f958,f857])).

fof(f958,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f635,f857])).

fof(f635,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_7 ),
    inference(resolution,[],[f118,f66])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f894,plain,
    ( spl5_95
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f863,f414,f111,f101,f891])).

fof(f414,plain,
    ( spl5_37
  <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f863,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(backward_demodulation,[],[f415,f857])).

fof(f415,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f414])).

fof(f741,plain,
    ( k1_xboole_0 != sK3
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f740,plain,
    ( ~ spl5_5
    | spl5_75
    | spl5_76
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f731,f269,f101,f737,f733,f106])).

fof(f106,plain,
    ( spl5_5
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f733,plain,
    ( spl5_75
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f269,plain,
    ( spl5_24
  <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f731,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f726,f271])).

fof(f271,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f269])).

fof(f726,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f73,f103])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f585,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_37 ),
    inference(avatar_split_clause,[],[f576,f414,f101,f111])).

fof(f576,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_37 ),
    inference(resolution,[],[f77,f429])).

fof(f429,plain,
    ( ! [X2,X3] : ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | spl5_37 ),
    inference(resolution,[],[f426,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f426,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0)) )
    | spl5_37 ),
    inference(resolution,[],[f416,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f416,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f414])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f376,plain,
    ( ~ spl5_4
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl5_4
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f54,f103,f359,f51])).

fof(f359,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f373,plain,
    ( spl5_33
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f368,f101,f91,f370])).

fof(f91,plain,
    ( spl5_2
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f368,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f93,f365])).

fof(f365,plain,
    ( ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f74,f103])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f272,plain,
    ( spl5_24
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f265,f101,f269])).

fof(f265,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f103])).

fof(f132,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f49,f129])).

fof(f129,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f127,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f42,f124,f120,f116])).

fof(f42,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f43,f111])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f44,f106])).

fof(f44,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f46,f96])).

fof(f46,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f47,f91])).

fof(f47,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f86,plain,
    ( spl5_1
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (11785)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (11775)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (11774)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (11776)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (11797)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (11779)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (11792)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (11796)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (11780)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (11788)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (11777)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (11781)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (11782)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (11790)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (11793)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (11791)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (11786)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (11789)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (11798)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (11800)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (11795)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (11794)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (11778)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (11783)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (11787)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (11799)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.74/0.58  % (11790)Refutation found. Thanks to Tanya!
% 1.74/0.58  % SZS status Theorem for theBenchmark
% 1.74/0.58  % SZS output start Proof for theBenchmark
% 1.74/0.58  fof(f1536,plain,(
% 1.74/0.58    $false),
% 1.74/0.58    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f127,f132,f272,f373,f376,f585,f740,f741,f894,f966,f970,f976,f1005,f1007,f1014,f1036,f1041,f1075,f1436,f1444,f1448,f1471,f1500,f1505,f1514,f1535])).
% 1.74/0.58  fof(f1535,plain,(
% 1.74/0.58    ~spl5_95 | ~spl5_157 | spl5_154 | ~spl5_31 | ~spl5_118 | ~spl5_151),
% 1.74/0.58    inference(avatar_split_clause,[],[f1534,f1441,f1113,f357,f1468,f1497,f891])).
% 1.74/0.58  fof(f891,plain,(
% 1.74/0.58    spl5_95 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 1.74/0.58  fof(f1497,plain,(
% 1.74/0.58    spl5_157 <=> v1_funct_1(k7_relat_1(sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).
% 1.74/0.58  fof(f1468,plain,(
% 1.74/0.58    spl5_154 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).
% 1.74/0.58  fof(f357,plain,(
% 1.74/0.58    spl5_31 <=> v1_relat_1(sK4)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.74/0.58  fof(f1113,plain,(
% 1.74/0.58    spl5_118 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 1.74/0.58  fof(f1441,plain,(
% 1.74/0.58    spl5_151 <=> k1_xboole_0 = k9_relat_1(sK4,sK1)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).
% 1.74/0.58  fof(f1534,plain,(
% 1.74/0.58    v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_31 | ~spl5_118 | ~spl5_151)),
% 1.74/0.58    inference(forward_demodulation,[],[f1533,f1443])).
% 1.74/0.58  fof(f1443,plain,(
% 1.74/0.58    k1_xboole_0 = k9_relat_1(sK4,sK1) | ~spl5_151),
% 1.74/0.58    inference(avatar_component_clause,[],[f1441])).
% 1.74/0.58  fof(f1533,plain,(
% 1.74/0.58    v1_funct_2(k7_relat_1(sK4,sK1),sK1,k9_relat_1(sK4,sK1)) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_31 | ~spl5_118)),
% 1.74/0.58    inference(forward_demodulation,[],[f1528,f377])).
% 1.74/0.58  fof(f377,plain,(
% 1.74/0.58    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) ) | ~spl5_31),
% 1.74/0.58    inference(resolution,[],[f358,f57])).
% 1.74/0.58  fof(f57,plain,(
% 1.74/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f28])).
% 1.74/0.58  fof(f28,plain,(
% 1.74/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.74/0.58    inference(ennf_transformation,[],[f8])).
% 1.74/0.58  fof(f8,axiom,(
% 1.74/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.74/0.58  fof(f358,plain,(
% 1.74/0.58    v1_relat_1(sK4) | ~spl5_31),
% 1.74/0.58    inference(avatar_component_clause,[],[f357])).
% 1.74/0.58  fof(f1528,plain,(
% 1.74/0.58    v1_funct_2(k7_relat_1(sK4,sK1),sK1,k2_relat_1(k7_relat_1(sK4,sK1))) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_118),
% 1.74/0.58    inference(superposition,[],[f52,f1114])).
% 1.74/0.58  fof(f1114,plain,(
% 1.74/0.58    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_118),
% 1.74/0.58    inference(avatar_component_clause,[],[f1113])).
% 1.74/0.58  fof(f52,plain,(
% 1.74/0.58    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f25])).
% 1.74/0.58  fof(f25,plain,(
% 1.74/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.58    inference(flattening,[],[f24])).
% 1.74/0.58  fof(f24,plain,(
% 1.74/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.58    inference(ennf_transformation,[],[f18])).
% 1.74/0.58  fof(f18,axiom,(
% 1.74/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.74/0.58  fof(f1514,plain,(
% 1.74/0.58    spl5_100 | ~spl5_102 | ~spl5_110),
% 1.74/0.58    inference(avatar_split_clause,[],[f1511,f1033,f934,f923])).
% 1.74/0.58  fof(f923,plain,(
% 1.74/0.58    spl5_100 <=> v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 1.74/0.58  fof(f934,plain,(
% 1.74/0.58    spl5_102 <=> v5_relat_1(k7_relat_1(sK4,sK1),sK2)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 1.74/0.58  fof(f1033,plain,(
% 1.74/0.58    spl5_110 <=> k1_xboole_0 = sK2),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 1.74/0.58  fof(f1511,plain,(
% 1.74/0.58    v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_102 | ~spl5_110)),
% 1.74/0.58    inference(backward_demodulation,[],[f935,f1035])).
% 1.74/0.58  fof(f1035,plain,(
% 1.74/0.58    k1_xboole_0 = sK2 | ~spl5_110),
% 1.74/0.58    inference(avatar_component_clause,[],[f1033])).
% 1.74/0.58  fof(f935,plain,(
% 1.74/0.58    v5_relat_1(k7_relat_1(sK4,sK1),sK2) | ~spl5_102),
% 1.74/0.58    inference(avatar_component_clause,[],[f934])).
% 1.74/0.58  fof(f1505,plain,(
% 1.74/0.58    ~spl5_113 | spl5_157),
% 1.74/0.58    inference(avatar_contradiction_clause,[],[f1502])).
% 1.74/0.58  fof(f1502,plain,(
% 1.74/0.58    $false | (~spl5_113 | spl5_157)),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f1074,f1499])).
% 1.74/0.58  fof(f1499,plain,(
% 1.74/0.58    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_157),
% 1.74/0.58    inference(avatar_component_clause,[],[f1497])).
% 1.74/0.58  fof(f1074,plain,(
% 1.74/0.58    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1))) ) | ~spl5_113),
% 1.74/0.58    inference(avatar_component_clause,[],[f1073])).
% 1.74/0.58  fof(f1073,plain,(
% 1.74/0.58    spl5_113 <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 1.74/0.58  fof(f1500,plain,(
% 1.74/0.58    ~spl5_157 | ~spl5_4 | ~spl5_6 | spl5_9),
% 1.74/0.58    inference(avatar_split_clause,[],[f1495,f124,f111,f101,f1497])).
% 1.74/0.58  fof(f101,plain,(
% 1.74/0.58    spl5_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.74/0.58  fof(f111,plain,(
% 1.74/0.58    spl5_6 <=> v1_funct_1(sK4)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.74/0.58  fof(f124,plain,(
% 1.74/0.58    spl5_9 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.74/0.58  fof(f1495,plain,(
% 1.74/0.58    ~v1_funct_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_9)),
% 1.74/0.58    inference(forward_demodulation,[],[f126,f857])).
% 1.74/0.58  fof(f857,plain,(
% 1.74/0.58    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl5_4 | ~spl5_6)),
% 1.74/0.58    inference(resolution,[],[f557,f103])).
% 1.74/0.58  fof(f103,plain,(
% 1.74/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_4),
% 1.74/0.58    inference(avatar_component_clause,[],[f101])).
% 1.74/0.58  fof(f557,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2)) ) | ~spl5_6),
% 1.74/0.58    inference(resolution,[],[f75,f113])).
% 1.74/0.58  fof(f113,plain,(
% 1.74/0.58    v1_funct_1(sK4) | ~spl5_6),
% 1.74/0.58    inference(avatar_component_clause,[],[f111])).
% 1.74/0.58  fof(f75,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f39])).
% 1.74/0.58  fof(f39,plain,(
% 1.74/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.74/0.58    inference(flattening,[],[f38])).
% 1.74/0.58  fof(f38,plain,(
% 1.74/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.74/0.58    inference(ennf_transformation,[],[f17])).
% 1.74/0.58  fof(f17,axiom,(
% 1.74/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.74/0.58  fof(f126,plain,(
% 1.74/0.58    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_9),
% 1.74/0.58    inference(avatar_component_clause,[],[f124])).
% 1.74/0.58  fof(f1471,plain,(
% 1.74/0.58    ~spl5_154 | spl5_108 | ~spl5_110),
% 1.74/0.58    inference(avatar_split_clause,[],[f1453,f1033,f1011,f1468])).
% 1.74/0.58  fof(f1011,plain,(
% 1.74/0.58    spl5_108 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 1.74/0.58  fof(f1453,plain,(
% 1.74/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_108 | ~spl5_110)),
% 1.74/0.58    inference(backward_demodulation,[],[f1013,f1035])).
% 1.74/0.58  fof(f1013,plain,(
% 1.74/0.58    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_108),
% 1.74/0.58    inference(avatar_component_clause,[],[f1011])).
% 1.74/0.58  fof(f1448,plain,(
% 1.74/0.58    spl5_109 | ~spl5_111 | ~spl5_118),
% 1.74/0.58    inference(avatar_split_clause,[],[f1445,f1113,f1038,f1029])).
% 1.74/0.58  fof(f1029,plain,(
% 1.74/0.58    spl5_109 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 1.74/0.58  fof(f1038,plain,(
% 1.74/0.58    spl5_111 <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 1.74/0.58  fof(f1445,plain,(
% 1.74/0.58    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_111 | ~spl5_118)),
% 1.74/0.58    inference(backward_demodulation,[],[f1040,f1114])).
% 1.74/0.58  fof(f1040,plain,(
% 1.74/0.58    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_111),
% 1.74/0.58    inference(avatar_component_clause,[],[f1038])).
% 1.74/0.58  fof(f1444,plain,(
% 1.74/0.58    ~spl5_100 | spl5_151 | ~spl5_31 | ~spl5_95),
% 1.74/0.58    inference(avatar_split_clause,[],[f1439,f891,f357,f1441,f923])).
% 1.74/0.58  fof(f1439,plain,(
% 1.74/0.58    k1_xboole_0 = k9_relat_1(sK4,sK1) | ~v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_31 | ~spl5_95)),
% 1.74/0.58    inference(forward_demodulation,[],[f980,f377])).
% 1.74/0.58  fof(f980,plain,(
% 1.74/0.58    k1_xboole_0 = k2_relat_1(k7_relat_1(sK4,sK1)) | ~v5_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | ~spl5_95),
% 1.74/0.58    inference(resolution,[],[f893,f175])).
% 1.74/0.58  fof(f175,plain,(
% 1.74/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0)) )),
% 1.74/0.58    inference(resolution,[],[f147,f60])).
% 1.74/0.58  fof(f60,plain,(
% 1.74/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f31])).
% 1.74/0.58  fof(f31,plain,(
% 1.74/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.74/0.58    inference(ennf_transformation,[],[f6])).
% 1.74/0.58  fof(f6,axiom,(
% 1.74/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.74/0.58  fof(f147,plain,(
% 1.74/0.58    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.74/0.58    inference(resolution,[],[f63,f50])).
% 1.74/0.58  fof(f50,plain,(
% 1.74/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f3])).
% 1.74/0.58  fof(f3,axiom,(
% 1.74/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.74/0.58  fof(f63,plain,(
% 1.74/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.74/0.58    inference(cnf_transformation,[],[f2])).
% 1.74/0.58  fof(f2,axiom,(
% 1.74/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.58  fof(f893,plain,(
% 1.74/0.58    v1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_95),
% 1.74/0.58    inference(avatar_component_clause,[],[f891])).
% 1.74/0.58  fof(f1436,plain,(
% 1.74/0.58    spl5_118 | ~spl5_3 | ~spl5_31 | ~spl5_76),
% 1.74/0.58    inference(avatar_split_clause,[],[f1434,f737,f357,f96,f1113])).
% 1.74/0.58  fof(f96,plain,(
% 1.74/0.58    spl5_3 <=> r1_tarski(sK1,sK0)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.74/0.58  fof(f737,plain,(
% 1.74/0.58    spl5_76 <=> sK0 = k1_relat_1(sK4)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 1.74/0.58  fof(f1434,plain,(
% 1.74/0.58    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_3 | ~spl5_31 | ~spl5_76)),
% 1.74/0.58    inference(resolution,[],[f744,f98])).
% 1.74/0.58  fof(f98,plain,(
% 1.74/0.58    r1_tarski(sK1,sK0) | ~spl5_3),
% 1.74/0.58    inference(avatar_component_clause,[],[f96])).
% 1.74/0.60  fof(f744,plain,(
% 1.74/0.60    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | (~spl5_31 | ~spl5_76)),
% 1.74/0.60    inference(backward_demodulation,[],[f378,f739])).
% 1.74/0.60  fof(f739,plain,(
% 1.74/0.60    sK0 = k1_relat_1(sK4) | ~spl5_76),
% 1.74/0.60    inference(avatar_component_clause,[],[f737])).
% 1.74/0.60  fof(f378,plain,(
% 1.74/0.60    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | ~spl5_31),
% 1.74/0.60    inference(resolution,[],[f358,f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f30])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(flattening,[],[f29])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f11])).
% 1.74/0.60  fof(f11,axiom,(
% 1.74/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.74/0.60  fof(f1075,plain,(
% 1.74/0.60    ~spl5_6 | ~spl5_4 | spl5_113 | ~spl5_4 | ~spl5_6),
% 1.74/0.60    inference(avatar_split_clause,[],[f1067,f111,f101,f1073,f101,f111])).
% 1.74/0.60  fof(f1067,plain,(
% 1.74/0.60    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_6)),
% 1.74/0.60    inference(superposition,[],[f76,f857])).
% 1.74/0.60  fof(f76,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.74/0.60    inference(flattening,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f16])).
% 1.74/0.60  fof(f16,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.74/0.60  fof(f1041,plain,(
% 1.74/0.60    spl5_111 | ~spl5_93),
% 1.74/0.60    inference(avatar_split_clause,[],[f1026,f881,f1038])).
% 1.74/0.60  fof(f881,plain,(
% 1.74/0.60    spl5_93 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 1.74/0.60  fof(f1026,plain,(
% 1.74/0.60    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_93),
% 1.74/0.60    inference(resolution,[],[f882,f67])).
% 1.74/0.60  fof(f67,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f34])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.74/0.60  fof(f882,plain,(
% 1.74/0.60    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_93),
% 1.74/0.60    inference(avatar_component_clause,[],[f881])).
% 1.74/0.60  fof(f1036,plain,(
% 1.74/0.60    spl5_108 | ~spl5_109 | spl5_110 | ~spl5_93),
% 1.74/0.60    inference(avatar_split_clause,[],[f1023,f881,f1033,f1029,f1011])).
% 1.74/0.60  fof(f1023,plain,(
% 1.74/0.60    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl5_93),
% 1.74/0.60    inference(resolution,[],[f882,f72])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f36,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(flattening,[],[f35])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.74/0.60  fof(f1014,plain,(
% 1.74/0.60    ~spl5_108 | ~spl5_4 | ~spl5_6 | spl5_8),
% 1.74/0.60    inference(avatar_split_clause,[],[f1009,f120,f111,f101,f1011])).
% 1.74/0.60  fof(f120,plain,(
% 1.74/0.60    spl5_8 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.74/0.60  fof(f1009,plain,(
% 1.74/0.60    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_4 | ~spl5_6 | spl5_8)),
% 1.74/0.60    inference(forward_demodulation,[],[f122,f857])).
% 1.74/0.60  fof(f122,plain,(
% 1.74/0.60    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_8),
% 1.74/0.60    inference(avatar_component_clause,[],[f120])).
% 1.74/0.60  fof(f1007,plain,(
% 1.74/0.60    ~spl5_95 | ~spl5_107 | ~spl5_33 | ~spl5_31 | spl5_93),
% 1.74/0.60    inference(avatar_split_clause,[],[f1006,f881,f357,f370,f963,f891])).
% 1.74/0.60  fof(f963,plain,(
% 1.74/0.60    spl5_107 <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 1.74/0.60  fof(f370,plain,(
% 1.74/0.60    spl5_33 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.74/0.60  fof(f1006,plain,(
% 1.74/0.60    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_31 | spl5_93)),
% 1.74/0.60    inference(forward_demodulation,[],[f1000,f377])).
% 1.74/0.60  fof(f1000,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_93),
% 1.74/0.60    inference(resolution,[],[f883,f66])).
% 1.74/0.60  fof(f66,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.74/0.60    inference(flattening,[],[f32])).
% 1.74/0.60  fof(f32,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.74/0.60    inference(ennf_transformation,[],[f14])).
% 1.74/0.60  fof(f14,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.74/0.60  fof(f883,plain,(
% 1.74/0.60    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_93),
% 1.74/0.60    inference(avatar_component_clause,[],[f881])).
% 1.74/0.60  fof(f1005,plain,(
% 1.74/0.60    ~spl5_31 | spl5_107),
% 1.74/0.60    inference(avatar_split_clause,[],[f1003,f963,f357])).
% 1.74/0.60  fof(f1003,plain,(
% 1.74/0.60    ~v1_relat_1(sK4) | spl5_107),
% 1.74/0.60    inference(resolution,[],[f965,f56])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f9])).
% 1.74/0.60  fof(f9,axiom,(
% 1.74/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.74/0.60  fof(f965,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_107),
% 1.74/0.60    inference(avatar_component_clause,[],[f963])).
% 1.74/0.60  fof(f976,plain,(
% 1.74/0.60    spl5_102 | ~spl5_4 | ~spl5_6 | ~spl5_63),
% 1.74/0.60    inference(avatar_split_clause,[],[f975,f629,f111,f101,f934])).
% 1.74/0.60  fof(f629,plain,(
% 1.74/0.60    spl5_63 <=> v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 1.74/0.60  fof(f975,plain,(
% 1.74/0.60    v5_relat_1(k7_relat_1(sK4,sK1),sK2) | (~spl5_4 | ~spl5_6 | ~spl5_63)),
% 1.74/0.60    inference(forward_demodulation,[],[f630,f857])).
% 1.74/0.60  fof(f630,plain,(
% 1.74/0.60    v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2) | ~spl5_63),
% 1.74/0.60    inference(avatar_component_clause,[],[f629])).
% 1.74/0.60  fof(f970,plain,(
% 1.74/0.60    ~spl5_33 | ~spl5_95 | ~spl5_4 | ~spl5_6 | ~spl5_31 | spl5_63),
% 1.74/0.60    inference(avatar_split_clause,[],[f969,f629,f357,f111,f101,f891,f370])).
% 1.74/0.60  fof(f969,plain,(
% 1.74/0.60    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_4 | ~spl5_6 | ~spl5_31 | spl5_63)),
% 1.74/0.60    inference(forward_demodulation,[],[f968,f857])).
% 1.74/0.60  fof(f968,plain,(
% 1.74/0.60    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_31 | spl5_63)),
% 1.74/0.60    inference(forward_demodulation,[],[f967,f377])).
% 1.74/0.60  fof(f967,plain,(
% 1.74/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_63)),
% 1.74/0.60    inference(forward_demodulation,[],[f633,f857])).
% 1.74/0.60  fof(f633,plain,(
% 1.74/0.60    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_63),
% 1.74/0.60    inference(resolution,[],[f631,f59])).
% 1.74/0.60  fof(f59,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f31])).
% 1.74/0.60  fof(f631,plain,(
% 1.74/0.60    ~v5_relat_1(k2_partfun1(sK0,sK3,sK4,sK1),sK2) | spl5_63),
% 1.74/0.60    inference(avatar_component_clause,[],[f629])).
% 1.74/0.60  fof(f966,plain,(
% 1.74/0.60    ~spl5_107 | ~spl5_33 | ~spl5_95 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_31),
% 1.74/0.60    inference(avatar_split_clause,[],[f961,f357,f116,f111,f101,f891,f370,f963])).
% 1.74/0.60  fof(f116,plain,(
% 1.74/0.60    spl5_7 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.74/0.60  fof(f961,plain,(
% 1.74/0.60    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_31)),
% 1.74/0.60    inference(forward_demodulation,[],[f960,f857])).
% 1.74/0.60  fof(f960,plain,(
% 1.74/0.60    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_31)),
% 1.74/0.60    inference(forward_demodulation,[],[f959,f377])).
% 1.74/0.60  fof(f959,plain,(
% 1.74/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.74/0.60    inference(forward_demodulation,[],[f958,f857])).
% 1.74/0.60  fof(f958,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.74/0.60    inference(forward_demodulation,[],[f635,f857])).
% 1.74/0.60  fof(f635,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_7),
% 1.74/0.60    inference(resolution,[],[f118,f66])).
% 1.74/0.60  fof(f118,plain,(
% 1.74/0.60    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_7),
% 1.74/0.60    inference(avatar_component_clause,[],[f116])).
% 1.74/0.60  fof(f894,plain,(
% 1.74/0.60    spl5_95 | ~spl5_4 | ~spl5_6 | ~spl5_37),
% 1.74/0.60    inference(avatar_split_clause,[],[f863,f414,f111,f101,f891])).
% 1.74/0.60  fof(f414,plain,(
% 1.74/0.60    spl5_37 <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.74/0.60  fof(f863,plain,(
% 1.74/0.60    v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_37)),
% 1.74/0.60    inference(backward_demodulation,[],[f415,f857])).
% 1.74/0.60  fof(f415,plain,(
% 1.74/0.60    v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~spl5_37),
% 1.74/0.60    inference(avatar_component_clause,[],[f414])).
% 1.74/0.60  fof(f741,plain,(
% 1.74/0.60    k1_xboole_0 != sK3 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3)),
% 1.74/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.74/0.60  fof(f740,plain,(
% 1.74/0.60    ~spl5_5 | spl5_75 | spl5_76 | ~spl5_4 | ~spl5_24),
% 1.74/0.60    inference(avatar_split_clause,[],[f731,f269,f101,f737,f733,f106])).
% 1.74/0.60  fof(f106,plain,(
% 1.74/0.60    spl5_5 <=> v1_funct_2(sK4,sK0,sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.74/0.60  fof(f733,plain,(
% 1.74/0.60    spl5_75 <=> k1_xboole_0 = sK3),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 1.74/0.60  fof(f269,plain,(
% 1.74/0.60    spl5_24 <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.74/0.60  fof(f731,plain,(
% 1.74/0.60    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~v1_funct_2(sK4,sK0,sK3) | (~spl5_4 | ~spl5_24)),
% 1.74/0.60    inference(forward_demodulation,[],[f726,f271])).
% 1.74/0.60  fof(f271,plain,(
% 1.74/0.60    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_24),
% 1.74/0.60    inference(avatar_component_clause,[],[f269])).
% 1.74/0.60  fof(f726,plain,(
% 1.74/0.60    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f73,f103])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f36])).
% 1.74/0.60  fof(f585,plain,(
% 1.74/0.60    ~spl5_6 | ~spl5_4 | spl5_37),
% 1.74/0.60    inference(avatar_split_clause,[],[f576,f414,f101,f111])).
% 1.74/0.60  fof(f576,plain,(
% 1.74/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_37),
% 1.74/0.60    inference(resolution,[],[f77,f429])).
% 1.74/0.60  fof(f429,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | spl5_37),
% 1.74/0.60    inference(resolution,[],[f426,f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,axiom,(
% 1.74/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.74/0.60  fof(f426,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0))) ) | spl5_37),
% 1.74/0.60    inference(resolution,[],[f416,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f23])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f5])).
% 1.74/0.60  fof(f5,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.74/0.60  fof(f416,plain,(
% 1.74/0.60    ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_37),
% 1.74/0.60    inference(avatar_component_clause,[],[f414])).
% 1.74/0.60  fof(f77,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f376,plain,(
% 1.74/0.60    ~spl5_4 | spl5_31),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f374])).
% 1.74/0.60  fof(f374,plain,(
% 1.74/0.60    $false | (~spl5_4 | spl5_31)),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f54,f103,f359,f51])).
% 1.74/0.60  fof(f359,plain,(
% 1.74/0.60    ~v1_relat_1(sK4) | spl5_31),
% 1.74/0.60    inference(avatar_component_clause,[],[f357])).
% 1.74/0.60  fof(f373,plain,(
% 1.74/0.60    spl5_33 | ~spl5_2 | ~spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f368,f101,f91,f370])).
% 1.74/0.60  fof(f91,plain,(
% 1.74/0.60    spl5_2 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.74/0.60  fof(f368,plain,(
% 1.74/0.60    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_2 | ~spl5_4)),
% 1.74/0.60    inference(backward_demodulation,[],[f93,f365])).
% 1.74/0.60  fof(f365,plain,(
% 1.74/0.60    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) ) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f74,f103])).
% 1.74/0.60  fof(f74,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f37])).
% 1.74/0.60  fof(f37,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f13])).
% 1.74/0.60  fof(f13,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.74/0.60  fof(f93,plain,(
% 1.74/0.60    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_2),
% 1.74/0.60    inference(avatar_component_clause,[],[f91])).
% 1.74/0.60  fof(f272,plain,(
% 1.74/0.60    spl5_24 | ~spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f265,f101,f269])).
% 1.74/0.60  fof(f265,plain,(
% 1.74/0.60    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f67,f103])).
% 1.74/0.60  fof(f132,plain,(
% 1.74/0.60    spl5_10),
% 1.74/0.60    inference(avatar_split_clause,[],[f49,f129])).
% 1.74/0.60  fof(f129,plain,(
% 1.74/0.60    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    v1_xboole_0(k1_xboole_0)),
% 1.74/0.60    inference(cnf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    v1_xboole_0(k1_xboole_0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.74/0.60  fof(f127,plain,(
% 1.74/0.60    ~spl5_7 | ~spl5_8 | ~spl5_9),
% 1.74/0.60    inference(avatar_split_clause,[],[f42,f124,f120,f116])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f22,plain,(
% 1.74/0.60    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.74/0.60    inference(flattening,[],[f21])).
% 1.74/0.60  fof(f21,plain,(
% 1.74/0.60    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.74/0.60    inference(ennf_transformation,[],[f20])).
% 1.74/0.60  fof(f20,negated_conjecture,(
% 1.74/0.60    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.74/0.60    inference(negated_conjecture,[],[f19])).
% 1.74/0.60  fof(f19,conjecture,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 1.74/0.60  fof(f114,plain,(
% 1.74/0.60    spl5_6),
% 1.74/0.60    inference(avatar_split_clause,[],[f43,f111])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    v1_funct_1(sK4)),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f109,plain,(
% 1.74/0.60    spl5_5),
% 1.74/0.60    inference(avatar_split_clause,[],[f44,f106])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    v1_funct_2(sK4,sK0,sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f104,plain,(
% 1.74/0.60    spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f45,f101])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f99,plain,(
% 1.74/0.60    spl5_3),
% 1.74/0.60    inference(avatar_split_clause,[],[f46,f96])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    r1_tarski(sK1,sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f94,plain,(
% 1.74/0.60    spl5_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f47,f91])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f89,plain,(
% 1.74/0.60    ~spl5_1),
% 1.74/0.60    inference(avatar_split_clause,[],[f48,f86])).
% 1.74/0.60  fof(f86,plain,(
% 1.74/0.60    spl5_1 <=> v1_xboole_0(sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ~v1_xboole_0(sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (11790)------------------------------
% 1.74/0.60  % (11790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (11790)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (11790)Memory used [KB]: 7291
% 1.74/0.60  % (11790)Time elapsed: 0.163 s
% 1.74/0.60  % (11790)------------------------------
% 1.74/0.60  % (11790)------------------------------
% 1.74/0.60  % (11767)Success in time 0.247 s
%------------------------------------------------------------------------------
