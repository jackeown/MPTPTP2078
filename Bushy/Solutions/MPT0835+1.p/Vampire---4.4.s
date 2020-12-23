%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t39_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  353 ( 793 expanded)
%              Number of leaves         :  105 ( 356 expanded)
%              Depth                    :    9
%              Number of atoms          :  830 (1776 expanded)
%              Number of equality atoms :  122 ( 260 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f102,f109,f125,f134,f143,f154,f164,f177,f194,f199,f212,f217,f224,f240,f256,f264,f277,f293,f299,f306,f336,f348,f363,f368,f375,f388,f402,f416,f429,f436,f442,f454,f461,f476,f481,f488,f501,f515,f529,f542,f549,f558,f566,f577,f584,f591,f777,f791,f800,f819,f835,f865,f904,f922,f930,f964,f979,f993,f1194,f1209,f1353,f1363,f1366,f1379,f1382])).

fof(f1382,plain,
    ( ~ spl4_4
    | ~ spl4_8
    | spl4_135 ),
    inference(avatar_contradiction_clause,[],[f1381])).

fof(f1381,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_135 ),
    inference(subsumption_resolution,[],[f1380,f133])).

fof(f133,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_8
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1380,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_135 ),
    inference(superposition,[],[f1378,f841])).

fof(f841,plain,
    ( ! [X18] : k8_relset_1(sK1,sK0,sK2,X18) = k10_relat_1(sK2,X18)
    | ~ spl4_4 ),
    inference(resolution,[],[f87,f108])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',redefinition_k8_relset_1)).

fof(f1378,plain,
    ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1377,plain,
    ( spl4_135
  <=> k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f1379,plain,
    ( ~ spl4_135
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_120
    | spl4_131 ),
    inference(avatar_split_clause,[],[f1369,f1351,f977,f334,f107,f1377])).

fof(f334,plain,
    ( spl4_44
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f977,plain,
    ( spl4_120
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f1351,plain,
    ( spl4_131
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f1369,plain,
    ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_120
    | ~ spl4_131 ),
    inference(forward_demodulation,[],[f1368,f978])).

fof(f978,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f977])).

fof(f1368,plain,
    ( k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_44
    | ~ spl4_131 ),
    inference(forward_demodulation,[],[f1367,f739])).

fof(f739,plain,
    ( ! [X18] : k7_relset_1(sK1,sK0,sK2,X18) = k9_relat_1(sK2,X18)
    | ~ spl4_4 ),
    inference(resolution,[],[f86,f108])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',redefinition_k7_relset_1)).

fof(f1367,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | ~ spl4_44
    | ~ spl4_131 ),
    inference(forward_demodulation,[],[f1352,f335])).

fof(f335,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1352,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1366,plain,
    ( ~ spl4_4
    | ~ spl4_10
    | spl4_133 ),
    inference(avatar_contradiction_clause,[],[f1365])).

fof(f1365,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_133 ),
    inference(subsumption_resolution,[],[f1364,f142])).

fof(f142,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_10
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1364,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_133 ),
    inference(superposition,[],[f1362,f739])).

fof(f1362,plain,
    ( k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl4_133 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f1361,plain,
    ( spl4_133
  <=> k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_133])])).

fof(f1363,plain,
    ( ~ spl4_133
    | ~ spl4_4
    | ~ spl4_34
    | ~ spl4_126
    | spl4_129 ),
    inference(avatar_split_clause,[],[f1356,f1345,f1207,f262,f107,f1361])).

fof(f262,plain,
    ( spl4_34
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f1207,plain,
    ( spl4_126
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f1345,plain,
    ( spl4_129
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f1356,plain,
    ( k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_34
    | ~ spl4_126
    | ~ spl4_129 ),
    inference(forward_demodulation,[],[f1355,f1208])).

fof(f1208,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_126 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1355,plain,
    ( k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_34
    | ~ spl4_129 ),
    inference(forward_demodulation,[],[f1354,f841])).

fof(f1354,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_34
    | ~ spl4_129 ),
    inference(forward_demodulation,[],[f1346,f263])).

fof(f263,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1346,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | ~ spl4_129 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1353,plain,
    ( ~ spl4_129
    | ~ spl4_131 ),
    inference(avatar_split_clause,[],[f63,f1351,f1345])).

fof(f63,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f58])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t39_relset_1)).

fof(f1209,plain,
    ( spl4_126
    | ~ spl4_4
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f1195,f1192,f107,f1207])).

fof(f1192,plain,
    ( spl4_124
  <=> k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f1195,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_4
    | ~ spl4_124 ),
    inference(superposition,[],[f1193,f841])).

fof(f1193,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2)
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f1194,plain,
    ( spl4_124
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1186,f334,f107,f1192])).

fof(f1186,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1169,f335])).

fof(f1169,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f81,f108])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t38_relset_1)).

fof(f993,plain,
    ( ~ spl4_123
    | ~ spl4_102
    | spl4_109 ),
    inference(avatar_split_clause,[],[f986,f830,f789,f991])).

fof(f991,plain,
    ( spl4_123
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f789,plain,
    ( spl4_102
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f830,plain,
    ( spl4_109
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f986,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl4_102
    | ~ spl4_109 ),
    inference(superposition,[],[f831,f790])).

fof(f790,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f789])).

fof(f831,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f830])).

fof(f979,plain,
    ( spl4_120
    | ~ spl4_4
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f965,f962,f107,f977])).

fof(f962,plain,
    ( spl4_118
  <=> k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f965,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_4
    | ~ spl4_118 ),
    inference(superposition,[],[f963,f739])).

fof(f963,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2)
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f962])).

fof(f964,plain,
    ( spl4_118
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f955,f262,f107,f962])).

fof(f955,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f946,f263])).

fof(f946,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f80,f108])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f930,plain,
    ( ~ spl4_115
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f929,f896,f899])).

fof(f899,plain,
    ( spl4_115
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f896,plain,
    ( spl4_112
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f929,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_112 ),
    inference(resolution,[],[f897,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t7_boole)).

fof(f897,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f896])).

fof(f922,plain,
    ( spl4_116
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f914,f833,f920])).

fof(f920,plain,
    ( spl4_116
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f833,plain,
    ( spl4_108
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f914,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_108 ),
    inference(superposition,[],[f69,f834])).

fof(f834,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f833])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',existence_m1_subset_1)).

fof(f904,plain,
    ( spl4_112
    | spl4_114
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f846,f817,f902,f896])).

fof(f902,plain,
    ( spl4_114
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f817,plain,
    ( spl4_106
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f846,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_106 ),
    inference(resolution,[],[f818,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t2_subset)).

fof(f818,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f817])).

fof(f865,plain,
    ( ~ spl4_111
    | ~ spl4_102
    | spl4_105 ),
    inference(avatar_split_clause,[],[f858,f795,f789,f863])).

fof(f863,plain,
    ( spl4_111
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).

fof(f795,plain,
    ( spl4_105
  <=> ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f858,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl4_102
    | ~ spl4_105 ),
    inference(superposition,[],[f796,f790])).

fof(f796,plain,
    ( ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_105 ),
    inference(avatar_component_clause,[],[f795])).

fof(f835,plain,
    ( spl4_108
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_104 ),
    inference(avatar_split_clause,[],[f824,f798,f162,f152,f833])).

fof(f152,plain,
    ( spl4_12
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f162,plain,
    ( spl4_14
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f798,plain,
    ( spl4_104
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f824,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_104 ),
    inference(forward_demodulation,[],[f820,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f820,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_12
    | ~ spl4_104 ),
    inference(resolution,[],[f799,f156])).

fof(f156,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_12 ),
    inference(resolution,[],[f153,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t8_boole)).

fof(f153,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f799,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f798])).

fof(f819,plain,
    ( spl4_106
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f807,f789,f817])).

fof(f807,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_102 ),
    inference(superposition,[],[f69,f790])).

fof(f800,plain,
    ( spl4_104
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f792,f769,f798])).

fof(f769,plain,
    ( spl4_98
  <=> ! [X5] : ~ r2_hidden(X5,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f792,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_98 ),
    inference(resolution,[],[f770,f112])).

fof(f112,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f69])).

fof(f770,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f769])).

fof(f791,plain,
    ( spl4_102
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f782,f775,f162,f152,f789])).

fof(f775,plain,
    ( spl4_100
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f782,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f778,f163])).

fof(f778,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_12
    | ~ spl4_100 ),
    inference(resolution,[],[f776,f156])).

fof(f776,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f775])).

fof(f777,plain,
    ( spl4_98
    | spl4_100
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f310,f93,f775,f769])).

fof(f93,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f310,plain,
    ( ! [X5] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X5,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl4_0 ),
    inference(resolution,[],[f225,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f83,f94])).

fof(f94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f93])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t5_subset)).

fof(f225,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f145,f69])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f82,f112])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t4_subset)).

fof(f591,plain,
    ( spl4_96
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f555,f474,f162,f152,f589])).

fof(f589,plain,
    ( spl4_96
  <=> k1_zfmisc_1(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f474,plain,
    ( spl4_74
  <=> v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f555,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f551,f163])).

fof(f551,plain,
    ( k1_zfmisc_1(sK1) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_74 ),
    inference(resolution,[],[f475,f156])).

fof(f475,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f474])).

fof(f584,plain,
    ( ~ spl4_95
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f575,f521,f582])).

fof(f582,plain,
    ( spl4_95
  <=> ~ r2_hidden(sK1,sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f521,plain,
    ( spl4_84
  <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f575,plain,
    ( ~ r2_hidden(sK1,sK3(k1_relat_1(sK2)))
    | ~ spl4_84 ),
    inference(resolution,[],[f522,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',antisymmetry_r2_hidden)).

fof(f522,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f521])).

fof(f577,plain,
    ( ~ spl4_87
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f576,f521,f524])).

fof(f524,plain,
    ( spl4_87
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f576,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_84 ),
    inference(resolution,[],[f522,f74])).

fof(f566,plain,
    ( spl4_92
    | ~ spl4_70
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f534,f513,f459,f564])).

fof(f564,plain,
    ( spl4_92
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f459,plain,
    ( spl4_70
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f513,plain,
    ( spl4_82
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f534,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_70
    | ~ spl4_82 ),
    inference(superposition,[],[f460,f514])).

fof(f514,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f513])).

fof(f460,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f459])).

fof(f558,plain,
    ( ~ spl4_91
    | spl4_73
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f550,f513,f465,f544])).

fof(f544,plain,
    ( spl4_91
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f465,plain,
    ( spl4_73
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f550,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_73
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f466,f514])).

fof(f466,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f465])).

fof(f549,plain,
    ( spl4_90
    | ~ spl4_72
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f533,f513,f468,f547])).

fof(f547,plain,
    ( spl4_90
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f468,plain,
    ( spl4_72
  <=> r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f533,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl4_72
    | ~ spl4_82 ),
    inference(superposition,[],[f469,f514])).

fof(f469,plain,
    ( r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f468])).

fof(f542,plain,
    ( ~ spl4_89
    | spl4_81
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f530,f513,f496,f540])).

fof(f540,plain,
    ( spl4_89
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f496,plain,
    ( spl4_81
  <=> ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f530,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK1)
    | ~ spl4_81
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f497,f514])).

fof(f497,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f496])).

fof(f529,plain,
    ( spl4_84
    | spl4_86
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f516,f499,f527,f521])).

fof(f527,plain,
    ( spl4_86
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f499,plain,
    ( spl4_80
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f516,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_80 ),
    inference(resolution,[],[f500,f72])).

fof(f500,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f499])).

fof(f515,plain,
    ( spl4_82
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f506,f493,f162,f152,f513])).

fof(f493,plain,
    ( spl4_78
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f506,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_78 ),
    inference(forward_demodulation,[],[f502,f163])).

fof(f502,plain,
    ( k1_relat_1(sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_78 ),
    inference(resolution,[],[f494,f156])).

fof(f494,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f493])).

fof(f501,plain,
    ( spl4_78
    | spl4_80
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f462,f459,f499,f493])).

fof(f462,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_70 ),
    inference(resolution,[],[f460,f145])).

fof(f488,plain,
    ( ~ spl4_77
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f479,f468,f486])).

fof(f486,plain,
    ( spl4_77
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f479,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),k1_relat_1(sK2))
    | ~ spl4_72 ),
    inference(resolution,[],[f469,f70])).

fof(f481,plain,
    ( ~ spl4_75
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f480,f468,f471])).

fof(f471,plain,
    ( spl4_75
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f480,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_72 ),
    inference(resolution,[],[f469,f74])).

fof(f476,plain,
    ( spl4_72
    | spl4_74
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f463,f459,f474,f468])).

fof(f463,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_70 ),
    inference(resolution,[],[f460,f72])).

fof(f461,plain,
    ( spl4_70
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f446,f334,f107,f459])).

fof(f446,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f443,f335])).

fof(f443,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f79,f108])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',dt_k1_relset_1)).

fof(f454,plain,
    ( ~ spl4_69
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f440,f408,f452])).

fof(f452,plain,
    ( spl4_69
  <=> ~ r2_hidden(sK0,sK3(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f408,plain,
    ( spl4_60
  <=> r2_hidden(sK3(k2_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f440,plain,
    ( ~ r2_hidden(sK0,sK3(k2_relat_1(sK2)))
    | ~ spl4_60 ),
    inference(resolution,[],[f409,f70])).

fof(f409,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),sK0)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f408])).

fof(f442,plain,
    ( ~ spl4_63
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f441,f408,f411])).

fof(f411,plain,
    ( spl4_63
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f441,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_60 ),
    inference(resolution,[],[f409,f74])).

fof(f436,plain,
    ( spl4_66
    | ~ spl4_48
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f420,f400,f355,f434])).

fof(f434,plain,
    ( spl4_66
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f355,plain,
    ( spl4_48
  <=> r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f400,plain,
    ( spl4_58
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f420,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_48
    | ~ spl4_58 ),
    inference(superposition,[],[f356,f401])).

fof(f401,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f400])).

fof(f356,plain,
    ( r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f355])).

fof(f429,plain,
    ( ~ spl4_65
    | spl4_57
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f417,f400,f383,f427])).

fof(f427,plain,
    ( spl4_65
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f383,plain,
    ( spl4_57
  <=> ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f417,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK0)
    | ~ spl4_57
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f384,f401])).

fof(f384,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK0)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f383])).

fof(f416,plain,
    ( spl4_60
    | spl4_62
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f403,f386,f414,f408])).

fof(f414,plain,
    ( spl4_62
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f386,plain,
    ( spl4_56
  <=> m1_subset_1(sK3(k2_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f403,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3(k2_relat_1(sK2)),sK0)
    | ~ spl4_56 ),
    inference(resolution,[],[f387,f72])).

fof(f387,plain,
    ( m1_subset_1(sK3(k2_relat_1(sK2)),sK0)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f386])).

fof(f402,plain,
    ( spl4_58
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f393,f380,f162,f152,f400])).

fof(f380,plain,
    ( spl4_54
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f393,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f389,f163])).

fof(f389,plain,
    ( k2_relat_1(sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(resolution,[],[f381,f156])).

fof(f381,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f380])).

fof(f388,plain,
    ( spl4_54
    | spl4_56
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f349,f346,f386,f380])).

fof(f346,plain,
    ( spl4_46
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f349,plain,
    ( m1_subset_1(sK3(k2_relat_1(sK2)),sK0)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl4_46 ),
    inference(resolution,[],[f347,f145])).

fof(f347,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f346])).

fof(f375,plain,
    ( ~ spl4_53
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f366,f355,f373])).

fof(f373,plain,
    ( spl4_53
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f366,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k2_relat_1(sK2))
    | ~ spl4_48 ),
    inference(resolution,[],[f356,f70])).

fof(f368,plain,
    ( ~ spl4_51
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f367,f355,f358])).

fof(f358,plain,
    ( spl4_51
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f367,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_48 ),
    inference(resolution,[],[f356,f74])).

fof(f363,plain,
    ( spl4_48
    | spl4_50
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f350,f346,f361,f355])).

fof(f361,plain,
    ( spl4_50
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f350,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_46 ),
    inference(resolution,[],[f347,f72])).

fof(f348,plain,
    ( spl4_46
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f341,f262,f107,f346])).

fof(f341,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f339,f263])).

fof(f339,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f78,f108])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',dt_k2_relset_1)).

fof(f336,plain,
    ( spl4_44
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f329,f107,f334])).

fof(f329,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f77,f108])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',redefinition_k1_relset_1)).

fof(f306,plain,
    ( ~ spl4_43
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f297,f269,f304])).

fof(f304,plain,
    ( spl4_43
  <=> ~ r2_hidden(k2_zfmisc_1(sK1,sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f269,plain,
    ( spl4_36
  <=> r2_hidden(sK3(sK2),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f297,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK1,sK0),sK3(sK2))
    | ~ spl4_36 ),
    inference(resolution,[],[f270,f70])).

fof(f270,plain,
    ( r2_hidden(sK3(sK2),k2_zfmisc_1(sK1,sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f269])).

fof(f299,plain,
    ( ~ spl4_39
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f298,f269,f272])).

fof(f272,plain,
    ( spl4_39
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f298,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_36 ),
    inference(resolution,[],[f270,f74])).

fof(f293,plain,
    ( spl4_40
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f281,f254,f123,f291])).

fof(f291,plain,
    ( spl4_40
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f123,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f254,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f281,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(superposition,[],[f124,f255])).

fof(f255,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f254])).

fof(f124,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f277,plain,
    ( spl4_36
    | spl4_38
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f257,f238,f275,f269])).

fof(f275,plain,
    ( spl4_38
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f238,plain,
    ( spl4_30
  <=> m1_subset_1(sK3(sK2),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f257,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | r2_hidden(sK3(sK2),k2_zfmisc_1(sK1,sK0))
    | ~ spl4_30 ),
    inference(resolution,[],[f239,f72])).

fof(f239,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK1,sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f264,plain,
    ( spl4_34
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f242,f107,f262])).

fof(f242,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f76,f108])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',redefinition_k2_relset_1)).

fof(f256,plain,
    ( spl4_32
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f247,f232,f162,f152,f254])).

fof(f232,plain,
    ( spl4_28
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f247,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f243,f163])).

fof(f243,plain,
    ( sK2 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(resolution,[],[f233,f156])).

fof(f233,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f232])).

fof(f240,plain,
    ( spl4_28
    | spl4_30
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f226,f107,f238,f232])).

fof(f226,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK1,sK0))
    | v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f145,f108])).

fof(f224,plain,
    ( ~ spl4_27
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f215,f204,f222])).

fof(f222,plain,
    ( spl4_27
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f204,plain,
    ( spl4_22
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f215,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),sK2)
    | ~ spl4_22 ),
    inference(resolution,[],[f205,f70])).

fof(f205,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f217,plain,
    ( ~ spl4_25
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f216,f204,f207])).

fof(f207,plain,
    ( spl4_25
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f216,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_22 ),
    inference(resolution,[],[f205,f74])).

fof(f212,plain,
    ( spl4_22
    | spl4_24
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f113,f107,f210,f204])).

fof(f210,plain,
    ( spl4_24
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f113,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f72,f108])).

fof(f199,plain,
    ( ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f198,f192,f183])).

fof(f183,plain,
    ( spl4_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f192,plain,
    ( spl4_20
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f198,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(resolution,[],[f193,f74])).

fof(f193,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl4_18
    | spl4_20
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f168,f162,f192,f186])).

fof(f186,plain,
    ( spl4_18
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f168,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(superposition,[],[f112,f163])).

fof(f177,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f169,f162,f175])).

fof(f175,plain,
    ( spl4_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f169,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(superposition,[],[f69,f163])).

fof(f164,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f157,f152,f162])).

fof(f157,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(resolution,[],[f153,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t6_boole)).

fof(f154,plain,
    ( spl4_12
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f147,f93,f152])).

fof(f147,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f146,f112])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f144,f69])).

fof(f143,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f135,f123,f141])).

fof(f135,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f67,f124])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t146_relat_1)).

fof(f134,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f126,f123,f132])).

fof(f126,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f124])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',t169_relat_1)).

fof(f125,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f107,f123])).

fof(f118,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f75,f108])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',cc1_relset_1)).

fof(f109,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f62,f107])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f102,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f65,f100])).

fof(f100,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',d2_xboole_0)).

fof(f95,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f88,f93])).

fof(f88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f64,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t39_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
