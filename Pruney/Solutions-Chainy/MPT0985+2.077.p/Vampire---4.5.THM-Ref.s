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
% DateTime   : Thu Dec  3 13:02:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 381 expanded)
%              Number of leaves         :   51 ( 170 expanded)
%              Depth                    :    9
%              Number of atoms          :  661 (1276 expanded)
%              Number of equality atoms :   96 ( 197 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f103,f107,f111,f119,f123,f133,f136,f149,f152,f214,f256,f272,f289,f294,f299,f334,f354,f358,f368,f506,f655,f666,f673,f715,f755,f782,f940,f1037,f1039,f1357,f1375,f1379])).

fof(f1379,plain,
    ( ~ spl4_9
    | spl4_81 ),
    inference(avatar_contradiction_clause,[],[f1376])).

fof(f1376,plain,
    ( $false
    | ~ spl4_9
    | spl4_81 ),
    inference(resolution,[],[f1374,f194])).

fof(f194,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl4_9 ),
    inference(superposition,[],[f77,f191])).

fof(f191,plain,
    ( ! [X0] : k1_xboole_0 = sK3(k1_xboole_0,X0)
    | ~ spl4_9 ),
    inference(resolution,[],[f188,f73])).

fof(f73,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v4_relat_1(sK3(X0,X1),X0)
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v4_relat_1(sK3(X0,X1),X0)
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(resolution,[],[f183,f122])).

fof(f122,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f183,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f77,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1374,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_81 ),
    inference(avatar_component_clause,[],[f1373])).

fof(f1373,plain,
    ( spl4_81
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1375,plain,
    ( ~ spl4_81
    | spl4_2
    | ~ spl4_42
    | ~ spl4_43
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1371,f718,f366,f362,f94,f1373])).

fof(f94,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f362,plain,
    ( spl4_42
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f366,plain,
    ( spl4_43
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f718,plain,
    ( spl4_62
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1371,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_42
    | ~ spl4_43
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1370,f719])).

fof(f719,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f718])).

fof(f1370,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_42
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f1369,f367])).

fof(f367,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f366])).

fof(f1369,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f95,f563])).

fof(f563,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f362])).

fof(f95,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1357,plain,(
    spl4_71 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | spl4_71 ),
    inference(resolution,[],[f939,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f939,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl4_71
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1039,plain,
    ( ~ spl4_10
    | ~ spl4_61
    | spl4_70 ),
    inference(avatar_split_clause,[],[f1038,f785,f713,f130])).

fof(f130,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f713,plain,
    ( spl4_61
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f785,plain,
    ( spl4_70
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1038,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl4_70 ),
    inference(resolution,[],[f786,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f786,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_70 ),
    inference(avatar_component_clause,[],[f785])).

fof(f1037,plain,
    ( ~ spl4_70
    | spl4_31
    | ~ spl4_41
    | ~ spl4_40
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f1035,f504,f352,f356,f287,f785])).

fof(f287,plain,
    ( spl4_31
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f356,plain,
    ( spl4_41
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f352,plain,
    ( spl4_40
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f504,plain,
    ( spl4_53
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1035,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_40
    | ~ spl4_53 ),
    inference(resolution,[],[f505,f353])).

fof(f353,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f352])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0) )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f504])).

fof(f940,plain,
    ( ~ spl4_71
    | spl4_3
    | ~ spl4_42
    | ~ spl4_43
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f936,f718,f366,f362,f97,f938])).

fof(f97,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f936,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_42
    | ~ spl4_43
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f935,f719])).

fof(f935,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_42
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f913,f563])).

fof(f913,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3
    | ~ spl4_43 ),
    inference(superposition,[],[f98,f367])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f782,plain,
    ( ~ spl4_6
    | spl4_61 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | ~ spl4_6
    | spl4_61 ),
    inference(subsumption_resolution,[],[f110,f772])).

fof(f772,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl4_61 ),
    inference(resolution,[],[f714,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f714,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_61 ),
    inference(avatar_component_clause,[],[f713])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f755,plain,
    ( spl4_62
    | ~ spl4_27
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f754,f366,f251,f718])).

fof(f251,plain,
    ( spl4_27
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f754,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_27
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f252,f367])).

fof(f252,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f715,plain,
    ( ~ spl4_61
    | spl4_3
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f707,f664,f97,f713])).

fof(f664,plain,
    ( spl4_57
  <=> ! [X0] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f707,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_3
    | ~ spl4_57 ),
    inference(resolution,[],[f665,f98])).

fof(f665,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f664])).

fof(f673,plain,
    ( k1_xboole_0 != k2_funct_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f666,plain,
    ( ~ spl4_10
    | spl4_57
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f662,f652,f664,f130])).

fof(f652,plain,
    ( spl4_56
  <=> ! [X0] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f662,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_56 ),
    inference(resolution,[],[f653,f71])).

fof(f653,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f652])).

fof(f655,plain,
    ( ~ spl4_10
    | ~ spl4_8
    | ~ spl4_41
    | spl4_31
    | spl4_56
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f645,f352,f652,f287,f356,f117,f130])).

fof(f117,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f645,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | k1_xboole_0 = k1_relat_1(sK2)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_40 ),
    inference(resolution,[],[f556,f353])).

fof(f556,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X3)))
      | ~ r1_tarski(X3,X4)
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k2_funct_1(X5),X6,X3)
      | m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X4)))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f85,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

% (309)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f506,plain,
    ( ~ spl4_1
    | spl4_53
    | spl4_2 ),
    inference(avatar_split_clause,[],[f502,f94,f504,f91])).

fof(f91,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f502,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | spl4_2 ),
    inference(resolution,[],[f83,f95])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f368,plain,
    ( ~ spl4_10
    | spl4_43
    | ~ spl4_42
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f345,f331,f362,f366,f130])).

fof(f331,plain,
    ( spl4_38
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f345,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_38 ),
    inference(superposition,[],[f60,f332])).

fof(f332,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f331])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f358,plain,
    ( spl4_41
    | ~ spl4_30
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f340,f331,f283,f356])).

fof(f283,plain,
    ( spl4_30
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f340,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl4_30
    | ~ spl4_38 ),
    inference(superposition,[],[f284,f332])).

fof(f284,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f283])).

fof(f354,plain,
    ( spl4_40
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f339,f331,f297,f352])).

fof(f297,plain,
    ( spl4_32
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f339,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(superposition,[],[f298,f332])).

fof(f298,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f297])).

fof(f334,plain,
    ( ~ spl4_6
    | spl4_38
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f328,f101,f331,f109])).

fof(f101,plain,
    ( spl4_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f328,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f102,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f102,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f299,plain,
    ( ~ spl4_20
    | ~ spl4_1
    | spl4_32
    | ~ spl4_18
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f295,f270,f212,f297,f91,f225])).

fof(f225,plain,
    ( spl4_20
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( spl4_18
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f270,plain,
    ( spl4_29
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f295,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f279,f213])).

fof(f213,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f279,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(superposition,[],[f65,f271])).

fof(f271,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f270])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f294,plain,
    ( ~ spl4_20
    | ~ spl4_1
    | spl4_30
    | ~ spl4_18
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f293,f270,f212,f283,f91,f225])).

fof(f293,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_18
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f278,f213])).

fof(f278,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(superposition,[],[f64,f271])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f289,plain,
    ( ~ spl4_20
    | spl4_27
    | ~ spl4_31
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f276,f270,f287,f251,f225])).

fof(f276,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(superposition,[],[f60,f271])).

fof(f272,plain,
    ( ~ spl4_10
    | ~ spl4_8
    | spl4_29
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f268,f105,f270,f117,f130])).

fof(f105,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f268,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f69,f106])).

fof(f106,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f256,plain,
    ( ~ spl4_10
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_split_clause,[],[f254,f225,f117,f130])).

fof(f254,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_20 ),
    inference(resolution,[],[f226,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f226,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f214,plain,
    ( ~ spl4_10
    | ~ spl4_8
    | spl4_18
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f210,f105,f212,f117,f130])).

fof(f210,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f68,f106])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f152,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f150,f56])).

fof(f150,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_12 ),
    inference(resolution,[],[f148,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f148,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f149,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f141,f121,f147,f144])).

fof(f144,plain,
    ( spl4_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f141,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(resolution,[],[f140,f122])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f62,f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f57])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f136,plain,
    ( ~ spl4_6
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_6
    | spl4_10 ),
    inference(subsumption_resolution,[],[f110,f134])).

fof(f134,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_10 ),
    inference(resolution,[],[f78,f131])).

fof(f131,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( ~ spl4_10
    | ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f128,f91,f117,f130])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f67,f92])).

fof(f92,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f123,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f119,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f111,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f97,f94,f91])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (32765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (305)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (32764)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (304)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (306)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (32767)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (307)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (32759)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (32766)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (32760)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (32762)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (32763)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (32761)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.55  % (302)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (301)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.55  % (308)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  % (310)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.56  % (303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (32765)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1384,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f99,f103,f107,f111,f119,f123,f133,f136,f149,f152,f214,f256,f272,f289,f294,f299,f334,f354,f358,f368,f506,f655,f666,f673,f715,f755,f782,f940,f1037,f1039,f1357,f1375,f1379])).
% 0.21/0.56  fof(f1379,plain,(
% 0.21/0.56    ~spl4_9 | spl4_81),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1376])).
% 0.21/0.56  fof(f1376,plain,(
% 0.21/0.56    $false | (~spl4_9 | spl4_81)),
% 0.21/0.56    inference(resolution,[],[f1374,f194])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl4_9),
% 0.21/0.56    inference(superposition,[],[f77,f191])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK3(k1_xboole_0,X0)) ) | ~spl4_9),
% 0.21/0.56    inference(resolution,[],[f188,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.21/0.56    inference(resolution,[],[f183,f122])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~v1_xboole_0(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_xboole_0 = X3) )),
% 0.21/0.56    inference(resolution,[],[f70,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f1374,plain,(
% 0.21/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl4_81),
% 0.21/0.56    inference(avatar_component_clause,[],[f1373])).
% 0.21/0.56  fof(f1373,plain,(
% 0.21/0.56    spl4_81 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.21/0.56  fof(f1375,plain,(
% 0.21/0.56    ~spl4_81 | spl4_2 | ~spl4_42 | ~spl4_43 | ~spl4_62),
% 0.21/0.56    inference(avatar_split_clause,[],[f1371,f718,f366,f362,f94,f1373])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.56  fof(f362,plain,(
% 0.21/0.56    spl4_42 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.56  fof(f366,plain,(
% 0.21/0.56    spl4_43 <=> k1_xboole_0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.56  fof(f718,plain,(
% 0.21/0.56    spl4_62 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.56  fof(f1371,plain,(
% 0.21/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_42 | ~spl4_43 | ~spl4_62)),
% 0.21/0.56    inference(forward_demodulation,[],[f1370,f719])).
% 0.21/0.56  fof(f719,plain,(
% 0.21/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl4_62),
% 0.21/0.56    inference(avatar_component_clause,[],[f718])).
% 0.21/0.56  fof(f1370,plain,(
% 0.21/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_42 | ~spl4_43)),
% 0.21/0.56    inference(forward_demodulation,[],[f1369,f367])).
% 0.21/0.56  fof(f367,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl4_43),
% 0.21/0.56    inference(avatar_component_clause,[],[f366])).
% 0.21/0.56  fof(f1369,plain,(
% 0.21/0.56    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_42)),
% 0.21/0.56    inference(forward_demodulation,[],[f95,f563])).
% 0.21/0.56  fof(f563,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~spl4_42),
% 0.21/0.56    inference(avatar_component_clause,[],[f362])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f94])).
% 0.21/0.56  fof(f1357,plain,(
% 0.21/0.56    spl4_71),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1356])).
% 0.21/0.56  fof(f1356,plain,(
% 0.21/0.56    $false | spl4_71),
% 0.21/0.56    inference(resolution,[],[f939,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f939,plain,(
% 0.21/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_71),
% 0.21/0.56    inference(avatar_component_clause,[],[f938])).
% 0.21/0.56  fof(f938,plain,(
% 0.21/0.56    spl4_71 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.21/0.56  fof(f1039,plain,(
% 0.21/0.56    ~spl4_10 | ~spl4_61 | spl4_70),
% 0.21/0.56    inference(avatar_split_clause,[],[f1038,f785,f713,f130])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    spl4_10 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.56  fof(f713,plain,(
% 0.21/0.56    spl4_61 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.21/0.56  fof(f785,plain,(
% 0.21/0.56    spl4_70 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.21/0.56  fof(f1038,plain,(
% 0.21/0.56    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl4_70),
% 0.21/0.56    inference(resolution,[],[f786,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.56  fof(f786,plain,(
% 0.21/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_70),
% 0.21/0.56    inference(avatar_component_clause,[],[f785])).
% 0.21/0.56  fof(f1037,plain,(
% 0.21/0.56    ~spl4_70 | spl4_31 | ~spl4_41 | ~spl4_40 | ~spl4_53),
% 0.21/0.56    inference(avatar_split_clause,[],[f1035,f504,f352,f356,f287,f785])).
% 0.21/0.56  fof(f287,plain,(
% 0.21/0.56    spl4_31 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.56  fof(f356,plain,(
% 0.21/0.56    spl4_41 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    spl4_40 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.56  fof(f504,plain,(
% 0.21/0.56    spl4_53 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(X0,sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.56  fof(f1035,plain,(
% 0.21/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | (~spl4_40 | ~spl4_53)),
% 0.21/0.56    inference(resolution,[],[f505,f353])).
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl4_40),
% 0.21/0.56    inference(avatar_component_clause,[],[f352])).
% 0.21/0.56  fof(f505,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK0)) ) | ~spl4_53),
% 0.21/0.56    inference(avatar_component_clause,[],[f504])).
% 0.21/0.56  fof(f940,plain,(
% 0.21/0.56    ~spl4_71 | spl4_3 | ~spl4_42 | ~spl4_43 | ~spl4_62),
% 0.21/0.56    inference(avatar_split_clause,[],[f936,f718,f366,f362,f97,f938])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.56  fof(f936,plain,(
% 0.21/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_42 | ~spl4_43 | ~spl4_62)),
% 0.21/0.56    inference(forward_demodulation,[],[f935,f719])).
% 0.21/0.56  fof(f935,plain,(
% 0.21/0.56    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_42 | ~spl4_43)),
% 0.21/0.56    inference(forward_demodulation,[],[f913,f563])).
% 0.21/0.56  fof(f913,plain,(
% 0.21/0.56    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl4_3 | ~spl4_43)),
% 0.21/0.56    inference(superposition,[],[f98,f367])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f97])).
% 0.21/0.56  fof(f782,plain,(
% 0.21/0.56    ~spl4_6 | spl4_61),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f774])).
% 0.21/0.56  fof(f774,plain,(
% 0.21/0.56    $false | (~spl4_6 | spl4_61)),
% 0.21/0.56    inference(subsumption_resolution,[],[f110,f772])).
% 0.21/0.56  fof(f772,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl4_61),
% 0.21/0.56    inference(resolution,[],[f714,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f714,plain,(
% 0.21/0.56    ~v4_relat_1(sK2,sK0) | spl4_61),
% 0.21/0.56    inference(avatar_component_clause,[],[f713])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.56  fof(f755,plain,(
% 0.21/0.56    spl4_62 | ~spl4_27 | ~spl4_43),
% 0.21/0.56    inference(avatar_split_clause,[],[f754,f366,f251,f718])).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    spl4_27 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.56  fof(f754,plain,(
% 0.21/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_27 | ~spl4_43)),
% 0.21/0.56    inference(forward_demodulation,[],[f252,f367])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_27),
% 0.21/0.56    inference(avatar_component_clause,[],[f251])).
% 0.21/0.56  fof(f715,plain,(
% 0.21/0.56    ~spl4_61 | spl4_3 | ~spl4_57),
% 0.21/0.56    inference(avatar_split_clause,[],[f707,f664,f97,f713])).
% 0.21/0.56  fof(f664,plain,(
% 0.21/0.56    spl4_57 <=> ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v4_relat_1(sK2,X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.56  fof(f707,plain,(
% 0.21/0.56    ~v4_relat_1(sK2,sK0) | (spl4_3 | ~spl4_57)),
% 0.21/0.56    inference(resolution,[],[f665,f98])).
% 0.21/0.56  fof(f665,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v4_relat_1(sK2,X0)) ) | ~spl4_57),
% 0.21/0.56    inference(avatar_component_clause,[],[f664])).
% 0.21/0.56  fof(f673,plain,(
% 0.21/0.56    k1_xboole_0 != k2_funct_1(sK2) | sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f666,plain,(
% 0.21/0.56    ~spl4_10 | spl4_57 | ~spl4_56),
% 0.21/0.56    inference(avatar_split_clause,[],[f662,f652,f664,f130])).
% 0.21/0.56  fof(f652,plain,(
% 0.21/0.56    spl4_56 <=> ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.56  fof(f662,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl4_56),
% 0.21/0.56    inference(resolution,[],[f653,f71])).
% 0.21/0.56  fof(f653,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl4_56),
% 0.21/0.56    inference(avatar_component_clause,[],[f652])).
% 0.21/0.56  fof(f655,plain,(
% 0.21/0.56    ~spl4_10 | ~spl4_8 | ~spl4_41 | spl4_31 | spl4_56 | ~spl4_40),
% 0.21/0.56    inference(avatar_split_clause,[],[f645,f352,f652,f287,f356,f117,f130])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl4_8 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.56  fof(f645,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_40),
% 0.21/0.56    inference(resolution,[],[f556,f353])).
% 0.21/0.56  fof(f556,plain,(
% 0.21/0.56    ( ! [X6,X4,X5,X3] : (~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X3))) | ~r1_tarski(X3,X4) | k1_xboole_0 = X3 | ~v1_funct_2(k2_funct_1(X5),X6,X3) | m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X4))) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.21/0.56    inference(resolution,[],[f85,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  % (309)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.56    inference(flattening,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.56  fof(f506,plain,(
% 0.21/0.56    ~spl4_1 | spl4_53 | spl4_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f502,f94,f504,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.56  fof(f502,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_1(k2_funct_1(sK2))) ) | spl4_2),
% 0.21/0.56    inference(resolution,[],[f83,f95])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f368,plain,(
% 0.21/0.56    ~spl4_10 | spl4_43 | ~spl4_42 | ~spl4_38),
% 0.21/0.56    inference(avatar_split_clause,[],[f345,f331,f362,f366,f130])).
% 0.21/0.56  fof(f331,plain,(
% 0.21/0.56    spl4_38 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.56  fof(f345,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl4_38),
% 0.21/0.56    inference(superposition,[],[f60,f332])).
% 0.21/0.56  fof(f332,plain,(
% 0.21/0.56    sK1 = k2_relat_1(sK2) | ~spl4_38),
% 0.21/0.56    inference(avatar_component_clause,[],[f331])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f358,plain,(
% 0.21/0.56    spl4_41 | ~spl4_30 | ~spl4_38),
% 0.21/0.56    inference(avatar_split_clause,[],[f340,f331,f283,f356])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    spl4_30 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.56  fof(f340,plain,(
% 0.21/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl4_30 | ~spl4_38)),
% 0.21/0.56    inference(superposition,[],[f284,f332])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl4_30),
% 0.21/0.56    inference(avatar_component_clause,[],[f283])).
% 0.21/0.56  fof(f354,plain,(
% 0.21/0.56    spl4_40 | ~spl4_32 | ~spl4_38),
% 0.21/0.56    inference(avatar_split_clause,[],[f339,f331,f297,f352])).
% 0.21/0.56  fof(f297,plain,(
% 0.21/0.56    spl4_32 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.56  fof(f339,plain,(
% 0.21/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl4_32 | ~spl4_38)),
% 0.21/0.56    inference(superposition,[],[f298,f332])).
% 0.21/0.56  fof(f298,plain,(
% 0.21/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl4_32),
% 0.21/0.56    inference(avatar_component_clause,[],[f297])).
% 0.21/0.56  fof(f334,plain,(
% 0.21/0.56    ~spl4_6 | spl4_38 | ~spl4_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f328,f101,f331,f109])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl4_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.56  fof(f328,plain,(
% 0.21/0.56    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.56    inference(superposition,[],[f102,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f101])).
% 0.21/0.56  fof(f299,plain,(
% 0.21/0.56    ~spl4_20 | ~spl4_1 | spl4_32 | ~spl4_18 | ~spl4_29),
% 0.21/0.56    inference(avatar_split_clause,[],[f295,f270,f212,f297,f91,f225])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    spl4_20 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    spl4_18 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.56  fof(f270,plain,(
% 0.21/0.56    spl4_29 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.56  fof(f295,plain,(
% 0.21/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_18 | ~spl4_29)),
% 0.21/0.56    inference(forward_demodulation,[],[f279,f213])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f212])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_29),
% 0.21/0.56    inference(superposition,[],[f65,f271])).
% 0.21/0.56  fof(f271,plain,(
% 0.21/0.56    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl4_29),
% 0.21/0.56    inference(avatar_component_clause,[],[f270])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    ~spl4_20 | ~spl4_1 | spl4_30 | ~spl4_18 | ~spl4_29),
% 0.21/0.56    inference(avatar_split_clause,[],[f293,f270,f212,f283,f91,f225])).
% 0.21/0.56  fof(f293,plain,(
% 0.21/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_18 | ~spl4_29)),
% 0.21/0.56    inference(forward_demodulation,[],[f278,f213])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_29),
% 0.21/0.56    inference(superposition,[],[f64,f271])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f289,plain,(
% 0.21/0.56    ~spl4_20 | spl4_27 | ~spl4_31 | ~spl4_29),
% 0.21/0.56    inference(avatar_split_clause,[],[f276,f270,f287,f251,f225])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_29),
% 0.21/0.56    inference(superposition,[],[f60,f271])).
% 0.21/0.56  fof(f272,plain,(
% 0.21/0.56    ~spl4_10 | ~spl4_8 | spl4_29 | ~spl4_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f268,f105,f270,f117,f130])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    spl4_5 <=> v2_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.56  fof(f268,plain,(
% 0.21/0.56    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.56    inference(resolution,[],[f69,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    v2_funct_1(sK2) | ~spl4_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f105])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    ~spl4_10 | ~spl4_8 | spl4_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f254,f225,f117,f130])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_20),
% 0.21/0.56    inference(resolution,[],[f226,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ~v1_relat_1(k2_funct_1(sK2)) | spl4_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f225])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    ~spl4_10 | ~spl4_8 | spl4_18 | ~spl4_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f210,f105,f212,f117,f130])).
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.56    inference(resolution,[],[f68,f106])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    spl4_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    $false | spl4_12),
% 0.21/0.56    inference(resolution,[],[f150,f56])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_12),
% 0.21/0.56    inference(resolution,[],[f148,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | spl4_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl4_12 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    spl4_11 | ~spl4_12 | ~spl4_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f141,f121,f147,f144])).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    spl4_11 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_9),
% 0.21/0.57    inference(resolution,[],[f140,f122])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(superposition,[],[f62,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(resolution,[],[f58,f57])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ~spl4_6 | spl4_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    $false | (~spl4_6 | spl4_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f110,f134])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_10),
% 0.21/0.57    inference(resolution,[],[f78,f131])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl4_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f130])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ~spl4_10 | ~spl4_8 | spl4_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f128,f91,f117,f130])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.21/0.57    inference(resolution,[],[f67,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f91])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    spl4_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f55,f121])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    spl4_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f49,f117])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f18])).
% 0.21/0.57  fof(f18,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    spl4_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f51,f109])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f52,f105])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v2_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    spl4_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f53,f101])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f54,f97,f94,f91])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (32765)------------------------------
% 0.21/0.57  % (32765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32765)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (32765)Memory used [KB]: 11385
% 0.21/0.57  % (32765)Time elapsed: 0.144 s
% 0.21/0.57  % (32765)------------------------------
% 0.21/0.57  % (32765)------------------------------
% 0.21/0.57  % (32758)Success in time 0.205 s
%------------------------------------------------------------------------------
