%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 476 expanded)
%              Number of leaves         :   40 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  706 (1547 expanded)
%              Number of equality atoms :  126 ( 246 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f189,f247,f284,f300,f337,f342,f347,f358,f423,f428,f500,f510,f548,f558,f613,f819,f841])).

fof(f841,plain,
    ( ~ spl2_24
    | spl2_27
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl2_24
    | spl2_27
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f838,f234])).

fof(f234,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f121,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f121,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f74,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f838,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_24
    | spl2_27
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f557,f830])).

fof(f830,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_24
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f499,f608])).

fof(f608,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl2_31
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f499,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl2_24
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f557,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl2_27
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f819,plain,
    ( ~ spl2_6
    | ~ spl2_16
    | ~ spl2_17
    | spl2_27
    | ~ spl2_32 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_17
    | spl2_27
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f817,f234])).

fof(f817,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_17
    | spl2_27
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f816,f715])).

fof(f715,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f670,f682])).

fof(f682,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f681,f161])).

fof(f161,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f73,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f681,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f680,f126])).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f680,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f679,f612])).

fof(f612,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl2_32
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f679,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f646,f126])).

fof(f646,plain,
    ( sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f452,f612])).

fof(f452,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl2_17 ),
    inference(resolution,[],[f427,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f427,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl2_17
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f670,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_32 ),
    inference(trivial_inequality_removal,[],[f644])).

fof(f644,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f445,f612])).

fof(f445,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f444,f188])).

fof(f188,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f444,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f78,f422])).

fof(f422,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl2_16
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f816,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(k1_xboole_0)),k6_relat_1(k1_xboole_0))
    | ~ spl2_17
    | spl2_27
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f669,f682])).

fof(f669,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0))
    | spl2_27
    | ~ spl2_32 ),
    inference(backward_demodulation,[],[f557,f612])).

fof(f613,plain,
    ( spl2_31
    | spl2_32
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f314,f154,f144,f610,f606])).

fof(f144,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f154,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f314,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f309,f146])).

fof(f146,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f309,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f108,f156])).

fof(f156,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f558,plain,
    ( ~ spl2_27
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | spl2_12
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f544,f507,f355,f334,f281,f186,f154,f139,f555])).

fof(f139,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f281,plain,
    ( spl2_9
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f334,plain,
    ( spl2_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f355,plain,
    ( spl2_15
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f507,plain,
    ( spl2_26
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f544,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | spl2_12
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f336,f543])).

fof(f543,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f522,f302])).

fof(f302,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f188,f141,f283,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f283,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f281])).

fof(f141,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f522,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f141,f156,f357,f509,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f509,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f507])).

fof(f357,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f355])).

fof(f336,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f334])).

fof(f548,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | spl2_13
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | spl2_13
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f546,f234])).

fof(f546,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | spl2_13
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f341,f545])).

fof(f545,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f520,f383])).

fof(f383,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f301,f375])).

fof(f375,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f188,f246,f346,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f346,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl2_14
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f246,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f301,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f188,f141,f283,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f520,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f141,f357,f156,f509,f119])).

fof(f341,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl2_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f510,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f371,f154,f149,f144,f139,f507])).

fof(f149,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f371,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f359,f328])).

fof(f328,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f151,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f359,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f500,plain,
    ( spl2_24
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f252,f154,f497])).

fof(f252,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f156,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f428,plain,
    ( spl2_17
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f160,f154,f425])).

fof(f160,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f156,f98])).

fof(f423,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f375,f344,f244,f186,f420])).

fof(f358,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f330,f154,f149,f144,f139,f355])).

fof(f330,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f326,f328])).

fof(f326,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f347,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f290,f154,f149,f139,f344])).

fof(f290,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f141,f151,f156,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f342,plain,
    ( ~ spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(avatar_split_clause,[],[f332,f297,f154,f149,f144,f139,f339])).

fof(f297,plain,
    ( spl2_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f332,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(backward_demodulation,[],[f299,f328])).

fof(f299,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f297])).

fof(f337,plain,
    ( ~ spl2_12
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(avatar_split_clause,[],[f331,f293,f154,f149,f144,f139,f334])).

fof(f293,plain,
    ( spl2_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f331,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(backward_demodulation,[],[f295,f328])).

fof(f295,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f293])).

fof(f300,plain,
    ( ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f120,f297,f293])).

fof(f120,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f72,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f57])).

fof(f57,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f284,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f274,f154,f149,f139,f281])).

fof(f274,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f141,f151,f156,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f247,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f203,f154,f244])).

fof(f203,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f156,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f189,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f175,f154,f186])).

fof(f175,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f156,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f157,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f71,f154])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f152,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f70,f149])).

fof(f70,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f147,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f69,f144])).

fof(f69,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f68,f139])).

fof(f68,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (23288)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (23294)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (23304)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (23308)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (23302)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (23312)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (23310)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (23306)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (23295)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (23289)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (23290)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (23292)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23287)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (23296)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (23302)Refutation not found, incomplete strategy% (23302)------------------------------
% 0.21/0.53  % (23302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23302)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23302)Memory used [KB]: 10746
% 0.21/0.53  % (23302)Time elapsed: 0.126 s
% 0.21/0.53  % (23302)------------------------------
% 0.21/0.53  % (23302)------------------------------
% 0.21/0.53  % (23286)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (23291)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (23313)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (23303)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23314)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (23309)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (23315)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23301)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (23307)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (23305)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (23298)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (23293)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (23297)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (23299)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (23300)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (23306)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f842,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f189,f247,f284,f300,f337,f342,f347,f358,f423,f428,f500,f510,f548,f558,f613,f819,f841])).
% 0.21/0.57  fof(f841,plain,(
% 0.21/0.57    ~spl2_24 | spl2_27 | ~spl2_31),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f840])).
% 0.21/0.57  fof(f840,plain,(
% 0.21/0.57    $false | (~spl2_24 | spl2_27 | ~spl2_31)),
% 0.21/0.57    inference(subsumption_resolution,[],[f838,f234])).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f121,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.57    inference(condensation,[],[f118])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f76,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,axiom,(
% 0.21/0.57    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.57  fof(f838,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl2_24 | spl2_27 | ~spl2_31)),
% 0.21/0.57    inference(backward_demodulation,[],[f557,f830])).
% 0.21/0.57  fof(f830,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK1) | (~spl2_24 | ~spl2_31)),
% 0.21/0.57    inference(backward_demodulation,[],[f499,f608])).
% 0.21/0.57  fof(f608,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_31),
% 0.21/0.57    inference(avatar_component_clause,[],[f606])).
% 0.21/0.57  fof(f606,plain,(
% 0.21/0.57    spl2_31 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.57  fof(f499,plain,(
% 0.21/0.57    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl2_24),
% 0.21/0.57    inference(avatar_component_clause,[],[f497])).
% 0.21/0.57  fof(f497,plain,(
% 0.21/0.57    spl2_24 <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.57  fof(f557,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | spl2_27),
% 0.21/0.57    inference(avatar_component_clause,[],[f555])).
% 0.21/0.57  fof(f555,plain,(
% 0.21/0.57    spl2_27 <=> r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.57  fof(f819,plain,(
% 0.21/0.57    ~spl2_6 | ~spl2_16 | ~spl2_17 | spl2_27 | ~spl2_32),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f818])).
% 0.21/0.57  fof(f818,plain,(
% 0.21/0.57    $false | (~spl2_6 | ~spl2_16 | ~spl2_17 | spl2_27 | ~spl2_32)),
% 0.21/0.57    inference(subsumption_resolution,[],[f817,f234])).
% 0.21/0.57  fof(f817,plain,(
% 0.21/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) | (~spl2_6 | ~spl2_16 | ~spl2_17 | spl2_27 | ~spl2_32)),
% 0.21/0.57    inference(forward_demodulation,[],[f816,f715])).
% 0.21/0.57  fof(f715,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl2_6 | ~spl2_16 | ~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(backward_demodulation,[],[f670,f682])).
% 0.21/0.57  fof(f682,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | (~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(subsumption_resolution,[],[f681,f161])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f73,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.57  fof(f681,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | (~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(forward_demodulation,[],[f680,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.57    inference(flattening,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f680,plain,(
% 0.21/0.57    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | k1_xboole_0 = sK1 | (~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(forward_demodulation,[],[f679,f612])).
% 0.21/0.57  fof(f612,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | ~spl2_32),
% 0.21/0.57    inference(avatar_component_clause,[],[f610])).
% 0.21/0.57  fof(f610,plain,(
% 0.21/0.57    spl2_32 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.57  fof(f679,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | (~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(forward_demodulation,[],[f646,f126])).
% 0.21/0.57  fof(f646,plain,(
% 0.21/0.57    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | (~spl2_17 | ~spl2_32)),
% 0.21/0.57    inference(backward_demodulation,[],[f452,f612])).
% 0.21/0.57  fof(f452,plain,(
% 0.21/0.57    sK1 = k2_zfmisc_1(sK0,sK0) | ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | ~spl2_17),
% 0.21/0.57    inference(resolution,[],[f427,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f427,plain,(
% 0.21/0.57    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f425])).
% 0.21/0.57  fof(f425,plain,(
% 0.21/0.57    spl2_17 <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.57  fof(f670,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(sK1) | (~spl2_6 | ~spl2_16 | ~spl2_32)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f644])).
% 0.21/0.57  fof(f644,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | (~spl2_6 | ~spl2_16 | ~spl2_32)),
% 0.21/0.57    inference(backward_demodulation,[],[f445,f612])).
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = k1_relat_1(sK1) | (~spl2_6 | ~spl2_16)),
% 0.21/0.57    inference(subsumption_resolution,[],[f444,f188])).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    v1_relat_1(sK1) | ~spl2_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f186])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    spl2_6 <=> v1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.57  fof(f444,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl2_16),
% 0.21/0.57    inference(superposition,[],[f78,f422])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | ~spl2_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f420])).
% 0.21/0.57  fof(f420,plain,(
% 0.21/0.57    spl2_16 <=> sK0 = k2_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.57  fof(f816,plain,(
% 0.21/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(k1_xboole_0)),k6_relat_1(k1_xboole_0)) | (~spl2_17 | spl2_27 | ~spl2_32)),
% 0.21/0.57    inference(forward_demodulation,[],[f669,f682])).
% 0.21/0.57  fof(f669,plain,(
% 0.21/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0)) | (spl2_27 | ~spl2_32)),
% 0.21/0.57    inference(backward_demodulation,[],[f557,f612])).
% 0.21/0.57  fof(f613,plain,(
% 0.21/0.57    spl2_31 | spl2_32 | ~spl2_2 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f314,f154,f144,f610,f606])).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f309,f146])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f144])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 0.21/0.57    inference(resolution,[],[f108,f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f154])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    ~spl2_27 | ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9 | spl2_12 | ~spl2_15 | ~spl2_26),
% 0.21/0.57    inference(avatar_split_clause,[],[f544,f507,f355,f334,f281,f186,f154,f139,f555])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    spl2_1 <=> v1_funct_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    spl2_9 <=> v2_funct_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    spl2_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.57  fof(f355,plain,(
% 0.21/0.57    spl2_15 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.57  fof(f507,plain,(
% 0.21/0.57    spl2_26 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.57  fof(f544,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9 | spl2_12 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(backward_demodulation,[],[f336,f543])).
% 0.21/0.57  fof(f543,plain,(
% 0.21/0.57    k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(forward_demodulation,[],[f522,f302])).
% 0.21/0.57  fof(f302,plain,(
% 0.21/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | (~spl2_1 | ~spl2_6 | ~spl2_9)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f188,f141,f283,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.57  fof(f283,plain,(
% 0.21/0.57    v2_funct_1(sK1) | ~spl2_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f281])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    v1_funct_1(sK1) | ~spl2_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f139])).
% 0.21/0.57  fof(f522,plain,(
% 0.21/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f156,f357,f509,f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.57  fof(f509,plain,(
% 0.21/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_26),
% 0.21/0.57    inference(avatar_component_clause,[],[f507])).
% 0.21/0.57  fof(f357,plain,(
% 0.21/0.57    v1_funct_1(k2_funct_1(sK1)) | ~spl2_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f355])).
% 0.21/0.57  fof(f336,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f334])).
% 0.21/0.57  fof(f548,plain,(
% 0.21/0.57    ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | spl2_13 | ~spl2_14 | ~spl2_15 | ~spl2_26),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f547])).
% 0.21/0.57  fof(f547,plain,(
% 0.21/0.57    $false | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | spl2_13 | ~spl2_14 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(subsumption_resolution,[],[f546,f234])).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | spl2_13 | ~spl2_14 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(backward_demodulation,[],[f341,f545])).
% 0.21/0.57  fof(f545,plain,(
% 0.21/0.57    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_14 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(forward_demodulation,[],[f520,f383])).
% 0.21/0.57  fof(f383,plain,(
% 0.21/0.57    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_14)),
% 0.21/0.57    inference(backward_demodulation,[],[f301,f375])).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | (~spl2_6 | ~spl2_8 | ~spl2_14)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f188,f246,f346,f87])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.57  fof(f346,plain,(
% 0.21/0.57    v2_funct_2(sK1,sK0) | ~spl2_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f344])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    spl2_14 <=> v2_funct_2(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    v5_relat_1(sK1,sK0) | ~spl2_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f244])).
% 0.21/0.57  fof(f244,plain,(
% 0.21/0.57    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.57  fof(f301,plain,(
% 0.21/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | (~spl2_1 | ~spl2_6 | ~spl2_9)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f188,f141,f283,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f33])).
% 0.21/0.57  fof(f520,plain,(
% 0.21/0.57    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_15 | ~spl2_26)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f357,f156,f509,f119])).
% 0.21/0.57  fof(f341,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f339])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    spl2_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.57  fof(f510,plain,(
% 0.21/0.57    spl2_26 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f371,f154,f149,f144,f139,f507])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.57  fof(f371,plain,(
% 0.21/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(forward_demodulation,[],[f359,f328])).
% 0.21/0.57  fof(f328,plain,(
% 0.21/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    v3_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f149])).
% 0.21/0.57  fof(f359,plain,(
% 0.21/0.57    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f94])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.57  fof(f500,plain,(
% 0.21/0.57    spl2_24 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f252,f154,f497])).
% 0.21/0.57  fof(f252,plain,(
% 0.21/0.57    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f156,f104])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f428,plain,(
% 0.21/0.57    spl2_17 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f160,f154,f425])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f156,f98])).
% 0.21/0.57  fof(f423,plain,(
% 0.21/0.57    spl2_16 | ~spl2_6 | ~spl2_8 | ~spl2_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f375,f344,f244,f186,f420])).
% 0.21/0.57  fof(f358,plain,(
% 0.21/0.57    spl2_15 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f330,f154,f149,f144,f139,f355])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    v1_funct_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(backward_demodulation,[],[f326,f328])).
% 0.21/0.57  fof(f326,plain,(
% 0.21/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    spl2_14 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f290,f154,f149,f139,f344])).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    v2_funct_2(sK1,sK0) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f151,f156,f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    ~spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f332,f297,f154,f149,f144,f139,f339])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    spl2_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_11)),
% 0.21/0.57    inference(backward_demodulation,[],[f299,f328])).
% 0.21/0.57  fof(f299,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f297])).
% 0.21/0.57  fof(f337,plain,(
% 0.21/0.57    ~spl2_12 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f331,f293,f154,f149,f144,f139,f334])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    spl2_10 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_10)),
% 0.21/0.57    inference(backward_demodulation,[],[f295,f328])).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f293])).
% 0.21/0.57  fof(f300,plain,(
% 0.21/0.57    ~spl2_10 | ~spl2_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f120,f297,f293])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.21/0.57    inference(definition_unfolding,[],[f72,f74,f74])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f25])).
% 0.21/0.57  fof(f25,conjecture,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    spl2_9 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f274,f154,f149,f139,f281])).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    v2_funct_1(sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f141,f151,f156,f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    spl2_8 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f203,f154,f244])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    v5_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f156,f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    spl2_6 | ~spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f175,f154,f186])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f156,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    spl2_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f71,f154])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    spl2_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f70,f149])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f69,f144])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f68,f139])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (23306)------------------------------
% 0.21/0.57  % (23306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23306)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (23306)Memory used [KB]: 11257
% 0.21/0.57  % (23306)Time elapsed: 0.115 s
% 0.21/0.57  % (23306)------------------------------
% 0.21/0.57  % (23306)------------------------------
% 1.65/0.57  % (23285)Success in time 0.212 s
%------------------------------------------------------------------------------
