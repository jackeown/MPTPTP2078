%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:50 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 276 expanded)
%              Number of leaves         :   36 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 ( 458 expanded)
%              Number of equality atoms :   89 ( 195 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f92,f100,f106,f117,f137,f150,f165,f218,f387,f550,f1034,f1112,f1114])).

fof(f1114,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1112,plain,
    ( spl3_49
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f1111,f1031,f1093])).

fof(f1093,plain,
    ( spl3_49
  <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1031,plain,
    ( spl3_43
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1111,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f1087,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1087,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_43 ),
    inference(superposition,[],[f743,f1033])).

fof(f1033,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f743,plain,(
    ! [X2,X3] : k3_tarski(k1_enumset1(X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f271,f190])).

fof(f190,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f60,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f271,plain,(
    ! [X2,X3] : k3_tarski(k1_enumset1(X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f59,f43])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f1034,plain,
    ( spl3_43
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f1029,f370,f1031])).

fof(f370,plain,
    ( spl3_24
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1029,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1014,f500])).

fof(f500,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f182,f442])).

fof(f442,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f436,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f66,f108])).

fof(f108,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f93,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(global_subsumption,[],[f33,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f436,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(X3,X3) ),
    inference(superposition,[],[f63,f418])).

fof(f418,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f410,f36])).

fof(f410,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f190,f132])).

fof(f182,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f61])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1014,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f190,f372])).

fof(f372,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f370])).

fof(f550,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f545,f215,f76,f547])).

fof(f547,plain,
    ( spl3_31
  <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f76,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f215,plain,
    ( spl3_17
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f545,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f544,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f544,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,sK0))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f535,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f59,f59])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f535,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f286,f217])).

fof(f217,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f286,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f387,plain,
    ( spl3_24
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f364,f134,f370])).

fof(f134,plain,
    ( spl3_10
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f364,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(superposition,[],[f63,f136])).

fof(f136,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f218,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f202,f147,f114,f215])).

fof(f114,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f147,plain,
    ( spl3_11
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f116,f149])).

fof(f149,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f116,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f165,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f87,f33])).

fof(f87,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f150,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f142,f76,f147])).

fof(f142,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f52,f78])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f137,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f131,f97,f134])).

fof(f97,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f66,f99])).

fof(f99,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f117,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f111,f76,f114])).

fof(f111,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f51,f78])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f106,plain,
    ( ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f101,f71,f103])).

fof(f103,plain,
    ( spl3_6
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f71,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f73,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f73,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f100,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f89,f97])).

fof(f89,plain,
    ( spl3_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f68])).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f76,f89,f85])).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f78])).

fof(f79,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f74,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:49:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31237)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (31256)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (31241)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (31245)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (31256)Refutation not found, incomplete strategy% (31256)------------------------------
% 0.21/0.54  % (31256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31256)Memory used [KB]: 10746
% 0.21/0.54  % (31256)Time elapsed: 0.124 s
% 0.21/0.54  % (31256)------------------------------
% 0.21/0.54  % (31256)------------------------------
% 0.21/0.54  % (31255)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (31239)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (31238)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (31240)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (31260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (31264)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (31242)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (31263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (31236)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (31265)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (31261)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (31262)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (31254)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (31249)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (31250)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (31257)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (31252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (31247)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (31253)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (31253)Refutation not found, incomplete strategy% (31253)------------------------------
% 0.21/0.56  % (31253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31244)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (31246)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (31258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (31248)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (31258)Refutation not found, incomplete strategy% (31258)------------------------------
% 0.21/0.56  % (31258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (31253)Memory used [KB]: 10618
% 0.21/0.56  % (31253)Time elapsed: 0.150 s
% 0.21/0.56  % (31258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (31258)Memory used [KB]: 10746
% 0.21/0.56  % (31258)Time elapsed: 0.149 s
% 0.21/0.56  % (31258)------------------------------
% 0.21/0.56  % (31258)------------------------------
% 0.21/0.56  % (31253)------------------------------
% 0.21/0.56  % (31253)------------------------------
% 1.58/0.58  % (31259)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.58  % (31251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.74/0.59  % (31251)Refutation not found, incomplete strategy% (31251)------------------------------
% 1.74/0.59  % (31251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.59  % (31251)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.59  
% 1.74/0.59  % (31251)Memory used [KB]: 6140
% 1.74/0.59  % (31251)Time elapsed: 0.005 s
% 1.74/0.59  % (31251)------------------------------
% 1.74/0.59  % (31251)------------------------------
% 1.74/0.59  % (31243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.13/0.65  % (31252)Refutation found. Thanks to Tanya!
% 2.13/0.65  % SZS status Theorem for theBenchmark
% 2.13/0.65  % SZS output start Proof for theBenchmark
% 2.13/0.65  fof(f1115,plain,(
% 2.13/0.65    $false),
% 2.13/0.65    inference(avatar_sat_refutation,[],[f74,f79,f92,f100,f106,f117,f137,f150,f165,f218,f387,f550,f1034,f1112,f1114])).
% 2.13/0.65  fof(f1114,plain,(
% 2.13/0.65    k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) | k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.13/0.65    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.65  fof(f1112,plain,(
% 2.13/0.65    spl3_49 | ~spl3_43),
% 2.13/0.65    inference(avatar_split_clause,[],[f1111,f1031,f1093])).
% 2.13/0.65  fof(f1093,plain,(
% 2.13/0.65    spl3_49 <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.13/0.65  fof(f1031,plain,(
% 2.13/0.65    spl3_43 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 2.13/0.65  fof(f1111,plain,(
% 2.13/0.65    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_43),
% 2.13/0.65    inference(forward_demodulation,[],[f1087,f36])).
% 2.13/0.65  fof(f36,plain,(
% 2.13/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.65    inference(cnf_transformation,[],[f7])).
% 2.13/0.65  fof(f7,axiom,(
% 2.13/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.13/0.65  fof(f1087,plain,(
% 2.13/0.65    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | ~spl3_43),
% 2.13/0.65    inference(superposition,[],[f743,f1033])).
% 2.13/0.65  fof(f1033,plain,(
% 2.13/0.65    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_43),
% 2.13/0.65    inference(avatar_component_clause,[],[f1031])).
% 2.13/0.65  fof(f743,plain,(
% 2.13/0.65    ( ! [X2,X3] : (k3_tarski(k1_enumset1(X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.13/0.65    inference(forward_demodulation,[],[f271,f190])).
% 2.13/0.65  fof(f190,plain,(
% 2.13/0.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 2.13/0.65    inference(superposition,[],[f60,f63])).
% 2.13/0.65  fof(f63,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f39,f43,f43])).
% 2.13/0.65  fof(f43,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f6])).
% 2.13/0.65  fof(f6,axiom,(
% 2.13/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.13/0.65  fof(f39,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f1])).
% 2.13/0.65  fof(f1,axiom,(
% 2.13/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.13/0.65  fof(f60,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f42,f43])).
% 2.13/0.65  fof(f42,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f3])).
% 2.13/0.65  fof(f3,axiom,(
% 2.13/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.13/0.65  fof(f271,plain,(
% 2.13/0.65    ( ! [X2,X3] : (k3_tarski(k1_enumset1(X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 2.13/0.65    inference(superposition,[],[f65,f57])).
% 2.13/0.65  fof(f57,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f8])).
% 2.13/0.65  fof(f8,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.13/0.65  fof(f65,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f45,f59,f43])).
% 2.13/0.65  fof(f59,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f41,f40])).
% 2.13/0.65  fof(f40,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f11])).
% 2.13/0.65  fof(f11,axiom,(
% 2.13/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.13/0.65  fof(f41,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f13])).
% 2.13/0.65  fof(f13,axiom,(
% 2.13/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.13/0.65  fof(f45,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f9])).
% 2.13/0.65  fof(f9,axiom,(
% 2.13/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.13/0.65  fof(f1034,plain,(
% 2.13/0.65    spl3_43 | ~spl3_24),
% 2.13/0.65    inference(avatar_split_clause,[],[f1029,f370,f1031])).
% 2.13/0.65  fof(f370,plain,(
% 2.13/0.65    spl3_24 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.13/0.65  fof(f1029,plain,(
% 2.13/0.65    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_24),
% 2.13/0.65    inference(forward_demodulation,[],[f1014,f500])).
% 2.13/0.65  fof(f500,plain,(
% 2.13/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.13/0.65    inference(backward_demodulation,[],[f182,f442])).
% 2.13/0.65  fof(f442,plain,(
% 2.13/0.65    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f436,f132])).
% 2.13/0.65  fof(f132,plain,(
% 2.13/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 2.13/0.65    inference(resolution,[],[f66,f108])).
% 2.13/0.65  fof(f108,plain,(
% 2.13/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.13/0.65    inference(resolution,[],[f93,f68])).
% 2.13/0.65  fof(f68,plain,(
% 2.13/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.13/0.65    inference(equality_resolution,[],[f54])).
% 2.13/0.65  fof(f54,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.13/0.65    inference(cnf_transformation,[],[f12])).
% 2.13/0.65  fof(f12,axiom,(
% 2.13/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.13/0.65  fof(f93,plain,(
% 2.13/0.65    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(global_subsumption,[],[f33,f83])).
% 2.13/0.65  fof(f83,plain,(
% 2.13/0.65    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(resolution,[],[f49,f35])).
% 2.13/0.65  fof(f35,plain,(
% 2.13/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f20])).
% 2.13/0.65  fof(f20,axiom,(
% 2.13/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.13/0.65  fof(f49,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f25])).
% 2.13/0.65  fof(f25,plain,(
% 2.13/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f14])).
% 2.13/0.65  fof(f14,axiom,(
% 2.13/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.13/0.65  fof(f33,plain,(
% 2.13/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f18])).
% 2.13/0.65  fof(f18,axiom,(
% 2.13/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.13/0.65  fof(f66,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.13/0.65    inference(definition_unfolding,[],[f50,f43])).
% 2.13/0.65  fof(f50,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.13/0.65    inference(cnf_transformation,[],[f26])).
% 2.13/0.65  fof(f26,plain,(
% 2.13/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.13/0.65    inference(ennf_transformation,[],[f4])).
% 2.13/0.65  fof(f4,axiom,(
% 2.13/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.13/0.65  fof(f436,plain,(
% 2.13/0.65    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(X3,X3)) )),
% 2.13/0.65    inference(superposition,[],[f63,f418])).
% 2.13/0.65  fof(f418,plain,(
% 2.13/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.65    inference(forward_demodulation,[],[f410,f36])).
% 2.13/0.65  fof(f410,plain,(
% 2.13/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.13/0.65    inference(superposition,[],[f190,f132])).
% 2.13/0.65  fof(f182,plain,(
% 2.13/0.65    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.13/0.65    inference(superposition,[],[f60,f61])).
% 2.13/0.65  fof(f61,plain,(
% 2.13/0.65    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.13/0.65    inference(definition_unfolding,[],[f37,f43])).
% 2.13/0.65  fof(f37,plain,(
% 2.13/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.13/0.65    inference(cnf_transformation,[],[f23])).
% 2.13/0.65  fof(f23,plain,(
% 2.13/0.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.13/0.65    inference(rectify,[],[f2])).
% 2.13/0.65  fof(f2,axiom,(
% 2.13/0.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.13/0.65  fof(f1014,plain,(
% 2.13/0.65    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) | ~spl3_24),
% 2.13/0.65    inference(superposition,[],[f190,f372])).
% 2.13/0.65  fof(f372,plain,(
% 2.13/0.65    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_24),
% 2.13/0.65    inference(avatar_component_clause,[],[f370])).
% 2.13/0.65  fof(f550,plain,(
% 2.13/0.65    spl3_31 | ~spl3_2 | ~spl3_17),
% 2.13/0.65    inference(avatar_split_clause,[],[f545,f215,f76,f547])).
% 2.13/0.65  fof(f547,plain,(
% 2.13/0.65    spl3_31 <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.13/0.65  fof(f76,plain,(
% 2.13/0.65    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.13/0.65  fof(f215,plain,(
% 2.13/0.65    spl3_17 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.13/0.65  fof(f545,plain,(
% 2.13/0.65    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | (~spl3_2 | ~spl3_17)),
% 2.13/0.65    inference(forward_demodulation,[],[f544,f62])).
% 2.13/0.65  fof(f62,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.13/0.65    inference(definition_unfolding,[],[f38,f40,f40])).
% 2.13/0.65  fof(f38,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f10])).
% 2.13/0.65  fof(f10,axiom,(
% 2.13/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.13/0.65  fof(f544,plain,(
% 2.13/0.65    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) | (~spl3_2 | ~spl3_17)),
% 2.13/0.65    inference(forward_demodulation,[],[f535,f64])).
% 2.13/0.65  fof(f64,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f44,f59,f59])).
% 2.13/0.65  fof(f44,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f5])).
% 2.13/0.65  fof(f5,axiom,(
% 2.13/0.65    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.13/0.65  fof(f535,plain,(
% 2.13/0.65    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | (~spl3_2 | ~spl3_17)),
% 2.13/0.65    inference(resolution,[],[f286,f217])).
% 2.13/0.65  fof(f217,plain,(
% 2.13/0.65    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_17),
% 2.13/0.65    inference(avatar_component_clause,[],[f215])).
% 2.13/0.65  fof(f286,plain,(
% 2.13/0.65    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5))) ) | ~spl3_2),
% 2.13/0.65    inference(resolution,[],[f67,f78])).
% 2.13/0.65  fof(f78,plain,(
% 2.13/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 2.13/0.65    inference(avatar_component_clause,[],[f76])).
% 2.13/0.65  fof(f67,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f58,f59])).
% 2.13/0.65  fof(f58,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f30])).
% 2.13/0.65  fof(f30,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(flattening,[],[f29])).
% 2.13/0.65  fof(f29,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f19])).
% 2.13/0.65  fof(f19,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.13/0.65  fof(f387,plain,(
% 2.13/0.65    spl3_24 | ~spl3_10),
% 2.13/0.65    inference(avatar_split_clause,[],[f364,f134,f370])).
% 2.13/0.65  fof(f134,plain,(
% 2.13/0.65    spl3_10 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.13/0.65  fof(f364,plain,(
% 2.13/0.65    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_10),
% 2.13/0.65    inference(superposition,[],[f63,f136])).
% 2.13/0.65  fof(f136,plain,(
% 2.13/0.65    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl3_10),
% 2.13/0.65    inference(avatar_component_clause,[],[f134])).
% 2.13/0.65  fof(f218,plain,(
% 2.13/0.65    spl3_17 | ~spl3_7 | ~spl3_11),
% 2.13/0.65    inference(avatar_split_clause,[],[f202,f147,f114,f215])).
% 2.13/0.65  fof(f114,plain,(
% 2.13/0.65    spl3_7 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.13/0.65  fof(f147,plain,(
% 2.13/0.65    spl3_11 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.13/0.65  fof(f202,plain,(
% 2.13/0.65    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_7 | ~spl3_11)),
% 2.13/0.65    inference(backward_demodulation,[],[f116,f149])).
% 2.13/0.65  fof(f149,plain,(
% 2.13/0.65    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 2.13/0.65    inference(avatar_component_clause,[],[f147])).
% 2.13/0.65  fof(f116,plain,(
% 2.13/0.65    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 2.13/0.65    inference(avatar_component_clause,[],[f114])).
% 2.13/0.65  fof(f165,plain,(
% 2.13/0.65    ~spl3_3),
% 2.13/0.65    inference(avatar_contradiction_clause,[],[f163])).
% 2.13/0.65  fof(f163,plain,(
% 2.13/0.65    $false | ~spl3_3),
% 2.13/0.65    inference(resolution,[],[f87,f33])).
% 2.13/0.65  fof(f87,plain,(
% 2.13/0.65    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 2.13/0.65    inference(avatar_component_clause,[],[f85])).
% 2.13/0.65  fof(f85,plain,(
% 2.13/0.65    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.13/0.65  fof(f150,plain,(
% 2.13/0.65    spl3_11 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f142,f76,f147])).
% 2.13/0.65  fof(f142,plain,(
% 2.13/0.65    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 2.13/0.65    inference(resolution,[],[f52,f78])).
% 2.13/0.65  fof(f52,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f28])).
% 2.13/0.65  fof(f28,plain,(
% 2.13/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f16])).
% 2.13/0.65  fof(f16,axiom,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.13/0.65  fof(f137,plain,(
% 2.13/0.65    spl3_10 | ~spl3_5),
% 2.13/0.65    inference(avatar_split_clause,[],[f131,f97,f134])).
% 2.13/0.65  fof(f97,plain,(
% 2.13/0.65    spl3_5 <=> r1_tarski(sK1,sK0)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.13/0.65  fof(f131,plain,(
% 2.13/0.65    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl3_5),
% 2.13/0.65    inference(resolution,[],[f66,f99])).
% 2.13/0.65  fof(f99,plain,(
% 2.13/0.65    r1_tarski(sK1,sK0) | ~spl3_5),
% 2.13/0.65    inference(avatar_component_clause,[],[f97])).
% 2.13/0.65  fof(f117,plain,(
% 2.13/0.65    spl3_7 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f111,f76,f114])).
% 2.13/0.65  fof(f111,plain,(
% 2.13/0.65    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_2),
% 2.13/0.65    inference(resolution,[],[f51,f78])).
% 2.13/0.65  fof(f51,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f27])).
% 2.13/0.65  fof(f27,plain,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f17])).
% 2.13/0.65  fof(f17,axiom,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.13/0.65  fof(f106,plain,(
% 2.13/0.65    ~spl3_6 | spl3_1),
% 2.13/0.65    inference(avatar_split_clause,[],[f101,f71,f103])).
% 2.13/0.65  fof(f103,plain,(
% 2.13/0.65    spl3_6 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.13/0.65  fof(f71,plain,(
% 2.13/0.65    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.13/0.65  fof(f101,plain,(
% 2.13/0.65    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 2.13/0.65    inference(forward_demodulation,[],[f73,f34])).
% 2.13/0.65  fof(f34,plain,(
% 2.13/0.65    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.13/0.65    inference(cnf_transformation,[],[f15])).
% 2.13/0.65  fof(f15,axiom,(
% 2.13/0.65    ! [X0] : k2_subset_1(X0) = X0),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.13/0.65  fof(f73,plain,(
% 2.13/0.65    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 2.13/0.65    inference(avatar_component_clause,[],[f71])).
% 2.13/0.65  fof(f100,plain,(
% 2.13/0.65    spl3_5 | ~spl3_4),
% 2.13/0.65    inference(avatar_split_clause,[],[f94,f89,f97])).
% 2.13/0.65  fof(f89,plain,(
% 2.13/0.65    spl3_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.13/0.65  fof(f94,plain,(
% 2.13/0.65    r1_tarski(sK1,sK0) | ~spl3_4),
% 2.13/0.65    inference(resolution,[],[f91,f68])).
% 2.13/0.65  fof(f91,plain,(
% 2.13/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 2.13/0.65    inference(avatar_component_clause,[],[f89])).
% 2.13/0.65  fof(f92,plain,(
% 2.13/0.65    spl3_3 | spl3_4 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f82,f76,f89,f85])).
% 2.13/0.65  fof(f82,plain,(
% 2.13/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 2.13/0.65    inference(resolution,[],[f49,f78])).
% 2.13/0.65  fof(f79,plain,(
% 2.13/0.65    spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f31,f76])).
% 2.13/0.65  fof(f31,plain,(
% 2.13/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.13/0.65    inference(cnf_transformation,[],[f24])).
% 2.13/0.65  fof(f24,plain,(
% 2.13/0.65    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f22])).
% 2.13/0.65  fof(f22,negated_conjecture,(
% 2.13/0.65    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.13/0.65    inference(negated_conjecture,[],[f21])).
% 2.13/0.65  fof(f21,conjecture,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.13/0.65  fof(f74,plain,(
% 2.13/0.65    ~spl3_1),
% 2.13/0.65    inference(avatar_split_clause,[],[f32,f71])).
% 2.13/0.65  fof(f32,plain,(
% 2.13/0.65    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.13/0.65    inference(cnf_transformation,[],[f24])).
% 2.13/0.65  % SZS output end Proof for theBenchmark
% 2.13/0.65  % (31252)------------------------------
% 2.13/0.65  % (31252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (31252)Termination reason: Refutation
% 2.13/0.65  
% 2.13/0.65  % (31252)Memory used [KB]: 11513
% 2.13/0.65  % (31252)Time elapsed: 0.238 s
% 2.13/0.65  % (31252)------------------------------
% 2.13/0.65  % (31252)------------------------------
% 2.13/0.65  % (31235)Success in time 0.281 s
%------------------------------------------------------------------------------
