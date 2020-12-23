%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 163 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  238 ( 402 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3707)Termination reason: Refutation not found, incomplete strategy

% (3707)Memory used [KB]: 6140
% (3707)Time elapsed: 0.004 s
% (3707)------------------------------
% (3707)------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f193,f228,f234,f248])).

fof(f248,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f243,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f243,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f217,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f217,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X4))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X4)) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_3
  <=> ! [X4] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X4))
        | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f234,plain,
    ( spl4_3
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f233,f219,f179,f216])).

fof(f179,plain,
    ( spl4_2
  <=> ! [X0] :
        ( sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f219,plain,
    ( spl4_4
  <=> sK1 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f230,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f230,plain,
    ( ! [X0] :
        ( sK1 = k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2))
        | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f55,f220])).

fof(f220,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f219])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f228,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f226,f31])).

fof(f226,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f225,f76])).

fof(f76,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f67,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f4,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f225,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl4_4 ),
    inference(superposition,[],[f221,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X0,X1))) = X0
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f52,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f221,plain,
    ( sK1 != k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f219])).

fof(f193,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f191,f56])).

fof(f191,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f185,f31])).

fof(f185,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ sP0(sK1,k1_zfmisc_1(sK1))
    | spl4_1 ),
    inference(resolution,[],[f177,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(superposition,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f177,plain,
    ( ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_1
  <=> m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f183,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f182,f179,f175])).

fof(f182,plain,(
    ! [X0] :
      ( sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2))
      | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f31])).

fof(f134,plain,(
    ! [X0] :
      ( sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2))
      | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f57,f107])).

fof(f107,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_subset_1(X8,X6,X7) = k4_subset_1(X9,X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f55,f55])).

fof(f57,plain,(
    sK1 != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f32,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (3696)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (3720)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.49  % (3711)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (3706)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (3720)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (3707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (3715)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (3707)Refutation not found, incomplete strategy% (3707)------------------------------
% 0.21/0.52  % (3707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (3707)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3707)Memory used [KB]: 6140
% 0.21/0.52  % (3707)Time elapsed: 0.004 s
% 0.21/0.52  % (3707)------------------------------
% 0.21/0.52  % (3707)------------------------------
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f183,f193,f228,f234,f248])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    $false | ~spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f243,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl4_3),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f237])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f217,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ( ! [X4] : (~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X4)) | ~m1_subset_1(sK2,k1_zfmisc_1(X4))) ) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl4_3 <=> ! [X4] : (~m1_subset_1(sK2,k1_zfmisc_1(X4)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    spl4_3 | ~spl4_2 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f233,f219,f179,f216])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl4_2 <=> ! [X0] : (sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    spl4_4 <=> sK1 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | (~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f230,f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0))) ) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f179])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 = k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl4_4),
% 0.21/0.52    inference(superposition,[],[f55,f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    sK1 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2))) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f219])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f51,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    spl4_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    $false | spl4_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f226,f31])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl4_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f225,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    r1_tarski(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f75,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f38,f31])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f45,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 0.21/0.52    inference(definition_folding,[],[f4,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl4_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    sK1 != sK1 | ~r1_tarski(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl4_4),
% 0.21/0.52    inference(superposition,[],[f221,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X0,X1))) = X0 | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f53,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f44,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f52,f37])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    sK1 != k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2))) | spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f219])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    $false | spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f191,f56])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ~sP0(sK1,k1_zfmisc_1(sK1)) | spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f31])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~sP0(sK1,k1_zfmisc_1(sK1)) | spl4_1),
% 0.21/0.52    inference(resolution,[],[f177,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_subset_1(X0,X2),X1) | ~m1_subset_1(X2,X1) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f43,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    spl4_1 <=> m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~spl4_1 | spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f182,f179,f175])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f134,f31])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0] : (sK1 != k4_subset_1(X0,sK2,k3_subset_1(sK1,sK2)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f57,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (k4_subset_1(X8,X6,X7) = k4_subset_1(X9,X6,X7) | ~m1_subset_1(X7,k1_zfmisc_1(X9)) | ~m1_subset_1(X6,k1_zfmisc_1(X9)) | ~m1_subset_1(X7,k1_zfmisc_1(X8)) | ~m1_subset_1(X6,k1_zfmisc_1(X8))) )),
% 0.21/0.52    inference(superposition,[],[f55,f55])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    sK1 != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f32,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3720)------------------------------
% 0.21/0.52  % (3720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3720)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3720)Memory used [KB]: 6268
% 0.21/0.52  % (3720)Time elapsed: 0.109 s
% 0.21/0.52  % (3720)------------------------------
% 0.21/0.52  % (3720)------------------------------
% 0.21/0.52  % (3698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3691)Success in time 0.156 s
%------------------------------------------------------------------------------
