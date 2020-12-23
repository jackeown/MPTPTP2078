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
% DateTime   : Thu Dec  3 12:45:23 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 225 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :   23
%              Number of atoms          :  248 ( 819 expanded)
%              Number of equality atoms :   46 ( 145 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f161,f506])).

fof(f506,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f504,f81])).

fof(f81,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f504,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f502,f39])).

fof(f39,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
          & ~ r2_hidden(X2,sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f502,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f496,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f496,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f261,f40])).

fof(f40,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f261,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f258,f251])).

fof(f251,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k5_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k5_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f202,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f202,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
      | r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(backward_demodulation,[],[f101,f190])).

fof(f190,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f112,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f112,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f111,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f111,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f107,f47])).

fof(f107,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK0) ),
    inference(superposition,[],[f67,f97])).

fof(f97,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f94,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f93,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
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
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
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
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f90,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f101,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f64,f92])).

fof(f92,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f89,f61])).

fof(f89,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f37,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f258,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,sK0)
      | r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f203,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f203,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
      | r2_hidden(X4,k3_subset_1(sK0,sK1))
      | r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f102,f190])).

fof(f102,plain,(
    ! [X4] :
      ( r2_hidden(X4,k3_subset_1(sK0,sK1))
      | r2_hidden(X4,sK0)
      | ~ r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ) ),
    inference(superposition,[],[f65,f92])).

fof(f161,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f159,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f77,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f72,f79,f75])).

fof(f72,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f38,f51])).

fof(f38,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:15:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (15811)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (15828)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (15820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (15829)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (15821)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (15837)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (15816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (15819)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (15817)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (15812)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (15815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (15840)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.60  % (15822)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (15834)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.61  % (15826)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.61  % (15831)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.61  % (15836)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.61  % (15832)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  % (15823)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.61  % (15838)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.61  % (15827)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (15813)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.62  % (15818)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.62  % (15839)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.62  % (15814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.62  % (15835)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.98/0.63  % (15825)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.98/0.63  % (15833)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.98/0.63  % (15819)Refutation found. Thanks to Tanya!
% 1.98/0.63  % SZS status Theorem for theBenchmark
% 1.98/0.64  % (15833)Refutation not found, incomplete strategy% (15833)------------------------------
% 1.98/0.64  % (15833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (15833)Termination reason: Refutation not found, incomplete strategy
% 1.98/0.64  
% 1.98/0.64  % (15833)Memory used [KB]: 10746
% 1.98/0.64  % (15833)Time elapsed: 0.207 s
% 1.98/0.64  % (15833)------------------------------
% 1.98/0.64  % (15833)------------------------------
% 1.98/0.64  % (15824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.98/0.64  % (15830)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.98/0.65  % SZS output start Proof for theBenchmark
% 1.98/0.65  fof(f507,plain,(
% 1.98/0.65    $false),
% 1.98/0.65    inference(avatar_sat_refutation,[],[f82,f161,f506])).
% 1.98/0.65  fof(f506,plain,(
% 1.98/0.65    ~spl4_2),
% 1.98/0.65    inference(avatar_contradiction_clause,[],[f505])).
% 1.98/0.65  fof(f505,plain,(
% 1.98/0.65    $false | ~spl4_2),
% 1.98/0.65    inference(subsumption_resolution,[],[f504,f81])).
% 1.98/0.65  fof(f81,plain,(
% 1.98/0.65    r2_hidden(sK2,sK0) | ~spl4_2),
% 1.98/0.65    inference(avatar_component_clause,[],[f79])).
% 1.98/0.65  fof(f79,plain,(
% 1.98/0.65    spl4_2 <=> r2_hidden(sK2,sK0)),
% 1.98/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.98/0.65  fof(f504,plain,(
% 1.98/0.65    ~r2_hidden(sK2,sK0)),
% 1.98/0.65    inference(subsumption_resolution,[],[f502,f39])).
% 1.98/0.65  fof(f39,plain,(
% 1.98/0.65    ~r2_hidden(sK2,sK1)),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.65  fof(f29,plain,(
% 1.98/0.65    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.98/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f28,f27,f26])).
% 1.98/0.65  fof(f26,plain,(
% 1.98/0.65    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.98/0.65    introduced(choice_axiom,[])).
% 1.98/0.65  fof(f27,plain,(
% 1.98/0.65    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.98/0.65    introduced(choice_axiom,[])).
% 1.98/0.65  fof(f28,plain,(
% 1.98/0.65    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.98/0.65    introduced(choice_axiom,[])).
% 1.98/0.65  fof(f20,plain,(
% 1.98/0.65    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.98/0.65    inference(flattening,[],[f19])).
% 1.98/0.65  fof(f19,plain,(
% 1.98/0.65    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.98/0.65    inference(ennf_transformation,[],[f18])).
% 1.98/0.65  fof(f18,negated_conjecture,(
% 1.98/0.65    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.98/0.65    inference(negated_conjecture,[],[f17])).
% 1.98/0.65  fof(f17,conjecture,(
% 1.98/0.65    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 1.98/0.65  fof(f502,plain,(
% 1.98/0.65    r2_hidden(sK2,sK1) | ~r2_hidden(sK2,sK0)),
% 1.98/0.65    inference(resolution,[],[f496,f64])).
% 1.98/0.65  fof(f64,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f35])).
% 1.98/0.65  fof(f35,plain,(
% 1.98/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.98/0.65    inference(nnf_transformation,[],[f25])).
% 1.98/0.65  fof(f25,plain,(
% 1.98/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.98/0.65    inference(ennf_transformation,[],[f4])).
% 1.98/0.65  fof(f4,axiom,(
% 1.98/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.98/0.65  fof(f496,plain,(
% 1.98/0.65    ~r2_hidden(sK2,k5_xboole_0(sK0,sK1))),
% 1.98/0.65    inference(resolution,[],[f261,f40])).
% 1.98/0.65  fof(f40,plain,(
% 1.98/0.65    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.65  fof(f261,plain,(
% 1.98/0.65    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.98/0.65    inference(subsumption_resolution,[],[f258,f251])).
% 1.98/0.65  fof(f251,plain,(
% 1.98/0.65    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k5_xboole_0(sK0,sK1))) )),
% 1.98/0.65    inference(duplicate_literal_removal,[],[f249])).
% 1.98/0.65  fof(f249,plain,(
% 1.98/0.65    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k5_xboole_0(sK0,sK1))) )),
% 1.98/0.65    inference(resolution,[],[f202,f63])).
% 1.98/0.65  fof(f63,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f35])).
% 1.98/0.65  fof(f202,plain,(
% 1.98/0.65    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) | r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,sK0)) )),
% 1.98/0.65    inference(backward_demodulation,[],[f101,f190])).
% 1.98/0.65  fof(f190,plain,(
% 1.98/0.65    k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.98/0.65    inference(superposition,[],[f112,f61])).
% 1.98/0.65  fof(f61,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f10])).
% 1.98/0.65  fof(f10,axiom,(
% 1.98/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.98/0.65  fof(f112,plain,(
% 1.98/0.65    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.98/0.65    inference(forward_demodulation,[],[f111,f47])).
% 1.98/0.65  fof(f47,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f2])).
% 1.98/0.65  fof(f2,axiom,(
% 1.98/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.98/0.65  fof(f111,plain,(
% 1.98/0.65    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))),
% 1.98/0.65    inference(forward_demodulation,[],[f107,f47])).
% 1.98/0.65  fof(f107,plain,(
% 1.98/0.65    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK0)),
% 1.98/0.65    inference(superposition,[],[f67,f97])).
% 1.98/0.65  fof(f97,plain,(
% 1.98/0.65    sK0 = k2_xboole_0(sK1,sK0)),
% 1.98/0.65    inference(resolution,[],[f94,f55])).
% 1.98/0.65  fof(f55,plain,(
% 1.98/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.98/0.65    inference(cnf_transformation,[],[f23])).
% 1.98/0.65  fof(f23,plain,(
% 1.98/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.98/0.65    inference(ennf_transformation,[],[f6])).
% 1.98/0.65  fof(f6,axiom,(
% 1.98/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.98/0.65  fof(f94,plain,(
% 1.98/0.65    r1_tarski(sK1,sK0)),
% 1.98/0.65    inference(resolution,[],[f93,f71])).
% 1.98/0.65  fof(f71,plain,(
% 1.98/0.65    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.98/0.65    inference(equality_resolution,[],[f57])).
% 1.98/0.65  fof(f57,plain,(
% 1.98/0.65    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.98/0.65    inference(cnf_transformation,[],[f34])).
% 1.98/0.65  fof(f34,plain,(
% 1.98/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.98/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.98/0.65  fof(f33,plain,(
% 1.98/0.65    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.98/0.65    introduced(choice_axiom,[])).
% 1.98/0.65  fof(f32,plain,(
% 1.98/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.98/0.65    inference(rectify,[],[f31])).
% 1.98/0.65  fof(f31,plain,(
% 1.98/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.98/0.65    inference(nnf_transformation,[],[f13])).
% 1.98/0.65  fof(f13,axiom,(
% 1.98/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.98/0.65  fof(f93,plain,(
% 1.98/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.98/0.65    inference(subsumption_resolution,[],[f90,f41])).
% 1.98/0.65  fof(f41,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f16])).
% 1.98/0.65  fof(f16,axiom,(
% 1.98/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.98/0.65  fof(f90,plain,(
% 1.98/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.98/0.65    inference(resolution,[],[f37,f51])).
% 1.98/0.65  fof(f51,plain,(
% 1.98/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f30])).
% 1.98/0.65  fof(f30,plain,(
% 1.98/0.65    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.98/0.65    inference(nnf_transformation,[],[f22])).
% 1.98/0.65  fof(f22,plain,(
% 1.98/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f14])).
% 1.98/0.65  fof(f14,axiom,(
% 1.98/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.98/0.65  fof(f37,plain,(
% 1.98/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.65  fof(f67,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f46,f50,f50])).
% 1.98/0.65  fof(f50,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f12])).
% 1.98/0.65  fof(f12,axiom,(
% 1.98/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.98/0.65  fof(f46,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f1])).
% 1.98/0.65  fof(f1,axiom,(
% 1.98/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.98/0.65  fof(f101,plain,(
% 1.98/0.65    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | ~r2_hidden(X3,sK0)) )),
% 1.98/0.65    inference(superposition,[],[f64,f92])).
% 1.98/0.65  fof(f92,plain,(
% 1.98/0.65    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 1.98/0.65    inference(forward_demodulation,[],[f89,f61])).
% 1.98/0.65  fof(f89,plain,(
% 1.98/0.65    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))),
% 1.98/0.65    inference(resolution,[],[f37,f69])).
% 1.98/0.65  fof(f69,plain,(
% 1.98/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f56,f66])).
% 1.98/0.65  fof(f66,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f48,f50])).
% 1.98/0.65  fof(f48,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f5])).
% 1.98/0.65  fof(f5,axiom,(
% 1.98/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.98/0.65  fof(f56,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f24])).
% 1.98/0.65  fof(f24,plain,(
% 1.98/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.98/0.65    inference(ennf_transformation,[],[f15])).
% 1.98/0.65  fof(f15,axiom,(
% 1.98/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.98/0.65  fof(f258,plain,(
% 1.98/0.65    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,sK0) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.98/0.65    inference(duplicate_literal_removal,[],[f257])).
% 1.98/0.65  fof(f257,plain,(
% 1.98/0.65    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,sK0) | r2_hidden(X3,sK0) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.98/0.65    inference(resolution,[],[f203,f65])).
% 1.98/0.65  fof(f65,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f35])).
% 1.98/0.65  fof(f203,plain,(
% 1.98/0.65    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) | r2_hidden(X4,k3_subset_1(sK0,sK1)) | r2_hidden(X4,sK0)) )),
% 1.98/0.65    inference(backward_demodulation,[],[f102,f190])).
% 1.98/0.65  fof(f102,plain,(
% 1.98/0.65    ( ! [X4] : (r2_hidden(X4,k3_subset_1(sK0,sK1)) | r2_hidden(X4,sK0) | ~r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))) )),
% 1.98/0.65    inference(superposition,[],[f65,f92])).
% 1.98/0.65  fof(f161,plain,(
% 1.98/0.65    ~spl4_1),
% 1.98/0.65    inference(avatar_contradiction_clause,[],[f160])).
% 1.98/0.65  fof(f160,plain,(
% 1.98/0.65    $false | ~spl4_1),
% 1.98/0.65    inference(subsumption_resolution,[],[f159,f36])).
% 1.98/0.65  fof(f36,plain,(
% 1.98/0.65    k1_xboole_0 != sK0),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.65  fof(f159,plain,(
% 1.98/0.65    k1_xboole_0 = sK0 | ~spl4_1),
% 1.98/0.65    inference(resolution,[],[f77,f45])).
% 1.98/0.65  fof(f45,plain,(
% 1.98/0.65    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.98/0.65    inference(cnf_transformation,[],[f21])).
% 1.98/0.65  fof(f21,plain,(
% 1.98/0.65    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.98/0.65    inference(ennf_transformation,[],[f3])).
% 1.98/0.65  fof(f3,axiom,(
% 1.98/0.65    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.98/0.65  fof(f77,plain,(
% 1.98/0.65    v1_xboole_0(sK0) | ~spl4_1),
% 1.98/0.65    inference(avatar_component_clause,[],[f75])).
% 1.98/0.65  fof(f75,plain,(
% 1.98/0.65    spl4_1 <=> v1_xboole_0(sK0)),
% 1.98/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.98/0.65  fof(f82,plain,(
% 1.98/0.65    spl4_1 | spl4_2),
% 1.98/0.65    inference(avatar_split_clause,[],[f72,f79,f75])).
% 1.98/0.65  fof(f72,plain,(
% 1.98/0.65    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.98/0.65    inference(resolution,[],[f38,f51])).
% 1.98/0.65  fof(f38,plain,(
% 1.98/0.65    m1_subset_1(sK2,sK0)),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.65  % SZS output end Proof for theBenchmark
% 1.98/0.65  % (15819)------------------------------
% 1.98/0.65  % (15819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.65  % (15819)Termination reason: Refutation
% 1.98/0.65  
% 1.98/0.65  % (15819)Memory used [KB]: 10874
% 1.98/0.65  % (15819)Time elapsed: 0.193 s
% 1.98/0.65  % (15819)------------------------------
% 1.98/0.65  % (15819)------------------------------
% 1.98/0.65  % (15810)Success in time 0.286 s
%------------------------------------------------------------------------------
