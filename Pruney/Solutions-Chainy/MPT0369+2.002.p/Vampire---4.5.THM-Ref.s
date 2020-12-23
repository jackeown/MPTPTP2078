%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:23 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
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
fof(f789,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f157,f788])).

fof(f788,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f787])).

fof(f787,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f786,f79])).

fof(f79,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f786,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f784,f38])).

fof(f38,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK0,sK1))
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,sK0) )
   => ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f784,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f761,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f761,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f758,f39])).

fof(f39,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f758,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f755,f240])).

fof(f240,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k5_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k5_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f198,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f198,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
      | r2_hidden(X3,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(backward_demodulation,[],[f99,f186])).

fof(f186,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f110,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f110,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f109,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f109,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f105,f45])).

fof(f105,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK0) ),
    inference(superposition,[],[f65,f95])).

fof(f95,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f92,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f91,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f91,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f88,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f62,f90])).

fof(f90,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f87,f59])).

fof(f87,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f36,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f755,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f754])).

fof(f754,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_subset_1(sK0,sK1))
      | r2_hidden(X3,sK0)
      | r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k5_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f199,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f199,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))
      | r2_hidden(X4,k3_subset_1(sK0,sK1))
      | r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f100,f186])).

fof(f100,plain,(
    ! [X4] :
      ( r2_hidden(X4,k3_subset_1(sK0,sK1))
      | r2_hidden(X4,sK0)
      | ~ r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ) ),
    inference(superposition,[],[f63,f90])).

fof(f157,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f155,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f75,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f70,f77,f73])).

fof(f70,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f37,f49])).

fof(f37,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (8834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (8833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (8815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (8820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (8823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (8817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (8814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (8840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (8819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (8828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (8822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (8832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (8842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (8821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (8843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (8839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (8818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (8836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (8831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (8841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (8826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (8835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (8831)Refutation not found, incomplete strategy% (8831)------------------------------
% 0.21/0.54  % (8831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (8816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (8836)Refutation not found, incomplete strategy% (8836)------------------------------
% 1.29/0.55  % (8836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (8836)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (8836)Memory used [KB]: 10746
% 1.29/0.55  % (8836)Time elapsed: 0.142 s
% 1.29/0.55  % (8836)------------------------------
% 1.29/0.55  % (8836)------------------------------
% 1.29/0.55  % (8831)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (8831)Memory used [KB]: 10618
% 1.29/0.55  % (8831)Time elapsed: 0.132 s
% 1.29/0.55  % (8831)------------------------------
% 1.29/0.55  % (8831)------------------------------
% 1.29/0.55  % (8822)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.56  % SZS output start Proof for theBenchmark
% 1.29/0.56  fof(f789,plain,(
% 1.29/0.56    $false),
% 1.29/0.56    inference(avatar_sat_refutation,[],[f80,f157,f788])).
% 1.29/0.56  fof(f788,plain,(
% 1.29/0.56    ~spl4_2),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f787])).
% 1.29/0.56  fof(f787,plain,(
% 1.29/0.56    $false | ~spl4_2),
% 1.29/0.56    inference(subsumption_resolution,[],[f786,f79])).
% 1.29/0.56  fof(f79,plain,(
% 1.29/0.56    r2_hidden(sK2,sK0) | ~spl4_2),
% 1.29/0.56    inference(avatar_component_clause,[],[f77])).
% 1.29/0.56  fof(f77,plain,(
% 1.29/0.56    spl4_2 <=> r2_hidden(sK2,sK0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.29/0.56  fof(f786,plain,(
% 1.29/0.56    ~r2_hidden(sK2,sK0)),
% 1.29/0.56    inference(subsumption_resolution,[],[f784,f38])).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ~r2_hidden(sK2,sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f27,f26,f25])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,sK0)) => (~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f19,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.29/0.56    inference(flattening,[],[f18])).
% 1.29/0.56  fof(f18,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.29/0.56    inference(ennf_transformation,[],[f17])).
% 1.29/0.56  fof(f17,negated_conjecture,(
% 1.29/0.56    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.29/0.56    inference(negated_conjecture,[],[f16])).
% 1.29/0.56  fof(f16,conjecture,(
% 1.29/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 1.29/0.56  fof(f784,plain,(
% 1.29/0.56    r2_hidden(sK2,sK1) | ~r2_hidden(sK2,sK0)),
% 1.29/0.56    inference(resolution,[],[f761,f62])).
% 1.29/0.56  fof(f62,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.29/0.56    inference(nnf_transformation,[],[f24])).
% 1.29/0.56  fof(f24,plain,(
% 1.29/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.29/0.56    inference(ennf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.29/0.56  fof(f761,plain,(
% 1.29/0.56    ~r2_hidden(sK2,k5_xboole_0(sK0,sK1))),
% 1.29/0.56    inference(resolution,[],[f758,f39])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f758,plain,(
% 1.29/0.56    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f755,f240])).
% 1.29/0.56  fof(f240,plain,(
% 1.29/0.56    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k5_xboole_0(sK0,sK1))) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f238])).
% 1.29/0.56  fof(f238,plain,(
% 1.29/0.56    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k5_xboole_0(sK0,sK1))) )),
% 1.29/0.56    inference(resolution,[],[f198,f61])).
% 1.29/0.56  fof(f61,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f34])).
% 1.29/0.56  fof(f198,plain,(
% 1.29/0.56    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) | r2_hidden(X3,k3_subset_1(sK0,sK1)) | ~r2_hidden(X3,sK0)) )),
% 1.29/0.56    inference(backward_demodulation,[],[f99,f186])).
% 1.29/0.56  fof(f186,plain,(
% 1.29/0.56    k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.29/0.56    inference(superposition,[],[f110,f59])).
% 1.29/0.56  fof(f59,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f9])).
% 1.29/0.56  fof(f9,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.29/0.56  fof(f110,plain,(
% 1.29/0.56    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.29/0.56    inference(forward_demodulation,[],[f109,f45])).
% 1.29/0.56  fof(f45,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.29/0.56  fof(f109,plain,(
% 1.29/0.56    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))),
% 1.29/0.56    inference(forward_demodulation,[],[f105,f45])).
% 1.29/0.56  fof(f105,plain,(
% 1.29/0.56    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK0)),
% 1.29/0.56    inference(superposition,[],[f65,f95])).
% 1.29/0.56  fof(f95,plain,(
% 1.29/0.56    sK0 = k2_xboole_0(sK1,sK0)),
% 1.29/0.56    inference(resolution,[],[f92,f53])).
% 1.29/0.56  fof(f53,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.29/0.56    inference(cnf_transformation,[],[f22])).
% 1.29/0.56  fof(f22,plain,(
% 1.29/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.29/0.56  fof(f92,plain,(
% 1.29/0.56    r1_tarski(sK1,sK0)),
% 1.29/0.56    inference(resolution,[],[f91,f69])).
% 1.29/0.56  fof(f69,plain,(
% 1.29/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.29/0.56    inference(equality_resolution,[],[f55])).
% 1.29/0.56  fof(f55,plain,(
% 1.29/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.29/0.56    inference(cnf_transformation,[],[f33])).
% 1.29/0.56  fof(f33,plain,(
% 1.29/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.29/0.56    inference(rectify,[],[f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.29/0.56    inference(nnf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,axiom,(
% 1.29/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.29/0.56  fof(f91,plain,(
% 1.29/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.56    inference(subsumption_resolution,[],[f88,f40])).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f15])).
% 1.29/0.56  fof(f15,axiom,(
% 1.29/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.29/0.56  fof(f88,plain,(
% 1.29/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.29/0.56    inference(resolution,[],[f36,f49])).
% 1.29/0.56  fof(f49,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f29])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.29/0.56    inference(nnf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,plain,(
% 1.29/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f13])).
% 1.29/0.56  fof(f13,axiom,(
% 1.29/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.29/0.56  fof(f36,plain,(
% 1.29/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f65,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f44,f48,f48])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f11,axiom,(
% 1.29/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.29/0.56  fof(f99,plain,(
% 1.29/0.56    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | ~r2_hidden(X3,sK0)) )),
% 1.29/0.56    inference(superposition,[],[f62,f90])).
% 1.29/0.56  fof(f90,plain,(
% 1.29/0.56    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 1.29/0.56    inference(forward_demodulation,[],[f87,f59])).
% 1.29/0.56  fof(f87,plain,(
% 1.29/0.56    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))),
% 1.29/0.56    inference(resolution,[],[f36,f67])).
% 1.29/0.56  fof(f67,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f54,f64])).
% 1.29/0.56  fof(f64,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f47,f48])).
% 1.29/0.56  fof(f47,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.29/0.56  fof(f54,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f23])).
% 1.29/0.56  fof(f23,plain,(
% 1.29/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f14])).
% 1.29/0.56  fof(f14,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.29/0.56  fof(f755,plain,(
% 1.29/0.56    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,sK0) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f754])).
% 1.29/0.56  fof(f754,plain,(
% 1.29/0.56    ( ! [X3] : (r2_hidden(X3,k3_subset_1(sK0,sK1)) | r2_hidden(X3,sK0) | r2_hidden(X3,sK0) | ~r2_hidden(X3,k5_xboole_0(sK0,sK1))) )),
% 1.29/0.56    inference(resolution,[],[f199,f63])).
% 1.29/0.56  fof(f63,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f34])).
% 1.29/0.56  fof(f199,plain,(
% 1.29/0.56    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) | r2_hidden(X4,k3_subset_1(sK0,sK1)) | r2_hidden(X4,sK0)) )),
% 1.29/0.56    inference(backward_demodulation,[],[f100,f186])).
% 1.29/0.56  fof(f100,plain,(
% 1.29/0.56    ( ! [X4] : (r2_hidden(X4,k3_subset_1(sK0,sK1)) | r2_hidden(X4,sK0) | ~r2_hidden(X4,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))) )),
% 1.29/0.56    inference(superposition,[],[f63,f90])).
% 1.29/0.56  fof(f157,plain,(
% 1.29/0.56    ~spl4_1),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f156])).
% 1.29/0.56  fof(f156,plain,(
% 1.29/0.56    $false | ~spl4_1),
% 1.29/0.56    inference(subsumption_resolution,[],[f155,f35])).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    k1_xboole_0 != sK0),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f155,plain,(
% 1.29/0.56    k1_xboole_0 = sK0 | ~spl4_1),
% 1.29/0.56    inference(resolution,[],[f75,f43])).
% 1.29/0.56  fof(f43,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f20,plain,(
% 1.29/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    v1_xboole_0(sK0) | ~spl4_1),
% 1.29/0.56    inference(avatar_component_clause,[],[f73])).
% 1.29/0.56  fof(f73,plain,(
% 1.29/0.56    spl4_1 <=> v1_xboole_0(sK0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.29/0.56  fof(f80,plain,(
% 1.29/0.56    spl4_1 | spl4_2),
% 1.29/0.56    inference(avatar_split_clause,[],[f70,f77,f73])).
% 1.29/0.56  fof(f70,plain,(
% 1.29/0.56    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 1.29/0.56    inference(resolution,[],[f37,f49])).
% 1.29/0.56  fof(f37,plain,(
% 1.29/0.56    m1_subset_1(sK2,sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (8822)------------------------------
% 1.29/0.56  % (8822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (8822)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (8822)Memory used [KB]: 11001
% 1.29/0.56  % (8822)Time elapsed: 0.128 s
% 1.29/0.56  % (8822)------------------------------
% 1.29/0.56  % (8822)------------------------------
% 1.53/0.57  % (8813)Success in time 0.195 s
%------------------------------------------------------------------------------
