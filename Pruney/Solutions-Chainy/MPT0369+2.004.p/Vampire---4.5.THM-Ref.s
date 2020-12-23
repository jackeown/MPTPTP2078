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
% DateTime   : Thu Dec  3 12:45:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 125 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 ( 425 expanded)
%              Number of equality atoms :   38 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f503,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f503,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f502,f88])).

fof(f88,plain,
    ( r2_hidden(sK3,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r2_hidden(sK3,k3_subset_1(sK1,sK2))
    & ~ r2_hidden(sK3,sK2)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(sK1))
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f31,f30,f29])).

fof(f29,plain,
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
              ( ~ r2_hidden(X2,k3_subset_1(sK1,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(sK1)) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(sK1,X1))
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(sK1)) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(sK1,sK2))
          & ~ r2_hidden(X2,sK2)
          & m1_subset_1(X2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k3_subset_1(sK1,sK2))
        & ~ r2_hidden(X2,sK2)
        & m1_subset_1(X2,sK1) )
   => ( ~ r2_hidden(sK3,k3_subset_1(sK1,sK2))
      & ~ r2_hidden(sK3,sK2)
      & m1_subset_1(sK3,sK1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f502,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f499,f41])).

fof(f41,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f499,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f493,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f493,plain,(
    ~ sP0(sK2,sK3,sK1) ),
    inference(resolution,[],[f461,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f461,plain,(
    ~ r2_hidden(sK3,k5_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f427,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f427,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f42,f202])).

fof(f202,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X3,X2) = k5_xboole_0(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f196,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f148,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f148,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,X1))
      | r1_tarski(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f60,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f107,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_subset_1(X0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f58,f68])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f196,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X3,X2) = k5_xboole_0(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f111,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f111,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f70,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,(
    ~ r2_hidden(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (17645)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (17648)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (17666)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (17656)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (17673)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.57  % (17653)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.58  % (17653)Refutation not found, incomplete strategy% (17653)------------------------------
% 0.20/0.58  % (17653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (17653)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (17653)Memory used [KB]: 10618
% 0.20/0.58  % (17653)Time elapsed: 0.153 s
% 0.20/0.58  % (17653)------------------------------
% 0.20/0.58  % (17653)------------------------------
% 0.20/0.59  % (17666)Refutation not found, incomplete strategy% (17666)------------------------------
% 0.20/0.59  % (17666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (17666)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (17666)Memory used [KB]: 10746
% 0.20/0.59  % (17666)Time elapsed: 0.165 s
% 0.20/0.59  % (17666)------------------------------
% 0.20/0.59  % (17666)------------------------------
% 0.20/0.59  % (17658)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.59  % (17649)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.59  % (17647)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.59  % (17667)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.60  % (17644)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.60  % (17644)Refutation not found, incomplete strategy% (17644)------------------------------
% 0.20/0.60  % (17644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (17644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (17644)Memory used [KB]: 1663
% 0.20/0.60  % (17644)Time elapsed: 0.176 s
% 0.20/0.60  % (17644)------------------------------
% 0.20/0.60  % (17644)------------------------------
% 0.20/0.60  % (17646)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.61  % (17663)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.61  % (17659)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.61  % (17673)Refutation found. Thanks to Tanya!
% 0.20/0.61  % SZS status Theorem for theBenchmark
% 0.20/0.61  % SZS output start Proof for theBenchmark
% 0.20/0.61  fof(f517,plain,(
% 0.20/0.61    $false),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f38,f503,f49])).
% 0.20/0.61  fof(f49,plain,(
% 0.20/0.61    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f20])).
% 0.20/0.61  fof(f20,plain,(
% 0.20/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.61    inference(ennf_transformation,[],[f2])).
% 0.20/0.61  fof(f2,axiom,(
% 0.20/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.61  fof(f503,plain,(
% 0.20/0.61    v1_xboole_0(sK1)),
% 0.20/0.61    inference(resolution,[],[f502,f88])).
% 0.20/0.61  fof(f88,plain,(
% 0.20/0.61    r2_hidden(sK3,sK1) | v1_xboole_0(sK1)),
% 0.20/0.61    inference(resolution,[],[f52,f40])).
% 0.20/0.61  fof(f40,plain,(
% 0.20/0.61    m1_subset_1(sK3,sK1)),
% 0.20/0.61    inference(cnf_transformation,[],[f32])).
% 0.20/0.61  fof(f32,plain,(
% 0.20/0.61    ((~r2_hidden(sK3,k3_subset_1(sK1,sK2)) & ~r2_hidden(sK3,sK2) & m1_subset_1(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))) & k1_xboole_0 != sK1),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f31,f30,f29])).
% 0.20/0.61  fof(f29,plain,(
% 0.20/0.61    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK1,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(sK1))) & k1_xboole_0 != sK1)),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f30,plain,(
% 0.20/0.61    ? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK1,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(sK1))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(sK1,sK2)) & ~r2_hidden(X2,sK2) & m1_subset_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f31,plain,(
% 0.20/0.61    ? [X2] : (~r2_hidden(X2,k3_subset_1(sK1,sK2)) & ~r2_hidden(X2,sK2) & m1_subset_1(X2,sK1)) => (~r2_hidden(sK3,k3_subset_1(sK1,sK2)) & ~r2_hidden(sK3,sK2) & m1_subset_1(sK3,sK1))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f19,plain,(
% 0.20/0.61    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.20/0.61    inference(flattening,[],[f18])).
% 0.20/0.61  fof(f18,plain,(
% 0.20/0.61    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.20/0.61    inference(ennf_transformation,[],[f17])).
% 0.20/0.61  fof(f17,negated_conjecture,(
% 0.20/0.61    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.61    inference(negated_conjecture,[],[f16])).
% 0.20/0.61  fof(f16,conjecture,(
% 0.20/0.61    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.20/0.61  fof(f52,plain,(
% 0.20/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f33])).
% 0.20/0.61  fof(f33,plain,(
% 0.20/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.61    inference(nnf_transformation,[],[f21])).
% 0.20/0.61  fof(f21,plain,(
% 0.20/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f7])).
% 0.20/0.61  fof(f7,axiom,(
% 0.20/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.61  fof(f502,plain,(
% 0.20/0.61    ~r2_hidden(sK3,sK1)),
% 0.20/0.61    inference(subsumption_resolution,[],[f499,f41])).
% 0.20/0.61  fof(f41,plain,(
% 0.20/0.61    ~r2_hidden(sK3,sK2)),
% 0.20/0.61    inference(cnf_transformation,[],[f32])).
% 0.20/0.61  fof(f499,plain,(
% 0.20/0.61    r2_hidden(sK3,sK2) | ~r2_hidden(sK3,sK1)),
% 0.20/0.61    inference(resolution,[],[f493,f63])).
% 0.20/0.61  fof(f63,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f36])).
% 0.20/0.61  fof(f36,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.61    inference(rectify,[],[f35])).
% 0.20/0.61  fof(f35,plain,(
% 0.20/0.61    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 0.20/0.61    inference(nnf_transformation,[],[f27])).
% 0.20/0.61  fof(f27,plain,(
% 0.20/0.61    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.61  fof(f493,plain,(
% 0.20/0.61    ~sP0(sK2,sK3,sK1)),
% 0.20/0.61    inference(resolution,[],[f461,f66])).
% 0.20/0.61  fof(f66,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f37])).
% 0.20/0.61  fof(f37,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.61    inference(nnf_transformation,[],[f28])).
% 0.20/0.61  fof(f28,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 0.20/0.61    inference(definition_folding,[],[f26,f27])).
% 0.20/0.61  fof(f26,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.61    inference(ennf_transformation,[],[f3])).
% 0.20/0.61  fof(f3,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.61  fof(f461,plain,(
% 0.20/0.61    ~r2_hidden(sK3,k5_xboole_0(sK1,sK2))),
% 0.20/0.61    inference(subsumption_resolution,[],[f427,f39])).
% 0.20/0.61  fof(f39,plain,(
% 0.20/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.20/0.61    inference(cnf_transformation,[],[f32])).
% 0.20/0.61  fof(f427,plain,(
% 0.20/0.61    ~r2_hidden(sK3,k5_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.20/0.61    inference(superposition,[],[f42,f202])).
% 0.20/0.61  fof(f202,plain,(
% 0.20/0.61    ( ! [X2,X3] : (k3_subset_1(X3,X2) = k5_xboole_0(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 0.20/0.61    inference(subsumption_resolution,[],[f196,f149])).
% 0.20/0.61  fof(f149,plain,(
% 0.20/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.20/0.61    inference(subsumption_resolution,[],[f148,f75])).
% 0.20/0.61  fof(f75,plain,(
% 0.20/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(forward_demodulation,[],[f69,f68])).
% 0.20/0.61  fof(f68,plain,(
% 0.20/0.61    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.61    inference(definition_unfolding,[],[f45,f67])).
% 0.20/0.61  fof(f67,plain,(
% 0.20/0.61    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.61    inference(definition_unfolding,[],[f48,f44])).
% 0.20/0.61  fof(f44,plain,(
% 0.20/0.61    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f8])).
% 0.20/0.61  fof(f8,axiom,(
% 0.20/0.61    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.61  fof(f48,plain,(
% 0.20/0.61    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f13])).
% 0.20/0.61  fof(f13,axiom,(
% 0.20/0.61    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.61  fof(f45,plain,(
% 0.20/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.61    inference(cnf_transformation,[],[f9])).
% 0.20/0.61  fof(f9,axiom,(
% 0.20/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.61  fof(f69,plain,(
% 0.20/0.61    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(definition_unfolding,[],[f47,f67])).
% 0.20/0.61  fof(f47,plain,(
% 0.20/0.61    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f11])).
% 0.20/0.61  fof(f11,axiom,(
% 0.20/0.61    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.61  fof(f148,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(subsumption_resolution,[],[f139,f43])).
% 0.20/0.61  fof(f43,plain,(
% 0.20/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f6])).
% 0.20/0.61  fof(f6,axiom,(
% 0.20/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.61  fof(f139,plain,(
% 0.20/0.61    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k3_subset_1(X0,X1)) | r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(superposition,[],[f60,f108])).
% 0.20/0.61  fof(f108,plain,(
% 0.20/0.61    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.20/0.61    inference(subsumption_resolution,[],[f107,f46])).
% 0.20/0.61  fof(f46,plain,(
% 0.20/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f15])).
% 0.20/0.61  fof(f15,axiom,(
% 0.20/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.61  fof(f107,plain,(
% 0.20/0.61    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(superposition,[],[f58,f68])).
% 0.20/0.61  fof(f58,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f24])).
% 0.20/0.61  fof(f24,plain,(
% 0.20/0.61    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f12])).
% 0.20/0.61  fof(f12,axiom,(
% 0.20/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.61  fof(f60,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f34])).
% 0.20/0.61  fof(f34,plain,(
% 0.20/0.61    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(nnf_transformation,[],[f25])).
% 0.20/0.61  fof(f25,plain,(
% 0.20/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f14])).
% 0.20/0.61  fof(f14,axiom,(
% 0.20/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.61  fof(f196,plain,(
% 0.20/0.61    ( ! [X2,X3] : (k3_subset_1(X3,X2) = k5_xboole_0(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~r1_tarski(X2,X3)) )),
% 0.20/0.61    inference(superposition,[],[f111,f56])).
% 0.20/0.61  fof(f56,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f22,plain,(
% 0.20/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.61    inference(ennf_transformation,[],[f5])).
% 0.20/0.61  fof(f5,axiom,(
% 0.20/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.61  fof(f111,plain,(
% 0.20/0.61    ( ! [X2,X3] : (k3_subset_1(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.20/0.61    inference(superposition,[],[f70,f50])).
% 0.20/0.61  fof(f50,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f1])).
% 0.20/0.61  fof(f1,axiom,(
% 0.20/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.61  fof(f70,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(definition_unfolding,[],[f57,f51])).
% 0.20/0.61  fof(f51,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f4])).
% 0.20/0.61  fof(f4,axiom,(
% 0.20/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.61  fof(f57,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f23])).
% 0.20/0.61  fof(f23,plain,(
% 0.20/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f10])).
% 0.20/0.61  fof(f10,axiom,(
% 0.20/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.61  fof(f42,plain,(
% 0.20/0.61    ~r2_hidden(sK3,k3_subset_1(sK1,sK2))),
% 0.20/0.61    inference(cnf_transformation,[],[f32])).
% 0.20/0.61  fof(f38,plain,(
% 0.20/0.61    k1_xboole_0 != sK1),
% 0.20/0.61    inference(cnf_transformation,[],[f32])).
% 0.20/0.61  % SZS output end Proof for theBenchmark
% 0.20/0.61  % (17673)------------------------------
% 0.20/0.61  % (17673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (17673)Termination reason: Refutation
% 0.20/0.61  
% 0.20/0.61  % (17673)Memory used [KB]: 1918
% 0.20/0.61  % (17673)Time elapsed: 0.181 s
% 0.20/0.61  % (17673)------------------------------
% 0.20/0.61  % (17673)------------------------------
% 0.20/0.61  % (17643)Success in time 0.247 s
%------------------------------------------------------------------------------
