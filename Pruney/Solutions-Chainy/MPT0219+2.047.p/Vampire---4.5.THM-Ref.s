%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:26 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  105 (2058 expanded)
%              Number of leaves         :   21 ( 518 expanded)
%              Depth                    :   24
%              Number of atoms          :  201 (5434 expanded)
%              Number of equality atoms :   73 (1301 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1838,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1835,f40])).

fof(f40,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1835,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f1825,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f70,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f1825,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1810,f537])).

fof(f537,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5 ),
    inference(backward_demodulation,[],[f206,f531])).

fof(f531,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(forward_demodulation,[],[f506,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f506,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f206,f189])).

fof(f189,plain,(
    ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6) ),
    inference(resolution,[],[f182,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f181,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f181,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k5_xboole_0(X5,X5)) ),
    inference(subsumption_resolution,[],[f179,f129])).

fof(f129,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k5_xboole_0(X3,X3))
      | ~ r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k5_xboole_0(X3,X3))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f61,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( sP0(k5_xboole_0(X2,X2),X3,X2)
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f64,f106])).

fof(f106,plain,(
    ! [X1] : k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(subsumption_resolution,[],[f102,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ! [X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f72,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f179,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k5_xboole_0(X5,X5)) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k5_xboole_0(X5,X5))
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f63,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ sP0(k5_xboole_0(X0,X0),X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f65,f106])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f206,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f59,f189])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1810,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f1626,f675])).

fof(f675,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f669,f42])).

fof(f669,plain,(
    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(superposition,[],[f537,f586])).

fof(f586,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f570,f189])).

fof(f570,plain,(
    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f537,f280])).

fof(f280,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f71,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f39,f70,f67,f70,f70])).

fof(f39,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f1626,plain,(
    ! [X4,X5] : r1_tarski(X4,k5_xboole_0(k3_xboole_0(X5,X4),k5_xboole_0(X4,X5))) ),
    inference(superposition,[],[f1194,f46])).

fof(f1194,plain,(
    ! [X6,X5] : r1_tarski(X5,k5_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f1182,f877])).

fof(f877,plain,(
    ! [X30,X31] : k5_xboole_0(X30,X31) = k5_xboole_0(X31,X30) ),
    inference(superposition,[],[f537,f854])).

fof(f854,plain,(
    ! [X30,X31] : k5_xboole_0(X31,k5_xboole_0(X30,X31)) = X30 ),
    inference(forward_demodulation,[],[f837,f42])).

fof(f837,plain,(
    ! [X30,X31] : k5_xboole_0(X31,k5_xboole_0(X30,X31)) = k5_xboole_0(X30,k1_xboole_0) ),
    inference(superposition,[],[f537,f210])).

fof(f210,plain,(
    ! [X8,X7] : k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f59,f189])).

fof(f1182,plain,(
    ! [X6,X5] : r1_tarski(X5,k5_xboole_0(k5_xboole_0(X5,X6),k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f1065,f537])).

fof(f1065,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f1040,f46])).

fof(f1040,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X0))) ),
    inference(superposition,[],[f216,f537])).

fof(f216,plain,(
    ! [X17,X18,X16] : r1_tarski(X18,k5_xboole_0(X18,k5_xboole_0(X16,k5_xboole_0(X17,k3_xboole_0(k5_xboole_0(X16,X17),X18))))) ),
    inference(superposition,[],[f73,f59])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:07:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.52  % (11974)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (11983)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (11998)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (11992)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (11975)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (11973)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (11992)Refutation not found, incomplete strategy% (11992)------------------------------
% 0.20/0.54  % (11992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11996)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (11984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (11990)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (11992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11992)Memory used [KB]: 1663
% 0.20/0.54  % (11992)Time elapsed: 0.065 s
% 0.20/0.54  % (11992)------------------------------
% 0.20/0.54  % (11992)------------------------------
% 0.20/0.54  % (11976)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (11982)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (11972)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (11991)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (11997)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (11979)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (11979)Refutation not found, incomplete strategy% (11979)------------------------------
% 0.20/0.56  % (11979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11979)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11979)Memory used [KB]: 10618
% 0.20/0.56  % (11979)Time elapsed: 0.145 s
% 0.20/0.56  % (11979)------------------------------
% 0.20/0.56  % (11979)------------------------------
% 0.20/0.56  % (11994)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (11988)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (11986)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (11989)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (11986)Refutation not found, incomplete strategy% (11986)------------------------------
% 0.20/0.57  % (11986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11986)Memory used [KB]: 10618
% 0.20/0.57  % (11986)Time elapsed: 0.160 s
% 0.20/0.57  % (11986)------------------------------
% 0.20/0.57  % (11986)------------------------------
% 0.20/0.57  % (11989)Refutation not found, incomplete strategy% (11989)------------------------------
% 0.20/0.57  % (11989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11989)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11989)Memory used [KB]: 10618
% 0.20/0.57  % (11989)Time elapsed: 0.161 s
% 0.20/0.57  % (11989)------------------------------
% 0.20/0.57  % (11989)------------------------------
% 1.71/0.57  % (11969)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.71/0.57  % (11971)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.71/0.57  % (11981)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.57  % (11970)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.71/0.57  % (11977)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.71/0.57  % (11995)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.71/0.57  % (11969)Refutation not found, incomplete strategy% (11969)------------------------------
% 1.71/0.57  % (11969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.57  % (11969)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.57  
% 1.71/0.57  % (11969)Memory used [KB]: 1663
% 1.71/0.57  % (11969)Time elapsed: 0.158 s
% 1.71/0.57  % (11969)------------------------------
% 1.71/0.57  % (11969)------------------------------
% 1.71/0.58  % (11978)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.71/0.58  % (11980)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.71/0.58  % (11978)Refutation not found, incomplete strategy% (11978)------------------------------
% 1.71/0.58  % (11978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (11978)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (11978)Memory used [KB]: 10618
% 1.71/0.58  % (11978)Time elapsed: 0.166 s
% 1.71/0.58  % (11978)------------------------------
% 1.71/0.58  % (11978)------------------------------
% 1.71/0.58  % (11985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.71/0.58  % (11987)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.86/0.59  % (11993)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.86/0.60  % (11980)Refutation not found, incomplete strategy% (11980)------------------------------
% 1.86/0.60  % (11980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.60  % (11980)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.60  
% 1.86/0.60  % (11980)Memory used [KB]: 10618
% 1.86/0.60  % (11980)Time elapsed: 0.199 s
% 1.86/0.60  % (11980)------------------------------
% 1.86/0.60  % (11980)------------------------------
% 2.14/0.63  % (11996)Refutation found. Thanks to Tanya!
% 2.14/0.63  % SZS status Theorem for theBenchmark
% 2.14/0.63  % SZS output start Proof for theBenchmark
% 2.14/0.63  fof(f1838,plain,(
% 2.14/0.63    $false),
% 2.14/0.63    inference(subsumption_resolution,[],[f1835,f40])).
% 2.14/0.63  fof(f40,plain,(
% 2.14/0.63    sK1 != sK2),
% 2.14/0.63    inference(cnf_transformation,[],[f29])).
% 2.14/0.63  fof(f29,plain,(
% 2.14/0.63    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 2.14/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f28])).
% 2.14/0.63  fof(f28,plain,(
% 2.14/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 2.14/0.63    introduced(choice_axiom,[])).
% 2.14/0.63  fof(f21,plain,(
% 2.14/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.14/0.63    inference(ennf_transformation,[],[f19])).
% 2.14/0.63  fof(f19,negated_conjecture,(
% 2.14/0.63    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.14/0.63    inference(negated_conjecture,[],[f18])).
% 2.14/0.63  fof(f18,conjecture,(
% 2.14/0.63    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.14/0.63  fof(f1835,plain,(
% 2.14/0.63    sK1 = sK2),
% 2.14/0.63    inference(resolution,[],[f1825,f74])).
% 2.14/0.63  fof(f74,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1) )),
% 2.14/0.63    inference(definition_unfolding,[],[f51,f70,f70])).
% 2.14/0.63  fof(f70,plain,(
% 2.14/0.63    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.14/0.63    inference(definition_unfolding,[],[f43,f69])).
% 2.14/0.63  fof(f69,plain,(
% 2.14/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.14/0.63    inference(definition_unfolding,[],[f47,f68])).
% 2.14/0.63  fof(f68,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.14/0.63    inference(definition_unfolding,[],[f58,f66])).
% 2.14/0.63  fof(f66,plain,(
% 2.14/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f16])).
% 2.14/0.63  fof(f16,axiom,(
% 2.14/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.14/0.63  fof(f58,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f15])).
% 2.14/0.63  fof(f15,axiom,(
% 2.14/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.14/0.63  fof(f47,plain,(
% 2.14/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f14])).
% 2.14/0.63  fof(f14,axiom,(
% 2.14/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.14/0.63  fof(f43,plain,(
% 2.14/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f13])).
% 2.14/0.63  fof(f13,axiom,(
% 2.14/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.14/0.63  fof(f51,plain,(
% 2.14/0.63    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 2.14/0.63    inference(cnf_transformation,[],[f23])).
% 2.14/0.63  fof(f23,plain,(
% 2.14/0.63    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.14/0.63    inference(ennf_transformation,[],[f17])).
% 2.14/0.63  fof(f17,axiom,(
% 2.14/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.14/0.63  fof(f1825,plain,(
% 2.14/0.63    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.14/0.63    inference(forward_demodulation,[],[f1810,f537])).
% 2.14/0.63  fof(f537,plain,(
% 2.14/0.63    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5) )),
% 2.14/0.63    inference(backward_demodulation,[],[f206,f531])).
% 2.14/0.63  fof(f531,plain,(
% 2.14/0.63    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = X6) )),
% 2.14/0.63    inference(forward_demodulation,[],[f506,f42])).
% 2.14/0.63  fof(f42,plain,(
% 2.14/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.14/0.63    inference(cnf_transformation,[],[f9])).
% 2.14/0.63  fof(f9,axiom,(
% 2.14/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.14/0.63  fof(f506,plain,(
% 2.14/0.63    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(X6,k1_xboole_0)) )),
% 2.14/0.63    inference(superposition,[],[f206,f189])).
% 2.14/0.63  fof(f189,plain,(
% 2.14/0.63    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) )),
% 2.14/0.63    inference(resolution,[],[f182,f89])).
% 2.14/0.63  fof(f89,plain,(
% 2.14/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.14/0.63    inference(resolution,[],[f54,f41])).
% 2.14/0.63  fof(f41,plain,(
% 2.14/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f8])).
% 2.14/0.63  fof(f8,axiom,(
% 2.14/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.14/0.63  fof(f54,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f31])).
% 2.14/0.63  fof(f31,plain,(
% 2.14/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.63    inference(flattening,[],[f30])).
% 2.14/0.63  fof(f30,plain,(
% 2.14/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.63    inference(nnf_transformation,[],[f5])).
% 2.14/0.63  fof(f5,axiom,(
% 2.14/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.63  fof(f182,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 2.14/0.63    inference(resolution,[],[f181,f56])).
% 2.14/0.63  fof(f56,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f35])).
% 2.14/0.63  fof(f35,plain,(
% 2.14/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.14/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 2.21/0.65  fof(f34,plain,(
% 2.21/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f33,plain,(
% 2.21/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.65    inference(rectify,[],[f32])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.65    inference(nnf_transformation,[],[f24])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.21/0.65  fof(f181,plain,(
% 2.21/0.65    ( ! [X4,X5] : (~r2_hidden(X4,k5_xboole_0(X5,X5))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f179,f129])).
% 2.21/0.65  fof(f129,plain,(
% 2.21/0.65    ( ! [X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,X3)) | ~r2_hidden(X2,X3)) )),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f128])).
% 2.21/0.65  fof(f128,plain,(
% 2.21/0.65    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X2,k5_xboole_0(X3,X3)) | ~r2_hidden(X2,X3)) )),
% 2.21/0.65    inference(resolution,[],[f61,f109])).
% 2.21/0.65  fof(f109,plain,(
% 2.21/0.65    ( ! [X2,X3] : (sP0(k5_xboole_0(X2,X2),X3,X2) | ~r2_hidden(X3,X2)) )),
% 2.21/0.65    inference(superposition,[],[f64,f106])).
% 2.21/0.65  fof(f106,plain,(
% 2.21/0.65    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f102,f75])).
% 2.21/0.65  fof(f75,plain,(
% 2.21/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/0.65    inference(equality_resolution,[],[f53])).
% 2.21/0.65  fof(f53,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.21/0.65    inference(cnf_transformation,[],[f31])).
% 2.21/0.65  fof(f102,plain,(
% 2.21/0.65    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 | ~r1_tarski(X1,X1)) )),
% 2.21/0.65    inference(superposition,[],[f72,f50])).
% 2.21/0.65  fof(f50,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f7])).
% 2.21/0.65  fof(f7,axiom,(
% 2.21/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.21/0.65  fof(f72,plain,(
% 2.21/0.65    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.21/0.65    inference(definition_unfolding,[],[f44,f67])).
% 2.21/0.65  fof(f67,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f49,f48])).
% 2.21/0.65  fof(f48,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f12])).
% 2.21/0.65  fof(f12,axiom,(
% 2.21/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.21/0.65    inference(cnf_transformation,[],[f20])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.65    inference(rectify,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f38])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.21/0.65    inference(nnf_transformation,[],[f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 2.21/0.65    inference(definition_folding,[],[f25,f26])).
% 2.21/0.65  fof(f26,plain,(
% 2.21/0.65    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.21/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.21/0.65  fof(f25,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.21/0.65    inference(ennf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.21/0.65  fof(f61,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f37])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 2.21/0.65    inference(rectify,[],[f36])).
% 2.21/0.65  fof(f36,plain,(
% 2.21/0.65    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 2.21/0.65    inference(nnf_transformation,[],[f26])).
% 2.21/0.65  fof(f179,plain,(
% 2.21/0.65    ( ! [X4,X5] : (r2_hidden(X4,X5) | ~r2_hidden(X4,k5_xboole_0(X5,X5))) )),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f173])).
% 2.21/0.65  fof(f173,plain,(
% 2.21/0.65    ( ! [X4,X5] : (r2_hidden(X4,X5) | ~r2_hidden(X4,k5_xboole_0(X5,X5)) | r2_hidden(X4,X5)) )),
% 2.21/0.65    inference(resolution,[],[f63,f108])).
% 2.21/0.65  fof(f108,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~sP0(k5_xboole_0(X0,X0),X1,X0) | r2_hidden(X1,X0)) )),
% 2.21/0.65    inference(superposition,[],[f65,f106])).
% 2.21/0.65  fof(f65,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f38])).
% 2.21/0.65  fof(f63,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f37])).
% 2.21/0.65  fof(f206,plain,(
% 2.21/0.65    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,X5)) )),
% 2.21/0.65    inference(superposition,[],[f59,f189])).
% 2.21/0.65  fof(f59,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f11])).
% 2.21/0.65  fof(f11,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.21/0.65  fof(f1810,plain,(
% 2.21/0.65    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 2.21/0.65    inference(superposition,[],[f1626,f675])).
% 2.21/0.65  fof(f675,plain,(
% 2.21/0.65    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 2.21/0.65    inference(forward_demodulation,[],[f669,f42])).
% 2.21/0.65  fof(f669,plain,(
% 2.21/0.65    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)),
% 2.21/0.65    inference(superposition,[],[f537,f586])).
% 2.21/0.65  fof(f586,plain,(
% 2.21/0.65    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 2.21/0.65    inference(forward_demodulation,[],[f570,f189])).
% 2.21/0.65  fof(f570,plain,(
% 2.21/0.65    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.21/0.65    inference(superposition,[],[f537,f280])).
% 2.21/0.65  fof(f280,plain,(
% 2.21/0.65    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 2.21/0.65    inference(forward_demodulation,[],[f71,f46])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f1])).
% 2.21/0.65  fof(f1,axiom,(
% 2.21/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.21/0.65  fof(f71,plain,(
% 2.21/0.65    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 2.21/0.65    inference(definition_unfolding,[],[f39,f70,f67,f70,f70])).
% 2.21/0.65  fof(f39,plain,(
% 2.21/0.65    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 2.21/0.65    inference(cnf_transformation,[],[f29])).
% 2.21/0.65  fof(f1626,plain,(
% 2.21/0.65    ( ! [X4,X5] : (r1_tarski(X4,k5_xboole_0(k3_xboole_0(X5,X4),k5_xboole_0(X4,X5)))) )),
% 2.21/0.65    inference(superposition,[],[f1194,f46])).
% 2.21/0.65  fof(f1194,plain,(
% 2.21/0.65    ( ! [X6,X5] : (r1_tarski(X5,k5_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,X6)))) )),
% 2.21/0.65    inference(forward_demodulation,[],[f1182,f877])).
% 2.21/0.65  fof(f877,plain,(
% 2.21/0.65    ( ! [X30,X31] : (k5_xboole_0(X30,X31) = k5_xboole_0(X31,X30)) )),
% 2.21/0.65    inference(superposition,[],[f537,f854])).
% 2.21/0.65  fof(f854,plain,(
% 2.21/0.65    ( ! [X30,X31] : (k5_xboole_0(X31,k5_xboole_0(X30,X31)) = X30) )),
% 2.21/0.65    inference(forward_demodulation,[],[f837,f42])).
% 2.21/0.65  fof(f837,plain,(
% 2.21/0.65    ( ! [X30,X31] : (k5_xboole_0(X31,k5_xboole_0(X30,X31)) = k5_xboole_0(X30,k1_xboole_0)) )),
% 2.21/0.65    inference(superposition,[],[f537,f210])).
% 2.21/0.65  fof(f210,plain,(
% 2.21/0.65    ( ! [X8,X7] : (k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 2.21/0.65    inference(superposition,[],[f59,f189])).
% 2.21/0.65  fof(f1182,plain,(
% 2.21/0.65    ( ! [X6,X5] : (r1_tarski(X5,k5_xboole_0(k5_xboole_0(X5,X6),k3_xboole_0(X5,X6)))) )),
% 2.21/0.65    inference(superposition,[],[f1065,f537])).
% 2.21/0.65  fof(f1065,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X0,X1))))) )),
% 2.21/0.65    inference(forward_demodulation,[],[f1040,f46])).
% 2.21/0.65  fof(f1040,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X0)))) )),
% 2.21/0.65    inference(superposition,[],[f216,f537])).
% 2.21/0.65  fof(f216,plain,(
% 2.21/0.65    ( ! [X17,X18,X16] : (r1_tarski(X18,k5_xboole_0(X18,k5_xboole_0(X16,k5_xboole_0(X17,k3_xboole_0(k5_xboole_0(X16,X17),X18)))))) )),
% 2.21/0.65    inference(superposition,[],[f73,f59])).
% 2.21/0.65  fof(f73,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f45,f67])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f10])).
% 2.21/0.65  fof(f10,axiom,(
% 2.21/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (11996)------------------------------
% 2.21/0.65  % (11996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (11996)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (11996)Memory used [KB]: 7036
% 2.21/0.65  % (11996)Time elapsed: 0.228 s
% 2.21/0.65  % (11996)------------------------------
% 2.21/0.65  % (11996)------------------------------
% 2.21/0.65  % (11968)Success in time 0.299 s
%------------------------------------------------------------------------------
