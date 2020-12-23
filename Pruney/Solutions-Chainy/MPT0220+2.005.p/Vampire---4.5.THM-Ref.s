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
% DateTime   : Thu Dec  3 12:35:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 301 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  173 ( 456 expanded)
%              Number of equality atoms :   70 ( 256 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1379,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1378,f76])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f73,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f1378,plain,(
    ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1368,f536])).

fof(f536,plain,(
    ! [X17,X16] : k5_xboole_0(X16,k5_xboole_0(X17,X16)) = X17 ),
    inference(forward_demodulation,[],[f525,f260])).

fof(f260,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f122,f227])).

fof(f227,plain,(
    ! [X11] : k1_xboole_0 = k4_xboole_0(X11,X11) ),
    inference(forward_demodulation,[],[f226,f132])).

fof(f132,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f122,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f226,plain,(
    ! [X11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X11,X11) ),
    inference(subsumption_resolution,[],[f199,f160])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f156,f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f156,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f59,plain,(
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

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f153,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | sP0(k1_xboole_0,X1,k1_xboole_0) ) ),
    inference(superposition,[],[f86,f132])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X1,X0))
      | sP0(X1,X2,X0) ) ),
    inference(superposition,[],[f62,f44])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f62,plain,(
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

fof(f199,plain,(
    ! [X11] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X11,X11)
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X11)) ) ),
    inference(superposition,[],[f125,f140])).

fof(f140,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f77,f40])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f47,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f74,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f122,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f74,f40])).

fof(f525,plain,(
    ! [X17,X16] : k5_xboole_0(X16,k5_xboole_0(X17,X16)) = k5_xboole_0(X17,k1_xboole_0) ),
    inference(superposition,[],[f113,f267])).

fof(f267,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f262,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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

fof(f262,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f227,f125])).

fof(f113,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f57,f44])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1368,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f75,f251])).

fof(f251,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(X4,X5) = k4_xboole_0(X4,X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f74,f141])).

fof(f141,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f77,f78])).

fof(f75,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f39,f72,f46,f73,f72])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (29354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (29379)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (29372)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (29355)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (29371)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (29372)Refutation not found, incomplete strategy% (29372)------------------------------
% 0.20/0.52  % (29372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29372)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29372)Memory used [KB]: 10618
% 0.20/0.52  % (29372)Time elapsed: 0.036 s
% 0.20/0.52  % (29372)------------------------------
% 0.20/0.52  % (29372)------------------------------
% 0.20/0.52  % (29371)Refutation not found, incomplete strategy% (29371)------------------------------
% 0.20/0.52  % (29371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29371)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29371)Memory used [KB]: 1663
% 0.20/0.52  % (29371)Time elapsed: 0.103 s
% 0.20/0.52  % (29371)------------------------------
% 0.20/0.52  % (29371)------------------------------
% 0.20/0.52  % (29356)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (29362)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (29361)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (29361)Refutation not found, incomplete strategy% (29361)------------------------------
% 0.20/0.52  % (29361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29361)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29361)Memory used [KB]: 10618
% 0.20/0.52  % (29361)Time elapsed: 0.115 s
% 0.20/0.52  % (29361)------------------------------
% 0.20/0.52  % (29361)------------------------------
% 0.20/0.53  % (29352)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (29353)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (29360)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (29352)Refutation not found, incomplete strategy% (29352)------------------------------
% 0.20/0.53  % (29352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29352)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29352)Memory used [KB]: 10618
% 0.20/0.53  % (29352)Time elapsed: 0.123 s
% 0.20/0.53  % (29352)------------------------------
% 0.20/0.53  % (29352)------------------------------
% 0.20/0.53  % (29354)Refutation not found, incomplete strategy% (29354)------------------------------
% 0.20/0.53  % (29354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29354)Memory used [KB]: 6140
% 0.20/0.53  % (29354)Time elapsed: 0.127 s
% 0.20/0.53  % (29354)------------------------------
% 0.20/0.53  % (29354)------------------------------
% 0.20/0.53  % (29377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (29369)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (29360)Refutation not found, incomplete strategy% (29360)------------------------------
% 0.20/0.53  % (29360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29375)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (29348)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (29348)Refutation not found, incomplete strategy% (29348)------------------------------
% 0.20/0.54  % (29348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29348)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29348)Memory used [KB]: 1663
% 0.20/0.54  % (29348)Time elapsed: 0.125 s
% 0.20/0.54  % (29348)------------------------------
% 0.20/0.54  % (29348)------------------------------
% 0.20/0.54  % (29360)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29360)Memory used [KB]: 10618
% 0.20/0.54  % (29360)Time elapsed: 0.133 s
% 0.20/0.54  % (29360)------------------------------
% 0.20/0.54  % (29360)------------------------------
% 0.20/0.54  % (29375)Refutation not found, incomplete strategy% (29375)------------------------------
% 0.20/0.54  % (29375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29375)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29375)Memory used [KB]: 6140
% 0.20/0.54  % (29375)Time elapsed: 0.129 s
% 0.20/0.54  % (29375)------------------------------
% 0.20/0.54  % (29375)------------------------------
% 0.20/0.54  % (29378)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (29376)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (29366)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (29367)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (29368)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (29359)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (29373)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (29359)Refutation not found, incomplete strategy% (29359)------------------------------
% 0.20/0.54  % (29359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29359)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29359)Memory used [KB]: 10618
% 0.20/0.54  % (29359)Time elapsed: 0.139 s
% 0.20/0.54  % (29359)------------------------------
% 0.20/0.54  % (29359)------------------------------
% 0.20/0.54  % (29358)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (29373)Refutation not found, incomplete strategy% (29373)------------------------------
% 0.20/0.55  % (29373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29373)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29373)Memory used [KB]: 1663
% 0.20/0.55  % (29373)Time elapsed: 0.139 s
% 0.20/0.55  % (29373)------------------------------
% 0.20/0.55  % (29373)------------------------------
% 0.20/0.55  % (29358)Refutation not found, incomplete strategy% (29358)------------------------------
% 0.20/0.55  % (29358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29358)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29358)Memory used [KB]: 10618
% 0.20/0.55  % (29358)Time elapsed: 0.138 s
% 0.20/0.55  % (29358)------------------------------
% 0.20/0.55  % (29358)------------------------------
% 0.20/0.55  % (29367)Refutation not found, incomplete strategy% (29367)------------------------------
% 0.20/0.55  % (29367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29367)Memory used [KB]: 10618
% 0.20/0.55  % (29367)Time elapsed: 0.138 s
% 0.20/0.55  % (29367)------------------------------
% 0.20/0.55  % (29367)------------------------------
% 0.20/0.55  % (29370)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (29363)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (29364)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (29350)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (29370)Refutation not found, incomplete strategy% (29370)------------------------------
% 0.20/0.55  % (29370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29370)Memory used [KB]: 10746
% 0.20/0.55  % (29370)Time elapsed: 0.148 s
% 0.20/0.55  % (29370)------------------------------
% 0.20/0.55  % (29370)------------------------------
% 0.20/0.55  % (29376)Refutation not found, incomplete strategy% (29376)------------------------------
% 0.20/0.55  % (29376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29376)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29376)Memory used [KB]: 10618
% 0.20/0.55  % (29376)Time elapsed: 0.148 s
% 0.20/0.55  % (29376)------------------------------
% 0.20/0.55  % (29376)------------------------------
% 0.20/0.56  % (29357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (29365)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (29374)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.59  % (29379)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f1379,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(subsumption_resolution,[],[f1378,f76])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f42,f73,f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f45,f71])).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f56,f70])).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f64,f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f65,f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f66,f67])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f41,f72])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,axiom,(
% 0.20/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.59  fof(f1378,plain,(
% 0.20/0.59    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.59    inference(subsumption_resolution,[],[f1368,f536])).
% 0.20/0.59  fof(f536,plain,(
% 0.20/0.59    ( ! [X17,X16] : (k5_xboole_0(X16,k5_xboole_0(X17,X16)) = X17) )),
% 0.20/0.59    inference(forward_demodulation,[],[f525,f260])).
% 0.20/0.59  fof(f260,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(backward_demodulation,[],[f122,f227])).
% 0.20/0.59  fof(f227,plain,(
% 0.20/0.59    ( ! [X11] : (k1_xboole_0 = k4_xboole_0(X11,X11)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f226,f132])).
% 0.20/0.59  fof(f132,plain,(
% 0.20/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.59    inference(superposition,[],[f122,f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.59  fof(f226,plain,(
% 0.20/0.59    ( ! [X11] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X11,X11)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f199,f160])).
% 0.20/0.59  fof(f160,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(resolution,[],[f156,f54])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(rectify,[],[f32])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.59  fof(f156,plain,(
% 0.20/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f153,f59])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.59    inference(rectify,[],[f36])).
% 1.80/0.60  fof(f36,plain,(
% 1.80/0.60    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.80/0.60    inference(nnf_transformation,[],[f26])).
% 1.80/0.60  fof(f26,plain,(
% 1.80/0.60    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.80/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.80/0.60  fof(f153,plain,(
% 1.80/0.60    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | sP0(k1_xboole_0,X1,k1_xboole_0)) )),
% 1.80/0.60    inference(superposition,[],[f86,f132])).
% 1.80/0.60  fof(f86,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X1,X0)) | sP0(X1,X2,X0)) )),
% 1.80/0.60    inference(superposition,[],[f62,f44])).
% 1.80/0.60  fof(f44,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f2])).
% 1.80/0.60  fof(f2,axiom,(
% 1.80/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.80/0.60  fof(f62,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f38])).
% 1.80/0.60  fof(f38,plain,(
% 1.80/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.80/0.60    inference(nnf_transformation,[],[f27])).
% 1.80/0.60  fof(f27,plain,(
% 1.80/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.80/0.60    inference(definition_folding,[],[f25,f26])).
% 1.80/0.60  fof(f25,plain,(
% 1.80/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.80/0.60    inference(ennf_transformation,[],[f4])).
% 1.80/0.60  fof(f4,axiom,(
% 1.80/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.80/0.60  fof(f199,plain,(
% 1.80/0.60    ( ! [X11] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X11,X11) | ~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X11))) )),
% 1.80/0.60    inference(superposition,[],[f125,f140])).
% 1.80/0.60  fof(f140,plain,(
% 1.80/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.80/0.60    inference(superposition,[],[f77,f40])).
% 1.80/0.60  fof(f77,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.80/0.60    inference(definition_unfolding,[],[f43,f47,f47])).
% 1.80/0.60  fof(f47,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f9])).
% 1.80/0.60  fof(f9,axiom,(
% 1.80/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.80/0.60  fof(f43,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f1])).
% 1.80/0.60  fof(f1,axiom,(
% 1.80/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.80/0.60  fof(f125,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(superposition,[],[f74,f78])).
% 1.80/0.60  fof(f78,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(definition_unfolding,[],[f49,f47])).
% 1.80/0.60  fof(f49,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f23])).
% 1.80/0.60  fof(f23,plain,(
% 1.80/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f7])).
% 1.80/0.60  fof(f7,axiom,(
% 1.80/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.80/0.60  fof(f74,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.80/0.60    inference(definition_unfolding,[],[f48,f47])).
% 1.80/0.60  fof(f48,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f6])).
% 1.80/0.60  fof(f6,axiom,(
% 1.80/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.80/0.60  fof(f122,plain,(
% 1.80/0.60    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.80/0.60    inference(superposition,[],[f74,f40])).
% 1.80/0.60  fof(f525,plain,(
% 1.80/0.60    ( ! [X17,X16] : (k5_xboole_0(X16,k5_xboole_0(X17,X16)) = k5_xboole_0(X17,k1_xboole_0)) )),
% 1.80/0.60    inference(superposition,[],[f113,f267])).
% 1.80/0.60  fof(f267,plain,(
% 1.80/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.80/0.60    inference(subsumption_resolution,[],[f262,f79])).
% 1.80/0.60  fof(f79,plain,(
% 1.80/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.80/0.60    inference(equality_resolution,[],[f51])).
% 1.80/0.60  fof(f51,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.80/0.60    inference(cnf_transformation,[],[f31])).
% 1.80/0.60  fof(f31,plain,(
% 1.80/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.60    inference(flattening,[],[f30])).
% 1.80/0.60  fof(f30,plain,(
% 1.80/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.60    inference(nnf_transformation,[],[f5])).
% 1.80/0.60  fof(f5,axiom,(
% 1.80/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.96/0.61  fof(f262,plain,(
% 1.96/0.61    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X1)) )),
% 1.96/0.61    inference(superposition,[],[f227,f125])).
% 1.96/0.61  fof(f113,plain,(
% 1.96/0.61    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 1.96/0.61    inference(superposition,[],[f57,f44])).
% 1.96/0.61  fof(f57,plain,(
% 1.96/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f10])).
% 1.96/0.61  fof(f10,axiom,(
% 1.96/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.96/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.96/0.61  fof(f1368,plain,(
% 1.96/0.61    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.96/0.61    inference(superposition,[],[f75,f251])).
% 1.96/0.61  fof(f251,plain,(
% 1.96/0.61    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k4_xboole_0(X4,X5) | ~r1_tarski(X5,X4)) )),
% 1.96/0.61    inference(superposition,[],[f74,f141])).
% 1.96/0.61  fof(f141,plain,(
% 1.96/0.61    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 1.96/0.61    inference(superposition,[],[f77,f78])).
% 1.96/0.61  fof(f75,plain,(
% 1.96/0.61    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.96/0.61    inference(definition_unfolding,[],[f39,f72,f46,f73,f72])).
% 1.96/0.61  fof(f46,plain,(
% 1.96/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.96/0.61    inference(cnf_transformation,[],[f11])).
% 1.96/0.61  fof(f11,axiom,(
% 1.96/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.96/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.96/0.61  fof(f39,plain,(
% 1.96/0.61    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.96/0.61    inference(cnf_transformation,[],[f29])).
% 1.96/0.61  fof(f29,plain,(
% 1.96/0.61    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.96/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).
% 1.96/0.61  fof(f28,plain,(
% 1.96/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k2_tarski(sK1,sK2))),
% 1.96/0.61    introduced(choice_axiom,[])).
% 1.96/0.61  fof(f22,plain,(
% 1.96/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.96/0.61    inference(ennf_transformation,[],[f21])).
% 1.96/0.61  fof(f21,negated_conjecture,(
% 1.96/0.61    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.96/0.61    inference(negated_conjecture,[],[f20])).
% 1.96/0.61  fof(f20,conjecture,(
% 1.96/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.96/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.96/0.61  % SZS output end Proof for theBenchmark
% 1.96/0.61  % (29379)------------------------------
% 1.96/0.61  % (29379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.61  % (29379)Termination reason: Refutation
% 1.96/0.61  
% 1.96/0.61  % (29379)Memory used [KB]: 2686
% 1.96/0.61  % (29379)Time elapsed: 0.164 s
% 1.96/0.61  % (29379)------------------------------
% 1.96/0.61  % (29379)------------------------------
% 1.96/0.61  % (29343)Success in time 0.251 s
%------------------------------------------------------------------------------
