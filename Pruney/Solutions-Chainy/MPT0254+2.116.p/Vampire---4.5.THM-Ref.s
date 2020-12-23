%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:28 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   88 (1495 expanded)
%              Number of leaves         :   17 ( 450 expanded)
%              Depth                    :   22
%              Number of atoms          :  197 (2134 expanded)
%              Number of equality atoms :  108 (1207 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1025,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1018,f772])).

fof(f772,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f768])).

fof(f768,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f647,f760])).

fof(f760,plain,(
    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f669,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f669,plain,(
    ~ r2_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f657])).

fof(f657,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f44,f616])).

fof(f616,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f532,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f532,plain,(
    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f226,f528])).

fof(f528,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f464,f35])).

fof(f464,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f455,f161])).

fof(f161,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f154,f159])).

fof(f159,plain,(
    k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f158,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f99,f35])).

fof(f99,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f95,f94])).

fof(f94,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f92,f35])).

fof(f92,plain,(
    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) ),
    inference(resolution,[],[f81,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f79,f56])).

fof(f56,plain,(
    k1_xboole_0 = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ) ),
    inference(forward_demodulation,[],[f69,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f52,f40])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f81,plain,(
    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[],[f75,f56])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f58,f41])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f95,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),X0),k1_xboole_0) ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f158,plain,(
    k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f148,f56])).

fof(f148,plain,(
    k4_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f76,f94])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f57,f41])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f36,f40,f40])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f154,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f145,f143])).

fof(f143,plain,(
    k2_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f38,f94])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f145,plain,(
    k4_xboole_0(k2_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f41,f94])).

fof(f455,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f75,f143])).

fof(f226,plain,(
    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f216,f109])).

fof(f216,plain,(
    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f82,f56])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f75,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f647,plain,
    ( k1_xboole_0 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f60,f616])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f55,f55])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f1018,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f73,f760])).

fof(f73,plain,(
    ! [X4,X1] : r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:53:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (28678)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (28698)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (28702)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (28679)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.53  % (28676)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.53  % (28675)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (28675)Refutation not found, incomplete strategy% (28675)------------------------------
% 1.23/0.53  % (28675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (28675)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (28675)Memory used [KB]: 1663
% 1.23/0.53  % (28675)Time elapsed: 0.098 s
% 1.23/0.53  % (28675)------------------------------
% 1.23/0.53  % (28675)------------------------------
% 1.23/0.53  % (28694)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.53  % (28682)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.53  % (28696)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.53  % (28686)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.53  % (28686)Refutation not found, incomplete strategy% (28686)------------------------------
% 1.23/0.53  % (28686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (28686)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (28686)Memory used [KB]: 10618
% 1.23/0.53  % (28686)Time elapsed: 0.108 s
% 1.23/0.53  % (28686)------------------------------
% 1.23/0.53  % (28686)------------------------------
% 1.23/0.54  % (28689)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.54  % (28680)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.54  % (28684)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.54  % (28687)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.54  % (28677)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.54  % (28688)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.55  % (28700)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (28700)Refutation not found, incomplete strategy% (28700)------------------------------
% 1.34/0.55  % (28700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28700)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28700)Memory used [KB]: 6140
% 1.34/0.55  % (28700)Time elapsed: 0.129 s
% 1.34/0.55  % (28700)------------------------------
% 1.34/0.55  % (28700)------------------------------
% 1.34/0.55  % (28693)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.55  % (28701)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.55  % (28699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.55  % (28703)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.55  % (28701)Refutation not found, incomplete strategy% (28701)------------------------------
% 1.34/0.55  % (28701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28701)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28701)Memory used [KB]: 6140
% 1.34/0.55  % (28701)Time elapsed: 0.132 s
% 1.34/0.55  % (28701)------------------------------
% 1.34/0.55  % (28701)------------------------------
% 1.34/0.55  % (28699)Refutation not found, incomplete strategy% (28699)------------------------------
% 1.34/0.55  % (28699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28699)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28699)Memory used [KB]: 6140
% 1.34/0.55  % (28699)Time elapsed: 0.130 s
% 1.34/0.55  % (28699)------------------------------
% 1.34/0.55  % (28699)------------------------------
% 1.34/0.55  % (28703)Refutation not found, incomplete strategy% (28703)------------------------------
% 1.34/0.55  % (28703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28703)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28703)Memory used [KB]: 1663
% 1.34/0.55  % (28703)Time elapsed: 0.001 s
% 1.34/0.55  % (28703)------------------------------
% 1.34/0.55  % (28703)------------------------------
% 1.34/0.55  % (28674)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.56  % (28695)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.56  % (28691)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.56  % (28692)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.56  % (28691)Refutation not found, incomplete strategy% (28691)------------------------------
% 1.34/0.56  % (28691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28691)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28691)Memory used [KB]: 1663
% 1.34/0.56  % (28691)Time elapsed: 0.141 s
% 1.34/0.56  % (28691)------------------------------
% 1.34/0.56  % (28691)------------------------------
% 1.34/0.56  % (28683)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.56  % (28692)Refutation not found, incomplete strategy% (28692)------------------------------
% 1.34/0.56  % (28692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28692)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28692)Memory used [KB]: 1663
% 1.34/0.56  % (28692)Time elapsed: 0.140 s
% 1.34/0.56  % (28692)------------------------------
% 1.34/0.56  % (28692)------------------------------
% 1.34/0.56  % (28685)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.56  % (28685)Refutation not found, incomplete strategy% (28685)------------------------------
% 1.34/0.56  % (28685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28688)Refutation not found, incomplete strategy% (28688)------------------------------
% 1.34/0.56  % (28688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28688)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28688)Memory used [KB]: 1663
% 1.34/0.56  % (28688)Time elapsed: 0.144 s
% 1.34/0.56  % (28688)------------------------------
% 1.34/0.56  % (28688)------------------------------
% 1.34/0.56  % (28685)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28685)Memory used [KB]: 6140
% 1.34/0.56  % (28685)Time elapsed: 0.143 s
% 1.34/0.56  % (28685)------------------------------
% 1.34/0.56  % (28685)------------------------------
% 1.34/0.56  % (28681)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.56  % (28697)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.56  % (28690)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.57  % (28690)Refutation not found, incomplete strategy% (28690)------------------------------
% 1.34/0.57  % (28690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (28690)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.58  
% 1.34/0.58  % (28690)Memory used [KB]: 10618
% 1.34/0.58  % (28690)Time elapsed: 0.154 s
% 1.34/0.58  % (28696)Refutation found. Thanks to Tanya!
% 1.34/0.58  % SZS status Theorem for theBenchmark
% 1.34/0.59  % (28690)------------------------------
% 1.34/0.59  % (28690)------------------------------
% 1.34/0.59  % SZS output start Proof for theBenchmark
% 1.34/0.59  fof(f1025,plain,(
% 1.34/0.59    $false),
% 1.34/0.59    inference(subsumption_resolution,[],[f1018,f772])).
% 1.34/0.59  fof(f772,plain,(
% 1.34/0.59    ~r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.59    inference(trivial_inequality_removal,[],[f768])).
% 1.34/0.59  fof(f768,plain,(
% 1.34/0.59    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.59    inference(backward_demodulation,[],[f647,f760])).
% 1.34/0.59  fof(f760,plain,(
% 1.34/0.59    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.34/0.59    inference(resolution,[],[f669,f34])).
% 1.34/0.59  fof(f34,plain,(
% 1.34/0.59    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.34/0.59    inference(cnf_transformation,[],[f18])).
% 1.34/0.59  fof(f18,plain,(
% 1.34/0.59    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.34/0.59    inference(ennf_transformation,[],[f9])).
% 1.34/0.59  fof(f9,axiom,(
% 1.34/0.59    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.34/0.59  fof(f669,plain,(
% 1.34/0.59    ~r2_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.34/0.59    inference(trivial_inequality_removal,[],[f657])).
% 1.34/0.59  fof(f657,plain,(
% 1.34/0.59    k1_xboole_0 != k1_xboole_0 | ~r2_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.34/0.59    inference(superposition,[],[f44,f616])).
% 1.34/0.59  fof(f616,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.34/0.59    inference(resolution,[],[f532,f35])).
% 1.34/0.59  fof(f35,plain,(
% 1.34/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.34/0.59    inference(cnf_transformation,[],[f19])).
% 1.34/0.59  fof(f19,plain,(
% 1.34/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.34/0.59    inference(ennf_transformation,[],[f7])).
% 1.34/0.59  fof(f7,axiom,(
% 1.34/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.34/0.59  fof(f532,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k1_xboole_0)),
% 1.34/0.59    inference(backward_demodulation,[],[f226,f528])).
% 1.34/0.59  fof(f528,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.34/0.59    inference(resolution,[],[f464,f35])).
% 1.34/0.59  fof(f464,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.34/0.59    inference(forward_demodulation,[],[f455,f161])).
% 1.34/0.59  fof(f161,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.34/0.59    inference(backward_demodulation,[],[f154,f159])).
% 1.34/0.59  fof(f159,plain,(
% 1.34/0.59    k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.34/0.59    inference(forward_demodulation,[],[f158,f109])).
% 1.34/0.59  fof(f109,plain,(
% 1.34/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.34/0.59    inference(resolution,[],[f99,f35])).
% 1.34/0.59  fof(f99,plain,(
% 1.34/0.59    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.34/0.59    inference(forward_demodulation,[],[f95,f94])).
% 1.34/0.59  fof(f94,plain,(
% 1.34/0.59    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.34/0.59    inference(resolution,[],[f92,f35])).
% 1.34/0.59  fof(f92,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)),
% 1.34/0.59    inference(resolution,[],[f81,f87])).
% 1.34/0.59  fof(f87,plain,(
% 1.34/0.59    ( ! [X0] : (~r1_tarski(X0,k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | r1_tarski(X0,k1_xboole_0)) )),
% 1.34/0.59    inference(superposition,[],[f79,f56])).
% 1.34/0.59  fof(f56,plain,(
% 1.34/0.59    k1_xboole_0 = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.34/0.59    inference(definition_unfolding,[],[f32,f55])).
% 1.34/0.59  fof(f55,plain,(
% 1.34/0.59    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.34/0.59    inference(definition_unfolding,[],[f33,f39])).
% 1.34/0.59  fof(f39,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f13])).
% 1.34/0.59  fof(f13,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).
% 1.34/0.59  fof(f33,plain,(
% 1.34/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f12])).
% 1.34/0.59  fof(f12,axiom,(
% 1.34/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.59  fof(f32,plain,(
% 1.34/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.59    inference(cnf_transformation,[],[f23])).
% 1.34/0.59  fof(f23,plain,(
% 1.34/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22])).
% 1.34/0.59  fof(f22,plain,(
% 1.34/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.59    introduced(choice_axiom,[])).
% 1.34/0.59  fof(f17,plain,(
% 1.34/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.34/0.59    inference(ennf_transformation,[],[f16])).
% 1.34/0.59  fof(f16,negated_conjecture,(
% 1.34/0.59    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.34/0.59    inference(negated_conjecture,[],[f15])).
% 1.34/0.59  fof(f15,conjecture,(
% 1.34/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.34/0.59  fof(f79,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)))) )),
% 1.34/0.59    inference(forward_demodulation,[],[f69,f41])).
% 1.34/0.59  fof(f41,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f8])).
% 1.34/0.59  fof(f8,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 1.34/0.59  fof(f69,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 1.34/0.59    inference(definition_unfolding,[],[f52,f40])).
% 1.34/0.59  fof(f40,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f2])).
% 1.34/0.59  fof(f2,axiom,(
% 1.34/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.34/0.59  fof(f52,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f31])).
% 1.34/0.59  fof(f31,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.34/0.59    inference(flattening,[],[f30])).
% 1.34/0.59  fof(f30,plain,(
% 1.34/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.34/0.59    inference(nnf_transformation,[],[f4])).
% 1.34/0.59  fof(f4,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.34/0.59  fof(f81,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.34/0.59    inference(superposition,[],[f75,f56])).
% 1.34/0.59  fof(f75,plain,(
% 1.34/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 1.34/0.59    inference(backward_demodulation,[],[f58,f41])).
% 1.34/0.59  fof(f58,plain,(
% 1.34/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 1.34/0.59    inference(definition_unfolding,[],[f37,f40])).
% 1.34/0.59  fof(f37,plain,(
% 1.34/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(cnf_transformation,[],[f10])).
% 1.34/0.59  fof(f10,axiom,(
% 1.34/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 1.34/0.59  fof(f95,plain,(
% 1.34/0.59    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),X0),k1_xboole_0)) )),
% 1.34/0.59    inference(resolution,[],[f92,f45])).
% 1.34/0.59  fof(f45,plain,(
% 1.34/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f21])).
% 1.34/0.59  fof(f21,plain,(
% 1.34/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.34/0.59    inference(ennf_transformation,[],[f5])).
% 1.34/0.59  fof(f5,axiom,(
% 1.34/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.34/0.59  fof(f158,plain,(
% 1.34/0.59    k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.34/0.59    inference(forward_demodulation,[],[f148,f56])).
% 1.34/0.59  fof(f148,plain,(
% 1.34/0.59    k4_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.34/0.59    inference(superposition,[],[f76,f94])).
% 1.34/0.59  fof(f76,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(backward_demodulation,[],[f57,f41])).
% 1.34/0.59  fof(f57,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) )),
% 1.34/0.59    inference(definition_unfolding,[],[f36,f40,f40])).
% 1.34/0.59  fof(f36,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f1])).
% 1.34/0.59  fof(f1,axiom,(
% 1.34/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.34/0.59  fof(f154,plain,(
% 1.34/0.59    k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.34/0.59    inference(forward_demodulation,[],[f145,f143])).
% 1.34/0.59  fof(f143,plain,(
% 1.34/0.59    k2_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.34/0.59    inference(superposition,[],[f38,f94])).
% 1.34/0.59  fof(f38,plain,(
% 1.34/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.34/0.59    inference(cnf_transformation,[],[f6])).
% 1.34/0.59  fof(f6,axiom,(
% 1.34/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.34/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.34/0.59  fof(f145,plain,(
% 1.34/0.59    k4_xboole_0(k2_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.34/0.59    inference(superposition,[],[f41,f94])).
% 1.34/0.59  fof(f455,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.34/0.59    inference(superposition,[],[f75,f143])).
% 1.34/0.59  fof(f226,plain,(
% 1.34/0.59    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 1.34/0.59    inference(forward_demodulation,[],[f216,f109])).
% 1.34/0.60  fof(f216,plain,(
% 1.34/0.60    r1_tarski(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 1.34/0.60    inference(superposition,[],[f82,f56])).
% 1.34/0.60  fof(f82,plain,(
% 1.34/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 1.34/0.60    inference(superposition,[],[f75,f38])).
% 1.34/0.60  fof(f44,plain,(
% 1.34/0.60    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f20])).
% 1.34/0.60  fof(f20,plain,(
% 1.34/0.60    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 1.34/0.60    inference(ennf_transformation,[],[f3])).
% 1.34/0.60  fof(f3,axiom,(
% 1.34/0.60    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 1.34/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 1.34/0.60  fof(f647,plain,(
% 1.34/0.60    k1_xboole_0 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.60    inference(superposition,[],[f60,f616])).
% 1.34/0.60  fof(f60,plain,(
% 1.34/0.60    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.34/0.60    inference(definition_unfolding,[],[f42,f55,f55])).
% 1.34/0.60  fof(f42,plain,(
% 1.34/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f24])).
% 1.34/0.60  fof(f24,plain,(
% 1.34/0.60    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.34/0.60    inference(nnf_transformation,[],[f14])).
% 1.34/0.60  fof(f14,axiom,(
% 1.34/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.34/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.34/0.60  fof(f1018,plain,(
% 1.34/0.60    r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.60    inference(superposition,[],[f73,f760])).
% 1.34/0.60  fof(f73,plain,(
% 1.34/0.60    ( ! [X4,X1] : (r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1))) )),
% 1.34/0.60    inference(equality_resolution,[],[f72])).
% 1.34/0.60  fof(f72,plain,(
% 1.34/0.60    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2) )),
% 1.34/0.60    inference(equality_resolution,[],[f65])).
% 1.34/0.60  fof(f65,plain,(
% 1.34/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.34/0.60    inference(definition_unfolding,[],[f47,f39])).
% 1.34/0.60  fof(f47,plain,(
% 1.34/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.34/0.60    inference(cnf_transformation,[],[f29])).
% 1.34/0.60  fof(f29,plain,(
% 1.34/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.34/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.34/0.60  fof(f28,plain,(
% 1.34/0.60    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.34/0.60    introduced(choice_axiom,[])).
% 1.34/0.60  fof(f27,plain,(
% 1.34/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.34/0.60    inference(rectify,[],[f26])).
% 1.34/0.60  fof(f26,plain,(
% 1.34/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.34/0.60    inference(flattening,[],[f25])).
% 1.34/0.60  fof(f25,plain,(
% 1.34/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.34/0.60    inference(nnf_transformation,[],[f11])).
% 1.34/0.60  fof(f11,axiom,(
% 1.34/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.34/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.34/0.60  % SZS output end Proof for theBenchmark
% 1.34/0.60  % (28696)------------------------------
% 1.34/0.60  % (28696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.60  % (28696)Termination reason: Refutation
% 1.34/0.60  
% 1.34/0.60  % (28696)Memory used [KB]: 6908
% 1.34/0.60  % (28696)Time elapsed: 0.109 s
% 1.34/0.60  % (28696)------------------------------
% 1.34/0.60  % (28696)------------------------------
% 1.34/0.60  % (28670)Success in time 0.218 s
%------------------------------------------------------------------------------
