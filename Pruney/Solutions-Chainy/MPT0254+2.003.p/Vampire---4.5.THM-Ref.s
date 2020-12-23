%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 615 expanded)
%              Number of leaves         :   21 ( 202 expanded)
%              Depth                    :   23
%              Number of atoms          :  159 ( 731 expanded)
%              Number of equality atoms :   95 ( 623 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f671,plain,(
    $false ),
    inference(resolution,[],[f666,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f666,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f86,f659])).

fof(f659,plain,(
    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f68,f658])).

fof(f658,plain,(
    k1_xboole_0 = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f344,f657])).

fof(f657,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f656,f45])).

fof(f45,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f656,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f651,f344])).

fof(f651,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f650,f267])).

fof(f267,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f101,f266])).

fof(f266,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f260,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f260,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f65,f101])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f101,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f69,f73])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f650,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_enumset1(X0,X0,X0,X0)) ),
    inference(forward_demodulation,[],[f215,f266])).

fof(f215,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0)) ),
    inference(forward_demodulation,[],[f194,f76])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f194,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(superposition,[],[f67,f43])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f62,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f344,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f337,f43])).

fof(f337,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f240,f329])).

fof(f329,plain,(
    sK1 = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f328,f315])).

fof(f315,plain,(
    sK1 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(forward_demodulation,[],[f312,f42])).

fof(f312,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f121,f311])).

fof(f311,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(forward_demodulation,[],[f111,f65])).

fof(f111,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) ),
    inference(superposition,[],[f50,f88])).

fof(f88,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(forward_demodulation,[],[f66,f51])).

fof(f66,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f37,f62,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f121,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f105,f76])).

fof(f105,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f50,f43])).

fof(f328,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f320,f177])).

fof(f177,plain,(
    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f169,f42])).

fof(f169,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f160,f43])).

fof(f160,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0)) = X0 ),
    inference(forward_demodulation,[],[f159,f76])).

fof(f159,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[],[f50,f144])).

fof(f144,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f88,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f47,f47])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f320,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f70,f315])).

fof(f240,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f230,f42])).

fof(f230,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f189,f43])).

fof(f189,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) = X0 ),
    inference(forward_demodulation,[],[f184,f50])).

fof(f184,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = X0 ),
    inference(backward_demodulation,[],[f160,f177])).

fof(f68,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f41,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f86,plain,(
    ! [X4] : ~ r1_tarski(k1_zfmisc_1(X4),X4) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(factoring,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f71,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (5874)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.47  % (5882)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (5864)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (5891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (5863)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (5867)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (5872)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (5873)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (5868)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (5885)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (5879)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (5877)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (5879)Refutation not found, incomplete strategy% (5879)------------------------------
% 0.20/0.53  % (5879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5879)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5879)Memory used [KB]: 10618
% 0.20/0.53  % (5879)Time elapsed: 0.109 s
% 0.20/0.53  % (5879)------------------------------
% 0.20/0.53  % (5879)------------------------------
% 0.20/0.53  % (5890)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (5883)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (5889)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (5884)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (5886)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (5875)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (5875)Refutation not found, incomplete strategy% (5875)------------------------------
% 0.20/0.53  % (5875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5875)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5875)Memory used [KB]: 10618
% 0.20/0.53  % (5875)Time elapsed: 0.126 s
% 0.20/0.53  % (5875)------------------------------
% 0.20/0.53  % (5875)------------------------------
% 0.20/0.53  % (5880)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (5887)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (5881)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (5876)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (5865)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (5866)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (5892)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (5892)Refutation not found, incomplete strategy% (5892)------------------------------
% 0.20/0.54  % (5892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5892)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5892)Memory used [KB]: 1663
% 0.20/0.54  % (5892)Time elapsed: 0.001 s
% 0.20/0.54  % (5892)------------------------------
% 0.20/0.54  % (5892)------------------------------
% 0.20/0.54  % (5871)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (5877)Refutation not found, incomplete strategy% (5877)------------------------------
% 0.20/0.54  % (5877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5877)Memory used [KB]: 1663
% 0.20/0.54  % (5877)Time elapsed: 0.095 s
% 0.20/0.54  % (5877)------------------------------
% 0.20/0.54  % (5877)------------------------------
% 0.20/0.54  % (5869)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (5888)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (5878)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (5889)Refutation not found, incomplete strategy% (5889)------------------------------
% 0.20/0.55  % (5889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5889)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5889)Memory used [KB]: 6140
% 0.20/0.55  % (5889)Time elapsed: 0.132 s
% 0.20/0.55  % (5889)------------------------------
% 0.20/0.55  % (5889)------------------------------
% 0.20/0.55  % (5870)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (5881)Refutation not found, incomplete strategy% (5881)------------------------------
% 0.20/0.56  % (5881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5881)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5881)Memory used [KB]: 1663
% 0.20/0.56  % (5881)Time elapsed: 0.152 s
% 0.20/0.56  % (5881)------------------------------
% 0.20/0.56  % (5881)------------------------------
% 0.20/0.57  % (5868)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f671,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(resolution,[],[f666,f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.58    inference(equality_resolution,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f666,plain,(
% 0.20/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    inference(superposition,[],[f86,f659])).
% 0.20/0.58  fof(f659,plain,(
% 0.20/0.58    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 0.20/0.58    inference(backward_demodulation,[],[f68,f658])).
% 0.20/0.58  fof(f658,plain,(
% 0.20/0.58    k1_xboole_0 = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    inference(backward_demodulation,[],[f344,f657])).
% 0.20/0.58  fof(f657,plain,(
% 0.20/0.58    k1_xboole_0 = sK0),
% 0.20/0.58    inference(forward_demodulation,[],[f656,f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,axiom,(
% 0.20/0.58    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.20/0.58  fof(f656,plain,(
% 0.20/0.58    k3_tarski(k1_xboole_0) = sK0),
% 0.20/0.58    inference(superposition,[],[f651,f344])).
% 0.20/0.58  fof(f651,plain,(
% 0.20/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.58    inference(forward_demodulation,[],[f650,f267])).
% 0.20/0.58  fof(f267,plain,(
% 0.20/0.58    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.20/0.58    inference(backward_demodulation,[],[f101,f266])).
% 0.20/0.58  fof(f266,plain,(
% 0.20/0.58    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f260,f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.58  fof(f260,plain,(
% 0.20/0.58    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) )),
% 0.20/0.58    inference(superposition,[],[f65,f101])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f48,f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 0.20/0.58    inference(resolution,[],[f69,f73])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f46,f47])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.58  fof(f650,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f215,f266])).
% 0.20/0.58  fof(f215,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f194,f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.58    inference(superposition,[],[f51,f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.58  fof(f194,plain,(
% 0.20/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 0.20/0.58    inference(superposition,[],[f67,f43])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f39,f62,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f52,f60])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f38,f47])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.58  fof(f344,plain,(
% 0.20/0.58    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.58    inference(forward_demodulation,[],[f337,f43])).
% 0.20/0.58  fof(f337,plain,(
% 0.20/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,sK1)),
% 0.20/0.58    inference(backward_demodulation,[],[f240,f329])).
% 0.20/0.58  fof(f329,plain,(
% 0.20/0.58    sK1 = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f328,f315])).
% 0.20/0.58  fof(f315,plain,(
% 0.20/0.58    sK1 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.58    inference(forward_demodulation,[],[f312,f42])).
% 0.20/0.58  fof(f312,plain,(
% 0.20/0.58    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.58    inference(superposition,[],[f121,f311])).
% 0.20/0.58  fof(f311,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.58    inference(forward_demodulation,[],[f111,f65])).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))),
% 0.20/0.58    inference(superposition,[],[f50,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f66,f51])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.58    inference(definition_unfolding,[],[f37,f62,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f40,f63])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.58    inference(ennf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.58    inference(negated_conjecture,[],[f24])).
% 0.20/0.58  fof(f24,conjecture,(
% 0.20/0.58    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.58  fof(f121,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 0.20/0.58    inference(forward_demodulation,[],[f105,f76])).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 0.20/0.58    inference(superposition,[],[f50,f43])).
% 0.20/0.58  fof(f328,plain,(
% 0.20/0.58    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f320,f177])).
% 0.20/0.58  fof(f177,plain,(
% 0.20/0.58    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.58    inference(forward_demodulation,[],[f169,f42])).
% 0.20/0.58  fof(f169,plain,(
% 0.20/0.58    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.20/0.58    inference(superposition,[],[f160,f43])).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0)) = X0) )),
% 0.20/0.58    inference(forward_demodulation,[],[f159,f76])).
% 0.20/0.58  fof(f159,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X0))) )),
% 0.20/0.58    inference(superposition,[],[f50,f144])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.20/0.58    inference(backward_demodulation,[],[f88,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f49,f47,f47])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.58  fof(f320,plain,(
% 0.20/0.58    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.58    inference(superposition,[],[f70,f315])).
% 0.20/0.58  fof(f240,plain,(
% 0.20/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.20/0.58    inference(forward_demodulation,[],[f230,f42])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0))),
% 0.20/0.58    inference(superposition,[],[f189,f43])).
% 0.20/0.58  fof(f189,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) = X0) )),
% 0.20/0.58    inference(forward_demodulation,[],[f184,f50])).
% 0.20/0.58  fof(f184,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = X0) )),
% 0.20/0.58    inference(backward_demodulation,[],[f160,f177])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    inference(definition_unfolding,[],[f41,f64])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,axiom,(
% 0.20/0.58    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X4] : (~r1_tarski(k1_zfmisc_1(X4),X4)) )),
% 0.20/0.58    inference(resolution,[],[f71,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.20/0.58    inference(factoring,[],[f61])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(rectify,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,axiom,(
% 0.20/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (5868)------------------------------
% 0.20/0.58  % (5868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (5868)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (5868)Memory used [KB]: 2174
% 0.20/0.58  % (5868)Time elapsed: 0.161 s
% 0.20/0.58  % (5868)------------------------------
% 0.20/0.58  % (5868)------------------------------
% 0.20/0.58  % (5862)Success in time 0.215 s
%------------------------------------------------------------------------------
