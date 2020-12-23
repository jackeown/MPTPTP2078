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
% DateTime   : Thu Dec  3 12:39:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  121 (2482 expanded)
%              Number of leaves         :   25 ( 825 expanded)
%              Depth                    :   38
%              Number of atoms          :  236 (2626 expanded)
%              Number of equality atoms :  171 (2555 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f969,plain,(
    $false ),
    inference(resolution,[],[f963,f693])).

fof(f693,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(global_subsumption,[],[f643,f690])).

fof(f690,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f54,f661])).

fof(f661,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f657,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f657,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f586,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f586,plain,(
    ! [X7] : r1_tarski(k3_xboole_0(k1_xboole_0,X7),k1_xboole_0) ),
    inference(superposition,[],[f78,f517])).

fof(f517,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(forward_demodulation,[],[f509,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f509,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f497,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f497,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f482,f118])).

fof(f118,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) ),
    inference(forward_demodulation,[],[f116,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[],[f57,f103])).

fof(f103,plain,(
    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f98,f47])).

fof(f98,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f97,f47])).

fof(f97,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f77,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f39,f75,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f74])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f482,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f462,f426])).

fof(f426,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f156,f136])).

fof(f136,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(forward_demodulation,[],[f133,f57])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[],[f57,f129])).

fof(f129,plain,(
    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f120,f43])).

fof(f120,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f107,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f57,f98])).

fof(f156,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f118,f115])).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) ),
    inference(forward_demodulation,[],[f112,f57])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[],[f57,f102])).

fof(f102,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f98,f57])).

fof(f462,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(backward_demodulation,[],[f107,f452])).

fof(f452,plain,(
    k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f451,f43])).

fof(f451,plain,(
    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f430,f43])).

fof(f430,plain,(
    k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f426,f42])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f643,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f641,f41])).

fof(f641,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f583,f46])).

fof(f583,plain,(
    ! [X4] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) ),
    inference(superposition,[],[f48,f517])).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f963,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f93,f948])).

fof(f948,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f945,f43])).

fof(f945,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f944,f43])).

fof(f944,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f942,f41])).

fof(f942,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f931,f79])).

fof(f931,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f77,f921])).

fof(f921,plain,(
    k1_xboole_0 = sK1 ),
    inference(superposition,[],[f905,f43])).

fof(f905,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f883,f42])).

fof(f883,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f102,f840])).

fof(f840,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f752,f46])).

fof(f752,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f574,f55])).

fof(f574,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f343,f517])).

fof(f343,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f78,f188])).

fof(f188,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f162,f47])).

fof(f162,plain,(
    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(forward_demodulation,[],[f151,f43])).

fof(f151,plain,(
    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f118,f42])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (15751)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (15742)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (15737)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (15743)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (15743)Refutation not found, incomplete strategy% (15743)------------------------------
% 0.21/0.51  % (15743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15743)Memory used [KB]: 6140
% 0.21/0.51  % (15743)Time elapsed: 0.001 s
% 0.21/0.51  % (15743)------------------------------
% 0.21/0.51  % (15743)------------------------------
% 0.21/0.51  % (15728)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (15746)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (15734)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (15738)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (15735)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15730)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15732)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15733)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15738)Refutation not found, incomplete strategy% (15738)------------------------------
% 0.21/0.52  % (15738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15738)Memory used [KB]: 10618
% 0.21/0.52  % (15738)Time elapsed: 0.079 s
% 0.21/0.52  % (15738)------------------------------
% 0.21/0.52  % (15738)------------------------------
% 0.21/0.52  % (15750)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15736)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15749)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (15754)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (15751)Refutation not found, incomplete strategy% (15751)------------------------------
% 0.21/0.52  % (15751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15751)Memory used [KB]: 1663
% 0.21/0.52  % (15751)Time elapsed: 0.112 s
% 0.21/0.52  % (15751)------------------------------
% 0.21/0.52  % (15751)------------------------------
% 0.21/0.53  % (15744)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15745)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15747)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15745)Refutation not found, incomplete strategy% (15745)------------------------------
% 0.21/0.53  % (15745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15745)Memory used [KB]: 10618
% 0.21/0.53  % (15745)Time elapsed: 0.123 s
% 0.21/0.53  % (15745)------------------------------
% 0.21/0.53  % (15745)------------------------------
% 0.21/0.53  % (15757)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (15740)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15739)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (15729)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15731)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (15741)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (15753)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15756)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (15752)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (15755)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15732)Refutation not found, incomplete strategy% (15732)------------------------------
% 0.21/0.54  % (15732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15732)Memory used [KB]: 6396
% 0.21/0.54  % (15732)Time elapsed: 0.114 s
% 0.21/0.54  % (15732)------------------------------
% 0.21/0.54  % (15732)------------------------------
% 0.21/0.54  % (15748)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15748)Refutation not found, incomplete strategy% (15748)------------------------------
% 0.21/0.55  % (15748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15748)Memory used [KB]: 10746
% 0.21/0.56  % (15748)Time elapsed: 0.142 s
% 0.21/0.56  % (15748)------------------------------
% 0.21/0.56  % (15748)------------------------------
% 0.21/0.57  % (15730)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.59  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f969,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(resolution,[],[f963,f693])).
% 1.59/0.59  fof(f693,plain,(
% 1.59/0.59    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.59/0.59    inference(global_subsumption,[],[f643,f690])).
% 1.59/0.59  fof(f690,plain,(
% 1.59/0.59    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X4)) )),
% 1.59/0.59    inference(superposition,[],[f54,f661])).
% 1.59/0.59  fof(f661,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.59    inference(forward_demodulation,[],[f657,f41])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f7])).
% 1.59/0.59  fof(f7,axiom,(
% 1.59/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.59/0.59  fof(f657,plain,(
% 1.59/0.59    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.59/0.59    inference(resolution,[],[f586,f55])).
% 1.59/0.59  fof(f55,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.59    inference(ennf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.59  fof(f586,plain,(
% 1.59/0.59    ( ! [X7] : (r1_tarski(k3_xboole_0(k1_xboole_0,X7),k1_xboole_0)) )),
% 1.59/0.59    inference(superposition,[],[f78,f517])).
% 1.59/0.59  fof(f517,plain,(
% 1.59/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.59/0.59    inference(forward_demodulation,[],[f509,f43])).
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f10])).
% 1.59/0.59  fof(f10,axiom,(
% 1.59/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.59/0.59  fof(f509,plain,(
% 1.59/0.59    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0))) )),
% 1.59/0.59    inference(superposition,[],[f497,f47])).
% 1.59/0.59  fof(f47,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f2])).
% 1.59/0.59  fof(f2,axiom,(
% 1.59/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.59/0.59  fof(f497,plain,(
% 1.59/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) )),
% 1.59/0.59    inference(forward_demodulation,[],[f482,f118])).
% 1.59/0.59  fof(f118,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) )),
% 1.59/0.59    inference(forward_demodulation,[],[f116,f57])).
% 1.59/0.59  fof(f57,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.59/0.59  fof(f116,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) )),
% 1.59/0.59    inference(superposition,[],[f57,f103])).
% 1.59/0.59  fof(f103,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(superposition,[],[f98,f47])).
% 1.59/0.59  fof(f98,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(forward_demodulation,[],[f97,f47])).
% 1.59/0.59  fof(f97,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(forward_demodulation,[],[f95,f46])).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.59  fof(f95,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.59/0.59    inference(superposition,[],[f77,f79])).
% 1.59/0.59  fof(f79,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f52,f75])).
% 1.59/0.59  fof(f75,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f49,f74])).
% 1.59/0.59  fof(f74,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f50,f73])).
% 1.59/0.59  fof(f73,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f56,f72])).
% 1.59/0.59  fof(f72,plain,(
% 1.59/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f58,f71])).
% 1.59/0.59  fof(f71,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f67,f70])).
% 1.59/0.59  fof(f70,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f68,f69])).
% 1.59/0.59  fof(f69,plain,(
% 1.59/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  fof(f20,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.59/0.59  fof(f67,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f19,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.59/0.59  fof(f58,plain,(
% 1.59/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f18])).
% 1.59/0.59  fof(f18,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f17])).
% 1.59/0.59  fof(f17,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.59  fof(f50,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,axiom,(
% 1.59/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.59  fof(f49,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f22])).
% 1.59/0.59  fof(f22,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f13])).
% 1.59/0.59  fof(f13,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.59/0.59  fof(f77,plain,(
% 1.59/0.59    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.59/0.59    inference(definition_unfolding,[],[f39,f75,f76])).
% 1.59/0.59  fof(f76,plain,(
% 1.59/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f44,f74])).
% 1.59/0.59  fof(f44,plain,(
% 1.59/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f15])).
% 1.59/0.59  fof(f15,axiom,(
% 1.59/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f31])).
% 1.59/0.59  fof(f31,plain,(
% 1.59/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30])).
% 1.59/0.59  fof(f30,plain,(
% 1.59/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.59/0.59    inference(ennf_transformation,[],[f24])).
% 1.59/0.59  fof(f24,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.59/0.59    inference(negated_conjecture,[],[f23])).
% 1.59/0.59  fof(f23,conjecture,(
% 1.59/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.59/0.59  fof(f482,plain,(
% 1.59/0.59    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X2))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) )),
% 1.59/0.59    inference(superposition,[],[f462,f426])).
% 1.59/0.59  fof(f426,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,X0))) )),
% 1.59/0.59    inference(forward_demodulation,[],[f156,f136])).
% 1.59/0.59  fof(f136,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) )),
% 1.59/0.59    inference(forward_demodulation,[],[f133,f57])).
% 1.59/0.59  fof(f133,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) )),
% 1.59/0.59    inference(superposition,[],[f57,f129])).
% 1.59/0.59  fof(f129,plain,(
% 1.59/0.59    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(forward_demodulation,[],[f120,f43])).
% 1.59/0.59  fof(f120,plain,(
% 1.59/0.59    k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(superposition,[],[f107,f42])).
% 1.59/0.59  fof(f42,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f12])).
% 1.59/0.59  fof(f12,axiom,(
% 1.59/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.59/0.59  fof(f107,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.59    inference(superposition,[],[f57,f98])).
% 1.59/0.59  fof(f156,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k1_xboole_0,X0))) )),
% 1.59/0.59    inference(superposition,[],[f118,f115])).
% 1.59/0.59  fof(f115,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) )),
% 1.59/0.59    inference(forward_demodulation,[],[f112,f57])).
% 1.59/0.59  fof(f112,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))) )),
% 1.59/0.59    inference(superposition,[],[f57,f102])).
% 1.59/0.59  fof(f102,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.59/0.59    inference(superposition,[],[f98,f57])).
% 1.59/0.59  fof(f462,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) )),
% 1.59/0.59    inference(backward_demodulation,[],[f107,f452])).
% 1.59/0.59  fof(f452,plain,(
% 1.59/0.59    k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.59/0.59    inference(forward_demodulation,[],[f451,f43])).
% 1.59/0.59  fof(f451,plain,(
% 1.59/0.59    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.59/0.59    inference(forward_demodulation,[],[f430,f43])).
% 1.59/0.59  fof(f430,plain,(
% 1.59/0.59    k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.59/0.59    inference(superposition,[],[f426,f42])).
% 1.59/0.59  fof(f78,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f45,f51])).
% 1.59/0.59  fof(f51,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.59  fof(f45,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f33])).
% 1.59/0.59  fof(f33,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f32])).
% 1.59/0.59  fof(f32,plain,(
% 1.59/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f27,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(ennf_transformation,[],[f25])).
% 1.59/0.59  fof(f25,plain,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(rectify,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.59/0.59  fof(f643,plain,(
% 1.59/0.59    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.59    inference(forward_demodulation,[],[f641,f41])).
% 1.59/0.59  fof(f641,plain,(
% 1.59/0.59    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.59/0.59    inference(superposition,[],[f583,f46])).
% 1.59/0.59  fof(f583,plain,(
% 1.59/0.59    ( ! [X4] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4)) )),
% 1.59/0.59    inference(superposition,[],[f48,f517])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.59/0.59  fof(f963,plain,(
% 1.59/0.59    r2_hidden(sK0,k1_xboole_0)),
% 1.59/0.59    inference(superposition,[],[f93,f948])).
% 1.59/0.59  fof(f948,plain,(
% 1.59/0.59    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.59/0.59    inference(superposition,[],[f945,f43])).
% 1.59/0.59  fof(f945,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.59/0.59    inference(forward_demodulation,[],[f944,f43])).
% 1.59/0.59  fof(f944,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k1_xboole_0)),
% 1.59/0.59    inference(forward_demodulation,[],[f942,f41])).
% 1.59/0.59  fof(f942,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.59/0.59    inference(superposition,[],[f931,f79])).
% 1.59/0.59  fof(f931,plain,(
% 1.59/0.59    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.59/0.59    inference(backward_demodulation,[],[f77,f921])).
% 1.59/0.59  fof(f921,plain,(
% 1.59/0.59    k1_xboole_0 = sK1),
% 1.59/0.59    inference(superposition,[],[f905,f43])).
% 1.59/0.59  fof(f905,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.59/0.59    inference(forward_demodulation,[],[f883,f42])).
% 1.59/0.59  fof(f883,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(backward_demodulation,[],[f102,f840])).
% 1.59/0.59  fof(f840,plain,(
% 1.59/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.59/0.59    inference(superposition,[],[f752,f46])).
% 1.59/0.59  fof(f752,plain,(
% 1.59/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.59/0.59    inference(resolution,[],[f574,f55])).
% 1.59/0.59  fof(f574,plain,(
% 1.59/0.59    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.59/0.59    inference(backward_demodulation,[],[f343,f517])).
% 1.59/0.59  fof(f343,plain,(
% 1.59/0.59    r1_tarski(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 1.59/0.59    inference(superposition,[],[f78,f188])).
% 1.59/0.59  fof(f188,plain,(
% 1.59/0.59    k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.59/0.59    inference(superposition,[],[f162,f47])).
% 1.59/0.59  fof(f162,plain,(
% 1.59/0.59    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 1.59/0.59    inference(forward_demodulation,[],[f151,f43])).
% 1.59/0.59  fof(f151,plain,(
% 1.59/0.59    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(sK1,k1_xboole_0))),
% 1.59/0.59    inference(superposition,[],[f118,f42])).
% 1.59/0.59  fof(f93,plain,(
% 1.59/0.59    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 1.59/0.59    inference(equality_resolution,[],[f92])).
% 1.59/0.59  fof(f92,plain,(
% 1.59/0.59    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 1.59/0.59    inference(equality_resolution,[],[f86])).
% 1.59/0.59  fof(f86,plain,(
% 1.59/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.59/0.59    inference(definition_unfolding,[],[f60,f73])).
% 1.59/0.59  fof(f60,plain,(
% 1.59/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.59/0.59    inference(cnf_transformation,[],[f38])).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.59/0.59    inference(rectify,[],[f35])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.59/0.59    inference(flattening,[],[f34])).
% 1.59/0.59  fof(f34,plain,(
% 1.59/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.59/0.59    inference(nnf_transformation,[],[f29])).
% 1.59/0.59  fof(f29,plain,(
% 1.59/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.59/0.59    inference(ennf_transformation,[],[f14])).
% 1.59/0.59  fof(f14,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (15730)------------------------------
% 1.59/0.59  % (15730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (15730)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (15730)Memory used [KB]: 11513
% 1.59/0.59  % (15730)Time elapsed: 0.132 s
% 1.59/0.59  % (15730)------------------------------
% 1.59/0.59  % (15730)------------------------------
% 1.59/0.59  % (15727)Success in time 0.22 s
%------------------------------------------------------------------------------
