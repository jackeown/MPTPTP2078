%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:18 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  113 (2559 expanded)
%              Number of leaves         :   20 ( 882 expanded)
%              Depth                    :   28
%              Number of atoms          :  145 (2766 expanded)
%              Number of equality atoms :  132 (2753 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(subsumption_resolution,[],[f843,f79])).

fof(f79,plain,(
    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f73,f70])).

fof(f70,plain,(
    r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f36,f35,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f57,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f27,f35,f55,f55])).

fof(f27,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f73,plain,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f61,f57])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f38,f55,f35,f55])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f843,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f842,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f842,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f835,f472])).

fof(f472,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f463,f435])).

fof(f435,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f434,f116])).

fof(f116,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0) ),
    inference(forward_demodulation,[],[f110,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f110,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f56,f102])).

fof(f102,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f57,f90])).

fof(f90,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) ),
    inference(superposition,[],[f78,f30])).

fof(f78,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) ),
    inference(forward_demodulation,[],[f72,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f43,f52,f52])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f72,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f56,f57])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f48,f49,f47,f55])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f434,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f407,f121])).

fof(f121,plain,(
    ! [X0] : k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,X0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X0) ),
    inference(forward_demodulation,[],[f120,f56])).

fof(f120,plain,(
    ! [X0] : k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f56,f116])).

fof(f407,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f28,f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X0,X1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X0,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))
      | sK1 = X1
      | sK1 = X0 ) ),
    inference(backward_demodulation,[],[f136,f212])).

fof(f212,plain,(
    ! [X19,X18] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X18,X19) = k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X18,X19) ),
    inference(forward_demodulation,[],[f205,f56])).

fof(f205,plain,(
    ! [X19,X18] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X18,X19) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X18),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X18)))) ),
    inference(superposition,[],[f56,f144])).

fof(f144,plain,(
    ! [X14] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X14) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X14) ),
    inference(forward_demodulation,[],[f143,f56])).

fof(f143,plain,(
    ! [X14] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X14) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X14),k3_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X14),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f56,f90])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))
      | sK1 = X1
      | sK1 = X0 ) ),
    inference(superposition,[],[f62,f90])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f42,f35,f53,f55,f54])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f463,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f141,f90])).

fof(f141,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k6_enumset1(X6,X7,X8,X9,X10,X11,X12,sK1) = k5_xboole_0(k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X12),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X12)))) ),
    inference(superposition,[],[f56,f90])).

fof(f835,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f788,f148])).

fof(f148,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f41,f103])).

fof(f103,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f91,f90])).

fof(f91,plain,(
    k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) ),
    inference(superposition,[],[f78,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f788,plain,(
    ! [X0] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f301,f782])).

fof(f782,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f777,f30])).

fof(f777,plain,(
    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f760,f29])).

fof(f760,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0)) = X0 ),
    inference(backward_demodulation,[],[f97,f759])).

fof(f759,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(forward_demodulation,[],[f751,f30])).

fof(f751,plain,(
    ! [X6] : k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f732,f32])).

fof(f732,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) ),
    inference(backward_demodulation,[],[f329,f725])).

fof(f725,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f296,f32])).

fof(f296,plain,(
    ! [X8] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f276,f30])).

fof(f276,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f164,f127])).

fof(f127,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f122,f30])).

fof(f122,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f97,f29])).

fof(f164,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f124,f41])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f97,f32])).

fof(f329,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X8)) ),
    inference(superposition,[],[f173,f159])).

fof(f159,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0)) ),
    inference(superposition,[],[f41,f127])).

fof(f173,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X1))) ),
    inference(forward_demodulation,[],[f172,f41])).

fof(f172,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X1))) ),
    inference(forward_demodulation,[],[f169,f41])).

fof(f169,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),X1)) ),
    inference(superposition,[],[f41,f124])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0)) ),
    inference(backward_demodulation,[],[f76,f90])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f57])).

fof(f301,plain,(
    ! [X0] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) ),
    inference(forward_demodulation,[],[f300,f30])).

fof(f300,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) ),
    inference(forward_demodulation,[],[f280,f32])).

fof(f280,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),X0)) ),
    inference(superposition,[],[f164,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 12:14:00 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.52  % (20750)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.52  % (20748)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (20756)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.53  % (20746)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (20741)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (20760)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.54  % (20764)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (20741)Refutation not found, incomplete strategy% (20741)------------------------------
% 0.23/0.54  % (20741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (20741)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (20741)Memory used [KB]: 1663
% 0.23/0.54  % (20741)Time elapsed: 0.111 s
% 0.23/0.54  % (20741)------------------------------
% 0.23/0.54  % (20741)------------------------------
% 0.23/0.54  % (20745)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % (20744)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.54  % (20750)Refutation not found, incomplete strategy% (20750)------------------------------
% 0.23/0.54  % (20750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (20750)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (20750)Memory used [KB]: 10618
% 0.23/0.54  % (20750)Time elapsed: 0.112 s
% 0.23/0.54  % (20750)------------------------------
% 0.23/0.54  % (20750)------------------------------
% 0.23/0.54  % (20764)Refutation not found, incomplete strategy% (20764)------------------------------
% 0.23/0.54  % (20764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (20756)Refutation not found, incomplete strategy% (20756)------------------------------
% 0.23/0.54  % (20756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (20756)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (20756)Memory used [KB]: 6140
% 0.23/0.54  % (20756)Time elapsed: 0.003 s
% 0.23/0.54  % (20756)------------------------------
% 0.23/0.54  % (20756)------------------------------
% 0.23/0.54  % (20742)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (20764)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (20764)Memory used [KB]: 1663
% 0.23/0.54  % (20764)Time elapsed: 0.113 s
% 0.23/0.54  % (20764)------------------------------
% 0.23/0.54  % (20764)------------------------------
% 0.23/0.54  % (20754)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.55  % (20768)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.55  % (20743)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (20747)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (20770)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (20767)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (20763)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.55  % (20751)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.55  % (20757)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.56  % (20751)Refutation not found, incomplete strategy% (20751)------------------------------
% 0.23/0.56  % (20751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (20751)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (20751)Memory used [KB]: 10618
% 0.23/0.56  % (20751)Time elapsed: 0.134 s
% 0.23/0.56  % (20751)------------------------------
% 0.23/0.56  % (20751)------------------------------
% 0.23/0.56  % (20761)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.56  % (20762)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (20766)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (20761)Refutation not found, incomplete strategy% (20761)------------------------------
% 0.23/0.56  % (20761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (20761)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (20761)Memory used [KB]: 10746
% 0.23/0.56  % (20761)Time elapsed: 0.138 s
% 0.23/0.56  % (20761)------------------------------
% 0.23/0.56  % (20761)------------------------------
% 0.23/0.56  % (20759)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.56  % (20749)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.56  % (20755)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.57  % (20753)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.57  % (20752)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.57  % (20752)Refutation not found, incomplete strategy% (20752)------------------------------
% 0.23/0.57  % (20752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (20752)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (20752)Memory used [KB]: 10618
% 0.23/0.57  % (20752)Time elapsed: 0.148 s
% 0.23/0.57  % (20752)------------------------------
% 0.23/0.57  % (20752)------------------------------
% 0.23/0.57  % (20769)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.57  % (20758)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.57  % (20765)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.57  % (20758)Refutation not found, incomplete strategy% (20758)------------------------------
% 0.23/0.57  % (20758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (20758)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (20758)Memory used [KB]: 10618
% 0.23/0.57  % (20758)Time elapsed: 0.159 s
% 0.23/0.57  % (20758)------------------------------
% 0.23/0.57  % (20758)------------------------------
% 1.95/0.66  % (20774)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.95/0.68  % (20771)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.95/0.68  % (20771)Refutation not found, incomplete strategy% (20771)------------------------------
% 1.95/0.68  % (20771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.68  % (20771)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.68  
% 1.95/0.68  % (20771)Memory used [KB]: 6140
% 1.95/0.68  % (20771)Time elapsed: 0.109 s
% 1.95/0.68  % (20771)------------------------------
% 1.95/0.68  % (20771)------------------------------
% 1.95/0.68  % (20775)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.95/0.69  % (20773)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.95/0.70  % (20772)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.95/0.70  % (20767)Refutation found. Thanks to Tanya!
% 1.95/0.70  % SZS status Theorem for theBenchmark
% 1.95/0.70  % SZS output start Proof for theBenchmark
% 1.95/0.70  fof(f844,plain,(
% 1.95/0.70    $false),
% 1.95/0.70    inference(subsumption_resolution,[],[f843,f79])).
% 1.95/0.70  fof(f79,plain,(
% 1.95/0.70    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.95/0.70    inference(subsumption_resolution,[],[f73,f70])).
% 1.95/0.70  fof(f70,plain,(
% 1.95/0.70    r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.95/0.70    inference(unit_resulting_resolution,[],[f57,f59])).
% 1.95/0.70  fof(f59,plain,(
% 1.95/0.70    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 1.95/0.70    inference(definition_unfolding,[],[f36,f35,f55])).
% 1.95/0.70  fof(f55,plain,(
% 1.95/0.70    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f31,f54])).
% 1.95/0.70  fof(f54,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f33,f53])).
% 1.95/0.70  fof(f53,plain,(
% 1.95/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f40,f52])).
% 1.95/0.70  fof(f52,plain,(
% 1.95/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f44,f51])).
% 1.95/0.70  fof(f51,plain,(
% 1.95/0.70    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f45,f50])).
% 1.95/0.70  fof(f50,plain,(
% 1.95/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f46,f47])).
% 1.95/0.70  fof(f47,plain,(
% 1.95/0.70    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f16])).
% 1.95/0.70  fof(f16,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.95/0.70  fof(f46,plain,(
% 1.95/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f15])).
% 1.95/0.70  fof(f15,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.95/0.70  fof(f45,plain,(
% 1.95/0.70    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f14])).
% 1.95/0.70  fof(f14,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.95/0.70  fof(f44,plain,(
% 1.95/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f13])).
% 1.95/0.70  fof(f13,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.95/0.70  fof(f40,plain,(
% 1.95/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f12])).
% 1.95/0.70  fof(f12,axiom,(
% 1.95/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.95/0.70  fof(f33,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f11])).
% 1.95/0.70  fof(f11,axiom,(
% 1.95/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.95/0.70  fof(f31,plain,(
% 1.95/0.70    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f10])).
% 1.95/0.70  fof(f10,axiom,(
% 1.95/0.70    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.95/0.70  fof(f35,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.95/0.70    inference(cnf_transformation,[],[f2])).
% 1.95/0.70  fof(f2,axiom,(
% 1.95/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.95/0.70  fof(f36,plain,(
% 1.95/0.70    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f25])).
% 1.95/0.70  fof(f25,plain,(
% 1.95/0.70    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.95/0.70    inference(nnf_transformation,[],[f18])).
% 1.95/0.70  fof(f18,axiom,(
% 1.95/0.70    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.95/0.70  fof(f57,plain,(
% 1.95/0.70    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.95/0.70    inference(definition_unfolding,[],[f27,f35,f55,f55])).
% 1.95/0.70  fof(f27,plain,(
% 1.95/0.70    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.95/0.70    inference(cnf_transformation,[],[f24])).
% 1.95/0.70  fof(f24,plain,(
% 1.95/0.70    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.95/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.95/0.70  fof(f23,plain,(
% 1.95/0.70    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.95/0.70    introduced(choice_axiom,[])).
% 1.95/0.70  fof(f21,plain,(
% 1.95/0.70    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.95/0.70    inference(ennf_transformation,[],[f20])).
% 1.95/0.70  fof(f20,negated_conjecture,(
% 1.95/0.70    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.95/0.70    inference(negated_conjecture,[],[f19])).
% 1.95/0.70  fof(f19,conjecture,(
% 1.95/0.70    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.95/0.70  fof(f73,plain,(
% 1.95/0.70    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.95/0.70    inference(superposition,[],[f61,f57])).
% 1.95/0.70  fof(f61,plain,(
% 1.95/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 1.95/0.70    inference(definition_unfolding,[],[f38,f55,f35,f55])).
% 1.95/0.70  fof(f38,plain,(
% 1.95/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f26])).
% 1.95/0.70  fof(f26,plain,(
% 1.95/0.70    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.95/0.70    inference(nnf_transformation,[],[f17])).
% 1.95/0.70  fof(f17,axiom,(
% 1.95/0.70    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.95/0.70  fof(f843,plain,(
% 1.95/0.70    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.95/0.70    inference(forward_demodulation,[],[f842,f29])).
% 1.95/0.70  fof(f29,plain,(
% 1.95/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f5])).
% 1.95/0.70  fof(f5,axiom,(
% 1.95/0.70    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.95/0.70  fof(f842,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 1.95/0.70    inference(forward_demodulation,[],[f835,f472])).
% 1.95/0.70  fof(f472,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.95/0.70    inference(forward_demodulation,[],[f463,f435])).
% 1.95/0.70  fof(f435,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.95/0.70    inference(forward_demodulation,[],[f434,f116])).
% 1.95/0.70  fof(f116,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0)),
% 1.95/0.70    inference(forward_demodulation,[],[f110,f30])).
% 1.95/0.70  fof(f30,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.95/0.70    inference(cnf_transformation,[],[f3])).
% 1.95/0.70  fof(f3,axiom,(
% 1.95/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.95/0.70  fof(f110,plain,(
% 1.95/0.70    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0)),
% 1.95/0.70    inference(superposition,[],[f56,f102])).
% 1.95/0.70  fof(f102,plain,(
% 1.95/0.70    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.95/0.70    inference(backward_demodulation,[],[f57,f90])).
% 1.95/0.70  fof(f90,plain,(
% 1.95/0.70    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),
% 1.95/0.70    inference(superposition,[],[f78,f30])).
% 1.95/0.70  fof(f78,plain,(
% 1.95/0.70    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),
% 1.95/0.70    inference(forward_demodulation,[],[f72,f63])).
% 1.95/0.70  fof(f63,plain,(
% 1.95/0.70    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 1.95/0.70    inference(definition_unfolding,[],[f43,f52,f52])).
% 1.95/0.70  fof(f43,plain,(
% 1.95/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f7])).
% 1.95/0.70  fof(f7,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 1.95/0.70  fof(f72,plain,(
% 1.95/0.70    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.95/0.70    inference(superposition,[],[f56,f57])).
% 1.95/0.70  fof(f56,plain,(
% 1.95/0.70    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.95/0.70    inference(definition_unfolding,[],[f48,f49,f47,f55])).
% 1.95/0.70  fof(f49,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.95/0.70    inference(definition_unfolding,[],[f34,f35])).
% 1.95/0.70  fof(f34,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.95/0.70    inference(cnf_transformation,[],[f6])).
% 1.95/0.70  fof(f6,axiom,(
% 1.95/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.95/0.70  fof(f48,plain,(
% 1.95/0.70    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.95/0.70    inference(cnf_transformation,[],[f9])).
% 1.95/0.70  fof(f9,axiom,(
% 1.95/0.70    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 1.95/0.70  fof(f434,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.95/0.70    inference(forward_demodulation,[],[f407,f121])).
% 1.95/0.70  fof(f121,plain,(
% 1.95/0.70    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,X0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X0)) )),
% 1.95/0.70    inference(forward_demodulation,[],[f120,f56])).
% 1.95/0.70  fof(f120,plain,(
% 1.95/0.70    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) )),
% 1.95/0.70    inference(superposition,[],[f56,f116])).
% 1.95/0.70  fof(f407,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.95/0.70    inference(unit_resulting_resolution,[],[f28,f28,f213])).
% 1.95/0.70  fof(f213,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X0,X1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X0,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) | sK1 = X1 | sK1 = X0) )),
% 1.95/0.70    inference(backward_demodulation,[],[f136,f212])).
% 1.95/0.70  fof(f212,plain,(
% 1.95/0.70    ( ! [X19,X18] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X18,X19) = k6_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,X18,X19)) )),
% 1.95/0.70    inference(forward_demodulation,[],[f205,f56])).
% 1.95/0.70  fof(f205,plain,(
% 1.95/0.70    ( ! [X19,X18] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X18,X19) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X18),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X18))))) )),
% 1.95/0.70    inference(superposition,[],[f56,f144])).
% 1.95/0.70  fof(f144,plain,(
% 1.95/0.70    ( ! [X14] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X14) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X14)) )),
% 1.95/0.70    inference(forward_demodulation,[],[f143,f56])).
% 1.95/0.70  fof(f143,plain,(
% 1.95/0.70    ( ! [X14] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X14) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X14),k3_xboole_0(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X14),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) )),
% 1.95/0.70    inference(superposition,[],[f56,f90])).
% 1.95/0.70  fof(f136,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) | sK1 = X1 | sK1 = X0) )),
% 1.95/0.70    inference(superposition,[],[f62,f90])).
% 1.95/0.70  fof(f62,plain,(
% 1.95/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 1.95/0.70    inference(definition_unfolding,[],[f42,f35,f53,f55,f54])).
% 1.95/0.70  fof(f42,plain,(
% 1.95/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 1.95/0.70    inference(cnf_transformation,[],[f22])).
% 1.95/0.70  fof(f22,plain,(
% 1.95/0.70    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 1.95/0.70    inference(ennf_transformation,[],[f8])).
% 1.95/0.70  fof(f8,axiom,(
% 1.95/0.70    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).
% 1.95/0.70  fof(f28,plain,(
% 1.95/0.70    sK0 != sK1),
% 1.95/0.70    inference(cnf_transformation,[],[f24])).
% 1.95/0.70  fof(f463,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 1.95/0.70    inference(superposition,[],[f141,f90])).
% 1.95/0.70  fof(f141,plain,(
% 1.95/0.70    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k6_enumset1(X6,X7,X8,X9,X10,X11,X12,sK1) = k5_xboole_0(k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X12),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X12))))) )),
% 1.95/0.70    inference(superposition,[],[f56,f90])).
% 1.95/0.70  fof(f835,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.95/0.70    inference(superposition,[],[f788,f148])).
% 1.95/0.70  fof(f148,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0))) )),
% 1.95/0.70    inference(superposition,[],[f41,f103])).
% 1.95/0.70  fof(f103,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 1.95/0.70    inference(forward_demodulation,[],[f91,f90])).
% 1.95/0.70  fof(f91,plain,(
% 1.95/0.70    k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),
% 1.95/0.70    inference(superposition,[],[f78,f32])).
% 1.95/0.70  fof(f32,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.95/0.70    inference(cnf_transformation,[],[f1])).
% 1.95/0.70  fof(f1,axiom,(
% 1.95/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.95/0.70  fof(f41,plain,(
% 1.95/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.95/0.70    inference(cnf_transformation,[],[f4])).
% 1.95/0.70  fof(f4,axiom,(
% 1.95/0.70    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.95/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.95/0.70  fof(f788,plain,(
% 1.95/0.70    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) )),
% 1.95/0.70    inference(backward_demodulation,[],[f301,f782])).
% 1.95/0.70  fof(f782,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 1.95/0.70    inference(forward_demodulation,[],[f777,f30])).
% 1.95/0.70  fof(f777,plain,(
% 1.95/0.70    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.95/0.70    inference(superposition,[],[f760,f29])).
% 1.95/0.70  fof(f760,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0)) = X0) )),
% 1.95/0.70    inference(backward_demodulation,[],[f97,f759])).
% 1.95/0.70  fof(f759,plain,(
% 1.95/0.70    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = X6) )),
% 1.95/0.70    inference(forward_demodulation,[],[f751,f30])).
% 1.95/0.70  fof(f751,plain,(
% 1.95/0.70    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0))) )),
% 1.95/0.70    inference(superposition,[],[f732,f32])).
% 1.95/0.70  fof(f732,plain,(
% 1.95/0.70    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8))) )),
% 1.95/0.70    inference(backward_demodulation,[],[f329,f725])).
% 1.95/0.70  fof(f725,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 1.95/0.70    inference(superposition,[],[f296,f32])).
% 1.95/0.70  fof(f296,plain,(
% 1.95/0.70    ( ! [X8] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,X8)) )),
% 1.95/0.70    inference(forward_demodulation,[],[f276,f30])).
% 1.95/0.70  fof(f276,plain,(
% 1.95/0.70    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) )),
% 1.95/0.70    inference(superposition,[],[f164,f127])).
% 1.95/0.70  fof(f127,plain,(
% 1.95/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.95/0.70    inference(forward_demodulation,[],[f122,f30])).
% 1.95/0.70  fof(f122,plain,(
% 1.95/0.70    k5_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.95/0.70    inference(superposition,[],[f97,f29])).
% 1.95/0.70  fof(f164,plain,(
% 1.95/0.70    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))))) )),
% 1.95/0.70    inference(superposition,[],[f124,f41])).
% 1.95/0.70  fof(f124,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) )),
% 1.95/0.70    inference(superposition,[],[f97,f32])).
% 1.95/0.70  fof(f329,plain,(
% 1.95/0.70    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X8))) )),
% 1.95/0.70    inference(superposition,[],[f173,f159])).
% 1.95/0.70  fof(f159,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0))) )),
% 1.95/0.70    inference(superposition,[],[f41,f127])).
% 1.95/0.70  fof(f173,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X1)))) )),
% 1.95/0.70    inference(forward_demodulation,[],[f172,f41])).
% 1.95/0.70  fof(f172,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X1)))) )),
% 1.95/0.70    inference(forward_demodulation,[],[f169,f41])).
% 1.95/0.70  fof(f169,plain,(
% 1.95/0.70    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),X1))) )),
% 1.95/0.70    inference(superposition,[],[f41,f124])).
% 1.95/0.70  fof(f97,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),X0))) )),
% 1.95/0.70    inference(backward_demodulation,[],[f76,f90])).
% 1.95/0.70  fof(f76,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.95/0.70    inference(superposition,[],[f41,f57])).
% 1.95/0.70  fof(f301,plain,(
% 1.95/0.70    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))))) )),
% 1.95/0.70    inference(forward_demodulation,[],[f300,f30])).
% 1.95/0.70  fof(f300,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))))) )),
% 1.95/0.70    inference(forward_demodulation,[],[f280,f32])).
% 1.95/0.70  fof(f280,plain,(
% 1.95/0.70    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),X0))) )),
% 1.95/0.70    inference(superposition,[],[f164,f29])).
% 1.95/0.70  % SZS output end Proof for theBenchmark
% 1.95/0.70  % (20767)------------------------------
% 1.95/0.70  % (20767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.70  % (20767)Termination reason: Refutation
% 1.95/0.70  
% 1.95/0.70  % (20767)Memory used [KB]: 12537
% 1.95/0.70  % (20767)Time elapsed: 0.283 s
% 1.95/0.70  % (20767)------------------------------
% 1.95/0.70  % (20767)------------------------------
% 2.55/0.71  % (20776)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.55/0.71  % (20778)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.55/0.72  % (20740)Success in time 0.341 s
%------------------------------------------------------------------------------
