%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 362 expanded)
%              Number of leaves         :   14 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 369 expanded)
%              Number of equality atoms :   60 ( 368 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f46,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(forward_demodulation,[],[f73,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(forward_demodulation,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f27,f36,f37,f36])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f19,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    inference(forward_demodulation,[],[f71,f58])).

fof(f58,plain,(
    ! [X6,X4,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6) ),
    inference(forward_demodulation,[],[f56,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f56,plain,(
    ! [X6,X4,X7,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7)) ),
    inference(superposition,[],[f22,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3)) ),
    inference(superposition,[],[f52,f58])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(forward_demodulation,[],[f51,f39])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(forward_demodulation,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(forward_demodulation,[],[f41,f39])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f26,f37,f36,f36])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f45,f39])).

fof(f45,plain,(
    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f44,f39])).

fof(f44,plain,(
    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f43,f39])).

fof(f43,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f38,f39])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) ),
    inference(definition_unfolding,[],[f18,f24,f37,f37,f37,f37])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:49:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (30291)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  % (30291)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f91])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.43    inference(superposition,[],[f46,f74])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) = k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X2,X2,X2,X2,X3))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f73,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f48,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f21,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f20,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f25,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f30,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f47,f39])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f40,f39])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f27,f36,f37,f36])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f19,f35])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f71,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X6,X4,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f56,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,axiom,(
% 0.22/0.43    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7))) )),
% 0.22/0.43    inference(superposition,[],[f22,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f29,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3))) )),
% 0.22/0.43    inference(superposition,[],[f52,f58])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f51,f39])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f50,f39])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f41,f39])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f26,f37,f36,f36])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.43    inference(forward_demodulation,[],[f45,f39])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.43    inference(forward_demodulation,[],[f44,f39])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.43    inference(forward_demodulation,[],[f43,f39])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2))),
% 0.22/0.43    inference(backward_demodulation,[],[f38,f39])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK2))),
% 0.22/0.43    inference(definition_unfolding,[],[f18,f24,f37,f37,f37,f37])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.22/0.43    inference(negated_conjecture,[],[f13])).
% 0.22/0.43  fof(f13,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (30291)------------------------------
% 0.22/0.43  % (30291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (30291)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (30291)Memory used [KB]: 1663
% 0.22/0.43  % (30291)Time elapsed: 0.008 s
% 0.22/0.43  % (30291)------------------------------
% 0.22/0.43  % (30291)------------------------------
% 0.22/0.43  % (30277)Success in time 0.068 s
%------------------------------------------------------------------------------
