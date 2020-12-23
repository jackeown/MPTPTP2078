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
% DateTime   : Thu Dec  3 12:58:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  64 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  68 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) ),
    inference(forward_demodulation,[],[f47,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ),
    inference(definition_unfolding,[],[f15,f14,f22,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f47,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[],[f28,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f28,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(forward_demodulation,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f18,f22,f14,f14])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f27,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    inference(backward_demodulation,[],[f23,f26])).

fof(f23,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(definition_unfolding,[],[f12,f14,f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f20,f14,f14])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f12,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (32100)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.41  % (32100)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))),
% 0.19/0.41    inference(forward_demodulation,[],[f47,f24])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f15,f14,f22,f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f13,f14])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.41  fof(f47,plain,(
% 0.19/0.41    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK3))),
% 0.19/0.41    inference(superposition,[],[f28,f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.19/0.41    inference(forward_demodulation,[],[f27,f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f18,f22,f14,f14])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.19/0.41    inference(backward_demodulation,[],[f23,f26])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),
% 0.19/0.41    inference(definition_unfolding,[],[f12,f14,f14,f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f20,f14,f14])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.19/0.41    inference(ennf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.19/0.41    inference(negated_conjecture,[],[f7])).
% 0.19/0.41  fof(f7,conjecture,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (32100)------------------------------
% 0.19/0.41  % (32100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (32100)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (32100)Memory used [KB]: 1663
% 0.19/0.41  % (32100)Time elapsed: 0.005 s
% 0.19/0.41  % (32100)------------------------------
% 0.19/0.41  % (32100)------------------------------
% 0.19/0.41  % (32086)Success in time 0.057 s
%------------------------------------------------------------------------------
