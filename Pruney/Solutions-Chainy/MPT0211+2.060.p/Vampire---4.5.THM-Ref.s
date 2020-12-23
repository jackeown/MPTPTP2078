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
% DateTime   : Thu Dec  3 12:34:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 202 expanded)
%              Number of leaves         :   10 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :   44 ( 203 expanded)
%              Number of equality atoms :   43 ( 202 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f672,plain,(
    $false ),
    inference(subsumption_resolution,[],[f671,f669])).

fof(f669,plain,(
    ! [X37,X35,X36] : k5_xboole_0(k1_enumset1(X35,X35,X35),k4_xboole_0(k1_enumset1(X35,X36,X37),k1_enumset1(X35,X35,X35))) = k1_enumset1(X35,X37,X36) ),
    inference(forward_demodulation,[],[f589,f582])).

fof(f582,plain,(
    ! [X14,X12,X13] : k1_enumset1(X12,X14,X13) = k5_xboole_0(k1_enumset1(X12,X12,X13),k4_xboole_0(k1_enumset1(X13,X13,X14),k1_enumset1(X12,X12,X13))) ),
    inference(superposition,[],[f35,f227])).

fof(f227,plain,(
    ! [X39,X37,X38] : k1_enumset1(X39,X37,X38) = k5_xboole_0(k1_enumset1(X39,X39,X39),k4_xboole_0(k1_enumset1(X38,X38,X37),k1_enumset1(X39,X39,X39))) ),
    inference(superposition,[],[f33,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(superposition,[],[f110,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f110,plain,(
    ! [X2,X1] : k1_enumset1(X1,X1,X2) = k1_enumset1(X1,X2,X2) ),
    inference(superposition,[],[f34,f33])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f20,f19,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f25,f20,f29,f19])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30,f20,f19,f19])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f27,f20,f29])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f589,plain,(
    ! [X37,X35,X36] : k5_xboole_0(k1_enumset1(X35,X35,X35),k4_xboole_0(k1_enumset1(X35,X36,X37),k1_enumset1(X35,X35,X35))) = k5_xboole_0(k1_enumset1(X35,X35,X36),k4_xboole_0(k1_enumset1(X36,X36,X37),k1_enumset1(X35,X35,X36))) ),
    inference(superposition,[],[f35,f35])).

fof(f671,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK2,sK1),k1_enumset1(sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f656,f21])).

fof(f656,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    inference(superposition,[],[f113,f35])).

fof(f113,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f112,f110])).

fof(f112,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK0,sK2,sK2),k1_enumset1(sK0,sK0,sK1))) ),
    inference(backward_demodulation,[],[f39,f110])).

fof(f39,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK0,sK2,sK2),k1_enumset1(sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f38,f21])).

fof(f38,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK0,sK2),k1_enumset1(sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f37,f21])).

fof(f37,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f36,f21])).

fof(f36,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK0,sK1))) ),
    inference(backward_demodulation,[],[f32,f21])).

fof(f32,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0))) ),
    inference(definition_unfolding,[],[f17,f20,f19,f19])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22031)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (22031)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f672,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f671,f669])).
% 0.20/0.44  fof(f669,plain,(
% 0.20/0.44    ( ! [X37,X35,X36] : (k5_xboole_0(k1_enumset1(X35,X35,X35),k4_xboole_0(k1_enumset1(X35,X36,X37),k1_enumset1(X35,X35,X35))) = k1_enumset1(X35,X37,X36)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f589,f582])).
% 0.20/0.44  fof(f582,plain,(
% 0.20/0.44    ( ! [X14,X12,X13] : (k1_enumset1(X12,X14,X13) = k5_xboole_0(k1_enumset1(X12,X12,X13),k4_xboole_0(k1_enumset1(X13,X13,X14),k1_enumset1(X12,X12,X13)))) )),
% 0.20/0.44    inference(superposition,[],[f35,f227])).
% 0.20/0.44  fof(f227,plain,(
% 0.20/0.44    ( ! [X39,X37,X38] : (k1_enumset1(X39,X37,X38) = k5_xboole_0(k1_enumset1(X39,X39,X39),k4_xboole_0(k1_enumset1(X38,X38,X37),k1_enumset1(X39,X39,X39)))) )),
% 0.20/0.44    inference(superposition,[],[f33,f120])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.20/0.44    inference(superposition,[],[f110,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X2,X1] : (k1_enumset1(X1,X1,X2) = k1_enumset1(X1,X2,X2)) )),
% 0.20/0.44    inference(superposition,[],[f34,f33])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f26,f20,f19,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f18,f19])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f25,f20,f29,f19])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f28,f30,f20,f19,f19])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f27,f20,f29])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.44  fof(f589,plain,(
% 0.20/0.44    ( ! [X37,X35,X36] : (k5_xboole_0(k1_enumset1(X35,X35,X35),k4_xboole_0(k1_enumset1(X35,X36,X37),k1_enumset1(X35,X35,X35))) = k5_xboole_0(k1_enumset1(X35,X35,X36),k4_xboole_0(k1_enumset1(X36,X36,X37),k1_enumset1(X35,X35,X36)))) )),
% 0.20/0.44    inference(superposition,[],[f35,f35])).
% 0.20/0.44  fof(f671,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK2,sK1),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.44    inference(forward_demodulation,[],[f656,f21])).
% 0.20/0.44  fof(f656,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.44    inference(superposition,[],[f113,f35])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.44    inference(forward_demodulation,[],[f112,f110])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK0,sK2,sK2),k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.45    inference(backward_demodulation,[],[f39,f110])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK0,sK2,sK2),k1_enumset1(sK0,sK1,sK1)))),
% 0.20/0.45    inference(forward_demodulation,[],[f38,f21])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK0,sK2),k1_enumset1(sK0,sK1,sK1)))),
% 0.20/0.45    inference(forward_demodulation,[],[f37,f21])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK0,sK1,sK1)))),
% 0.20/0.45    inference(forward_demodulation,[],[f36,f21])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK0,sK1)))),
% 0.20/0.45    inference(backward_demodulation,[],[f32,f21])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k4_xboole_0(k1_enumset1(sK2,sK2,sK0),k1_enumset1(sK1,sK1,sK0)))),
% 0.20/0.45    inference(definition_unfolding,[],[f17,f20,f19,f19])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.45    inference(negated_conjecture,[],[f12])).
% 0.20/0.45  fof(f12,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (22031)------------------------------
% 0.20/0.45  % (22031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (22031)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (22031)Memory used [KB]: 2302
% 0.20/0.45  % (22031)Time elapsed: 0.034 s
% 0.20/0.45  % (22031)------------------------------
% 0.20/0.45  % (22031)------------------------------
% 0.20/0.45  % (22017)Success in time 0.092 s
%------------------------------------------------------------------------------
