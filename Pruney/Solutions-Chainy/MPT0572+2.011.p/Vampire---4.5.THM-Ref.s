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
% DateTime   : Thu Dec  3 12:50:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 203 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 249 expanded)
%              Number of equality atoms :   24 ( 159 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(resolution,[],[f455,f39])).

fof(f39,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f34,f36])).

fof(f34,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f21,f33,f33])).

fof(f21,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(f455,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k10_relat_1(sK2,X1),k4_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X0)))) ),
    inference(superposition,[],[f419,f53])).

fof(f53,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4)) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f24,f33,f33])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f419,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(k10_relat_1(sK2,X3),k4_xboole_0(k10_relat_1(sK2,X3),k10_relat_1(sK2,X2)))) ),
    inference(resolution,[],[f251,f253])).

fof(f253,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k10_relat_1(sK2,X0)) ),
    inference(superposition,[],[f247,f53])).

fof(f247,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,X3)),k10_relat_1(sK2,X2)) ),
    inference(superposition,[],[f242,f42])).

fof(f42,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f242,plain,(
    ! [X8,X9] : r1_tarski(k10_relat_1(sK2,X8),k10_relat_1(sK2,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f22,f238])).

fof(f238,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f251,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(X3,X4)),X5)
      | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X3,X4)),k4_xboole_0(X5,k4_xboole_0(X5,k10_relat_1(sK2,X3)))) ) ),
    inference(resolution,[],[f247,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (7133)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  % (7133)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f481,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(resolution,[],[f455,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.22/0.43    inference(forward_demodulation,[],[f38,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f27,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f25,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f26,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.22/0.44    inference(backward_demodulation,[],[f34,f36])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.22/0.44    inference(definition_unfolding,[],[f21,f33,f33])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f11])).
% 0.22/0.44  fof(f11,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).
% 0.22/0.44  fof(f455,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k10_relat_1(sK2,X1),k4_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X0))))) )),
% 0.22/0.44    inference(superposition,[],[f419,f53])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(X7,X6))) )),
% 0.22/0.44    inference(superposition,[],[f47,f36])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 0.22/0.44    inference(superposition,[],[f35,f36])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f24,f33,f33])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.44  fof(f419,plain,(
% 0.22/0.44    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(k10_relat_1(sK2,X3),k4_xboole_0(k10_relat_1(sK2,X3),k10_relat_1(sK2,X2))))) )),
% 0.22/0.44    inference(resolution,[],[f251,f253])).
% 0.22/0.44  fof(f253,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k10_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(superposition,[],[f247,f53])).
% 0.22/0.44  fof(f247,plain,(
% 0.22/0.44    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,X3)),k10_relat_1(sK2,X2))) )),
% 0.22/0.44    inference(superposition,[],[f242,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.22/0.44    inference(resolution,[],[f28,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.44  fof(f242,plain,(
% 0.22/0.44    ( ! [X8,X9] : (r1_tarski(k10_relat_1(sK2,X8),k10_relat_1(sK2,k2_xboole_0(X8,X9)))) )),
% 0.22/0.44    inference(superposition,[],[f22,f238])).
% 0.22/0.44  fof(f238,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 0.22/0.44    inference(resolution,[],[f30,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.44  fof(f251,plain,(
% 0.22/0.44    ( ! [X4,X5,X3] : (~r1_tarski(k10_relat_1(sK2,k4_xboole_0(X3,X4)),X5) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X3,X4)),k4_xboole_0(X5,k4_xboole_0(X5,k10_relat_1(sK2,X3))))) )),
% 0.22/0.44    inference(resolution,[],[f247,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f37,f36])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f31,f33])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (7133)------------------------------
% 0.22/0.44  % (7133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (7133)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (7133)Memory used [KB]: 2174
% 0.22/0.44  % (7133)Time elapsed: 0.024 s
% 0.22/0.44  % (7133)------------------------------
% 0.22/0.44  % (7133)------------------------------
% 0.22/0.44  % (7113)Success in time 0.082 s
%------------------------------------------------------------------------------
