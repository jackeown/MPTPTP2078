%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  62 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  64 expanded)
%              Number of equality atoms :   26 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f17,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(f26,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4))) ),
    inference(forward_demodulation,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(definition_unfolding,[],[f19,f14,f13,f13,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4))) ),
    inference(backward_demodulation,[],[f21,f24])).

fof(f21,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    inference(definition_unfolding,[],[f12,f14,f13,f13,f20,f15,f15,f15,f15])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f18,f13,f13])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (26089)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.40  % (26089)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f27,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(subsumption_resolution,[],[f26,f22])).
% 0.21/0.40  fof(f22,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f17,f13])).
% 0.21/0.40  fof(f13,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.40  fof(f17,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f3])).
% 0.21/0.40  fof(f3,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.21/0.40  fof(f26,plain,(
% 0.21/0.40    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)))),
% 0.21/0.40    inference(forward_demodulation,[],[f25,f24])).
% 0.21/0.40  fof(f24,plain,(
% 0.21/0.40    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f19,f14,f13,f13,f15,f15])).
% 0.21/0.40  fof(f15,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f4])).
% 0.21/0.40  fof(f4,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f5])).
% 0.21/0.40  fof(f5,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.40  fof(f19,plain,(
% 0.21/0.40    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f6])).
% 0.21/0.40  fof(f6,axiom,(
% 0.21/0.40    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).
% 0.21/0.40  fof(f25,plain,(
% 0.21/0.40    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)))),
% 0.21/0.40    inference(backward_demodulation,[],[f21,f24])).
% 0.21/0.40  fof(f21,plain,(
% 0.21/0.40    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 0.21/0.40    inference(definition_unfolding,[],[f12,f14,f13,f13,f20,f15,f15,f15,f15])).
% 0.21/0.40  fof(f20,plain,(
% 0.21/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f18,f13,f13])).
% 0.21/0.40  fof(f18,plain,(
% 0.21/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f1])).
% 0.21/0.40  fof(f1,axiom,(
% 0.21/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.40  fof(f12,plain,(
% 0.21/0.40    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.21/0.40    inference(cnf_transformation,[],[f11])).
% 0.21/0.40  fof(f11,plain,(
% 0.21/0.40    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.21/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).
% 0.21/0.40  fof(f10,plain,(
% 0.21/0.40    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f9,plain,(
% 0.21/0.40    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.21/0.40    inference(ennf_transformation,[],[f8])).
% 0.21/0.40  fof(f8,negated_conjecture,(
% 0.21/0.40    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.21/0.40    inference(negated_conjecture,[],[f7])).
% 0.21/0.40  fof(f7,conjecture,(
% 0.21/0.40    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 0.21/0.40  % SZS output end Proof for theBenchmark
% 0.21/0.40  % (26089)------------------------------
% 0.21/0.40  % (26089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (26089)Termination reason: Refutation
% 0.21/0.40  
% 0.21/0.40  % (26089)Memory used [KB]: 6140
% 0.21/0.40  % (26089)Time elapsed: 0.004 s
% 0.21/0.41  % (26089)------------------------------
% 0.21/0.41  % (26089)------------------------------
% 0.21/0.41  % (26081)Success in time 0.057 s
%------------------------------------------------------------------------------
