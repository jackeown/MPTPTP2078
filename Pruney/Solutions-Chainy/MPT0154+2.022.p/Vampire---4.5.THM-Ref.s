%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   27 (  35 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f436])).

fof(f436,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f23,f209])).

fof(f209,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(forward_demodulation,[],[f207,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f207,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[],[f111,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f111,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0) ),
    inference(backward_demodulation,[],[f85,f110])).

fof(f110,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3) ),
    inference(forward_demodulation,[],[f109,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f109,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f36,f65])).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0) ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f34,f25])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f37,f25])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (17385)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (17374)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (17375)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (17388)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (17375)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f440,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f436])).
% 0.20/0.47  fof(f436,plain,(
% 0.20/0.47    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)),
% 0.20/0.47    inference(superposition,[],[f23,f209])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f207,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(superposition,[],[f111,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)) )),
% 0.20/0.47    inference(backward_demodulation,[],[f85,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f109,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))) )),
% 0.20/0.47    inference(superposition,[],[f36,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f63,f30])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.20/0.47    inference(superposition,[],[f34,f25])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.20/0.47    inference(superposition,[],[f37,f25])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    inference(negated_conjecture,[],[f16])).
% 0.20/0.47  fof(f16,conjecture,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17375)------------------------------
% 0.20/0.47  % (17375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17375)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (17375)Memory used [KB]: 2046
% 0.20/0.47  % (17375)Time elapsed: 0.060 s
% 0.20/0.47  % (17375)------------------------------
% 0.20/0.47  % (17375)------------------------------
% 0.20/0.47  % (17382)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (17369)Success in time 0.119 s
%------------------------------------------------------------------------------
