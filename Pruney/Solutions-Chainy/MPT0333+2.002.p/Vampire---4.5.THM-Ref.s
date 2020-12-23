%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:11 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   18 (  35 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  38 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f23,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_zfmisc_1(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) ),
    inference(forward_demodulation,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2))) ),
    inference(definition_unfolding,[],[f15,f11,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f22,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_zfmisc_1(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) ),
    inference(forward_demodulation,[],[f19,f21])).

fof(f19,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_xboole_0(k1_tarski(k4_tarski(sK1,sK2)),k1_tarski(k4_tarski(sK1,sK3)))) ),
    inference(definition_unfolding,[],[f10,f11,f11,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f17,f11,f11])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f10,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.64/0.58  % (12590)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.58  % (12600)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.58  % (12610)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (12612)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.58  % (12593)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.58  % (12610)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f23,f13])).
% 1.64/0.58  fof(f13,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_zfmisc_1(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))),
% 1.64/0.58    inference(forward_demodulation,[],[f22,f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2)))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f15,f11,f11])).
% 1.64/0.58  fof(f11,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.64/0.58  fof(f15,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_zfmisc_1(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))),
% 1.64/0.58    inference(forward_demodulation,[],[f19,f21])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_xboole_0(k1_tarski(k4_tarski(sK1,sK2)),k1_tarski(k4_tarski(sK1,sK3))))),
% 1.64/0.58    inference(definition_unfolding,[],[f10,f11,f11,f18])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f17,f11,f11])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.64/0.58  fof(f10,plain,(
% 1.64/0.58    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 1.64/0.58    inference(cnf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,plain,(
% 1.64/0.58    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.64/0.58    inference(ennf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.64/0.58    inference(negated_conjecture,[],[f6])).
% 1.64/0.58  fof(f6,conjecture,(
% 1.64/0.58    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (12610)------------------------------
% 1.64/0.58  % (12610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (12610)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (12610)Memory used [KB]: 1663
% 1.64/0.58  % (12610)Time elapsed: 0.004 s
% 1.64/0.58  % (12610)------------------------------
% 1.64/0.58  % (12610)------------------------------
% 1.64/0.58  % (12612)Refutation not found, incomplete strategy% (12612)------------------------------
% 1.64/0.58  % (12612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (12612)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (12612)Memory used [KB]: 1663
% 1.64/0.58  % (12612)Time elapsed: 0.101 s
% 1.64/0.58  % (12612)------------------------------
% 1.64/0.58  % (12612)------------------------------
% 1.64/0.58  % (12604)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.64/0.58  % (12588)Success in time 0.218 s
%------------------------------------------------------------------------------
