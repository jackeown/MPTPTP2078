%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   19 (  34 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  37 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f25,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f15,f11,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK3)) ),
    inference(superposition,[],[f16,f17])).

fof(f16,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3))) ),
    inference(definition_unfolding,[],[f10,f12,f11,f11,f13,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.45  % (14566)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.45  % (14566)Refutation found. Thanks to Tanya!
% 0.23/0.45  % SZS status Theorem for theBenchmark
% 0.23/0.46  % (14574)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.46  % (14573)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.46  % (14574)Refutation not found, incomplete strategy% (14574)------------------------------
% 0.23/0.46  % (14574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (14574)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.46  
% 0.23/0.46  % (14574)Memory used [KB]: 10490
% 0.23/0.46  % (14574)Time elapsed: 0.034 s
% 0.23/0.46  % (14574)------------------------------
% 0.23/0.46  % (14574)------------------------------
% 0.23/0.46  % SZS output start Proof for theBenchmark
% 0.23/0.46  fof(f27,plain,(
% 0.23/0.46    $false),
% 0.23/0.46    inference(trivial_inequality_removal,[],[f26])).
% 0.23/0.46  fof(f26,plain,(
% 0.23/0.46    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))),
% 0.23/0.46    inference(forward_demodulation,[],[f25,f17])).
% 0.23/0.46  fof(f17,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2)))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f15,f11,f11])).
% 0.23/0.46  fof(f11,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f1])).
% 0.23/0.46  fof(f1,axiom,(
% 0.23/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.23/0.46  fof(f15,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f2])).
% 0.23/0.46  fof(f2,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.23/0.46  fof(f25,plain,(
% 0.23/0.46    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK3))),
% 0.23/0.46    inference(superposition,[],[f16,f17])).
% 0.23/0.46  fof(f16,plain,(
% 0.23/0.46    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3)))),
% 0.23/0.46    inference(definition_unfolding,[],[f10,f12,f11,f11,f13,f13])).
% 0.23/0.46  fof(f13,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f3])).
% 0.23/0.46  fof(f3,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.23/0.46  fof(f12,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f4])).
% 0.23/0.46  fof(f4,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.23/0.46  fof(f10,plain,(
% 0.23/0.46    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.23/0.46    inference(cnf_transformation,[],[f9])).
% 0.23/0.46  fof(f9,plain,(
% 0.23/0.46    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.23/0.46  fof(f8,plain,(
% 0.23/0.46    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f7,plain,(
% 0.23/0.46    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.23/0.46    inference(ennf_transformation,[],[f6])).
% 0.23/0.46  fof(f6,negated_conjecture,(
% 0.23/0.46    ~! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.23/0.46    inference(negated_conjecture,[],[f5])).
% 0.23/0.46  fof(f5,conjecture,(
% 0.23/0.46    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).
% 0.23/0.46  % SZS output end Proof for theBenchmark
% 0.23/0.46  % (14566)------------------------------
% 0.23/0.46  % (14566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (14566)Termination reason: Refutation
% 0.23/0.46  
% 0.23/0.46  % (14566)Memory used [KB]: 6140
% 0.23/0.46  % (14566)Time elapsed: 0.046 s
% 0.23/0.46  % (14566)------------------------------
% 0.23/0.46  % (14566)------------------------------
% 0.23/0.46  % (14560)Success in time 0.098 s
%------------------------------------------------------------------------------
