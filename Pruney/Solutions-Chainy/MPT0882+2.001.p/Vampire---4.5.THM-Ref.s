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
% DateTime   : Thu Dec  3 12:58:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  29 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(superposition,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2))) ),
    inference(definition_unfolding,[],[f16,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3))) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(backward_demodulation,[],[f18,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f18,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3))) ),
    inference(definition_unfolding,[],[f11,f14,f12,f12,f15,f15])).

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

fof(f11,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:41:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (21688)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (21678)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (21677)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (21676)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (21680)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (21688)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.49    inference(superposition,[],[f21,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f12,f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3))) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.49    inference(backward_demodulation,[],[f18,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3)))),
% 0.22/0.49    inference(definition_unfolding,[],[f11,f14,f12,f12,f15,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_mcart_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (21688)------------------------------
% 0.22/0.49  % (21688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21688)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (21688)Memory used [KB]: 6140
% 0.22/0.49  % (21688)Time elapsed: 0.068 s
% 0.22/0.49  % (21688)------------------------------
% 0.22/0.49  % (21688)------------------------------
% 0.22/0.49  % (21686)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (21685)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (21673)Success in time 0.126 s
%------------------------------------------------------------------------------
