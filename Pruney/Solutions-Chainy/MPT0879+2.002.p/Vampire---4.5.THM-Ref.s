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
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15])).

fof(f15,plain,(
    k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f14,plain,(
    k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f13,f10])).

fof(f13,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f9,f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f9,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

% (31581)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f8,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31577)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (31579)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (31571)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (31571)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.21/0.47    inference(superposition,[],[f14,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2))),
% 0.21/0.47    inference(forward_demodulation,[],[f13,f10])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.21/0.47    inference(definition_unfolding,[],[f9,f12,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % (31581)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31571)------------------------------
% 0.21/0.47  % (31571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31571)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31571)Memory used [KB]: 6012
% 0.21/0.47  % (31571)Time elapsed: 0.060 s
% 0.21/0.47  % (31571)------------------------------
% 0.21/0.47  % (31571)------------------------------
% 0.21/0.47  % (31570)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31566)Success in time 0.113 s
%------------------------------------------------------------------------------
