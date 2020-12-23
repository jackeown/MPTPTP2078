%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 350 expanded)
%              Number of leaves         :   15 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 ( 355 expanded)
%              Number of equality atoms :   53 ( 354 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f106])).

% (6014)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f106,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f105,f50])).

fof(f50,plain,(
    ! [X6,X4,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6) ),
    inference(forward_demodulation,[],[f48,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f48,plain,(
    ! [X6,X4,X7,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7)) ),
    inference(superposition,[],[f23,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f105,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(superposition,[],[f104,f93])).

fof(f93,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f87,f83])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f73,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f20,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f31,f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f22,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f44,f39])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f34,f33,f36,f38,f37])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(f87,plain,(
    ! [X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(superposition,[],[f83,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_tarski(X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f28,f35,f35])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f104,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f40,f93])).

fof(f40,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (6019)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (6020)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (6026)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (6016)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (6018)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (6012)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (6022)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (6013)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (6022)Refutation not found, incomplete strategy% (6022)------------------------------
% 0.20/0.48  % (6022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6022)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (6022)Memory used [KB]: 10618
% 0.20/0.48  % (6022)Time elapsed: 0.071 s
% 0.20/0.48  % (6022)------------------------------
% 0.20/0.48  % (6022)------------------------------
% 0.20/0.48  % (6024)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (6021)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (6015)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (6017)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (6015)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f106])).
% 0.20/0.49  % (6014)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.49    inference(forward_demodulation,[],[f105,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X6,X4,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f48,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7))) )),
% 0.20/0.49    inference(superposition,[],[f23,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f30,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.20/0.49    inference(superposition,[],[f104,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f87,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.49    inference(superposition,[],[f73,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f20,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f31,f36,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f32])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.49    inference(superposition,[],[f44,f39])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k3_tarski(k6_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f34,f33,f36,f38,f37])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.20/0.49    inference(superposition,[],[f83,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_tarski(X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f35,f35])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2))),
% 0.20/0.49    inference(backward_demodulation,[],[f40,f93])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2))),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f14])).
% 0.20/0.49  fof(f14,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6015)------------------------------
% 0.20/0.49  % (6015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6015)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6015)Memory used [KB]: 6268
% 0.20/0.49  % (6015)Time elapsed: 0.086 s
% 0.20/0.49  % (6015)------------------------------
% 0.20/0.49  % (6015)------------------------------
% 0.20/0.49  % (6010)Success in time 0.137 s
%------------------------------------------------------------------------------
