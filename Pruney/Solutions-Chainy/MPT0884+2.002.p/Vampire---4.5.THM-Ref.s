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
% DateTime   : Thu Dec  3 12:58:55 EST 2020

% Result     : Theorem 25.88s
% Output     : Refutation 25.88s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 269 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 271 expanded)
%              Number of equality atoms :   53 ( 270 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48924,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48712,f9365])).

fof(f9365,plain,(
    ! [X327,X329,X326,X328,X330] : k2_enumset1(k4_tarski(k4_tarski(X326,X327),X329),k4_tarski(k4_tarski(X326,X327),X330),k4_tarski(k4_tarski(X328,X327),X329),k4_tarski(k4_tarski(X328,X327),X330)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X326,X326,X326,X328),k2_enumset1(X327,X327,X327,X327)),k2_enumset1(X329,X329,X329,X330)) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f30,f36,f37,f36])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f33,f36,f36])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f48712,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    inference(superposition,[],[f41,f48096])).

fof(f48096,plain,(
    ! [X43,X41,X42,X40] : k2_enumset1(X40,X41,X42,X43) = k2_enumset1(X40,X42,X41,X43) ),
    inference(superposition,[],[f488,f76])).

fof(f76,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X4,X4,X5,X5),k2_enumset1(X6,X6,X6,X7)) ),
    inference(superposition,[],[f40,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f46,f40])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f32,f27,f37])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f31,f36,f36])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f488,plain,(
    ! [X30,X33,X31,X32] : k2_xboole_0(k2_enumset1(X33,X33,X30,X30),k2_enumset1(X31,X31,X31,X32)) = k2_enumset1(X33,X31,X30,X32) ),
    inference(forward_demodulation,[],[f418,f487])).

fof(f487,plain,(
    ! [X28,X26,X29,X27] : k2_xboole_0(k2_enumset1(X29,X29,X29,X29),k2_enumset1(X27,X26,X28,X28)) = k2_enumset1(X29,X26,X27,X28) ),
    inference(forward_demodulation,[],[f417,f76])).

fof(f417,plain,(
    ! [X28,X26,X29,X27] : k2_xboole_0(k2_enumset1(X29,X29,X26,X26),k2_enumset1(X27,X27,X27,X28)) = k2_xboole_0(k2_enumset1(X29,X29,X29,X29),k2_enumset1(X27,X26,X28,X28)) ),
    inference(superposition,[],[f48,f221])).

fof(f221,plain,(
    ! [X10,X8,X9] : k2_enumset1(X8,X8,X9,X10) = k2_enumset1(X9,X8,X10,X10) ),
    inference(superposition,[],[f55,f46])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3)) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f36,f36])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X4)) ),
    inference(definition_unfolding,[],[f35,f38,f27,f36])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f418,plain,(
    ! [X30,X33,X31,X32] : k2_xboole_0(k2_enumset1(X33,X33,X30,X30),k2_enumset1(X31,X31,X31,X32)) = k2_xboole_0(k2_enumset1(X33,X33,X33,X33),k2_enumset1(X30,X31,X32,X32)) ),
    inference(superposition,[],[f48,f65])).

fof(f41,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    inference(definition_unfolding,[],[f20,f25,f36,f37,f36,f26,f26,f26,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (20578)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (20576)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (20569)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (20579)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (20568)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (20571)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (20575)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (20573)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (20574)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (20581)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (20570)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (20580)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (20582)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (20572)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20567)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (20566)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.54  % (20583)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.56  % (20577)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.56  % (20577)Refutation not found, incomplete strategy% (20577)------------------------------
% 0.21/0.56  % (20577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20577)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20577)Memory used [KB]: 10618
% 0.21/0.56  % (20577)Time elapsed: 0.129 s
% 0.21/0.56  % (20577)------------------------------
% 0.21/0.56  % (20577)------------------------------
% 5.16/1.03  % (20570)Time limit reached!
% 5.16/1.03  % (20570)------------------------------
% 5.16/1.03  % (20570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.16/1.03  % (20570)Termination reason: Time limit
% 5.16/1.03  % (20570)Termination phase: Saturation
% 5.16/1.03  
% 5.16/1.03  % (20570)Memory used [KB]: 9210
% 5.16/1.03  % (20570)Time elapsed: 0.600 s
% 5.16/1.03  % (20570)------------------------------
% 5.16/1.03  % (20570)------------------------------
% 12.36/1.94  % (20571)Time limit reached!
% 12.36/1.94  % (20571)------------------------------
% 12.36/1.94  % (20571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.78/1.96  % (20571)Termination reason: Time limit
% 12.78/1.96  % (20571)Termination phase: Saturation
% 12.78/1.96  
% 12.78/1.96  % (20571)Memory used [KB]: 27249
% 12.78/1.96  % (20571)Time elapsed: 1.500 s
% 12.78/1.96  % (20571)------------------------------
% 12.78/1.96  % (20571)------------------------------
% 12.78/1.98  % (20572)Time limit reached!
% 12.78/1.98  % (20572)------------------------------
% 12.78/1.98  % (20572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.78/1.98  % (20572)Termination reason: Time limit
% 12.78/1.98  
% 12.78/1.98  % (20572)Memory used [KB]: 15735
% 12.78/1.98  % (20572)Time elapsed: 1.517 s
% 12.78/1.98  % (20572)------------------------------
% 12.78/1.98  % (20572)------------------------------
% 14.79/2.22  % (20568)Time limit reached!
% 14.79/2.22  % (20568)------------------------------
% 14.79/2.22  % (20568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.79/2.22  % (20568)Termination reason: Time limit
% 14.79/2.22  
% 14.79/2.22  % (20568)Memory used [KB]: 14328
% 14.79/2.22  % (20568)Time elapsed: 1.810 s
% 14.79/2.22  % (20568)------------------------------
% 14.79/2.22  % (20568)------------------------------
% 17.79/2.62  % (20578)Time limit reached!
% 17.79/2.62  % (20578)------------------------------
% 17.79/2.62  % (20578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.62  % (20578)Termination reason: Time limit
% 17.79/2.62  % (20578)Termination phase: Saturation
% 17.79/2.62  
% 17.79/2.62  % (20578)Memory used [KB]: 15863
% 17.79/2.62  % (20578)Time elapsed: 2.200 s
% 17.79/2.62  % (20578)------------------------------
% 17.79/2.62  % (20578)------------------------------
% 25.88/3.62  % (20575)Refutation found. Thanks to Tanya!
% 25.88/3.62  % SZS status Theorem for theBenchmark
% 25.88/3.63  % SZS output start Proof for theBenchmark
% 25.88/3.63  fof(f48924,plain,(
% 25.88/3.63    $false),
% 25.88/3.63    inference(subsumption_resolution,[],[f48712,f9365])).
% 25.88/3.63  fof(f9365,plain,(
% 25.88/3.63    ( ! [X327,X329,X326,X328,X330] : (k2_enumset1(k4_tarski(k4_tarski(X326,X327),X329),k4_tarski(k4_tarski(X326,X327),X330),k4_tarski(k4_tarski(X328,X327),X329),k4_tarski(k4_tarski(X328,X327),X330)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X326,X326,X326,X328),k2_enumset1(X327,X327,X327,X327)),k2_enumset1(X329,X329,X329,X330))) )),
% 25.88/3.63    inference(superposition,[],[f47,f44])).
% 25.88/3.63  fof(f44,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f30,f36,f37,f36])).
% 25.88/3.63  fof(f37,plain,(
% 25.88/3.63    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 25.88/3.63    inference(definition_unfolding,[],[f21,f36])).
% 25.88/3.63  fof(f21,plain,(
% 25.88/3.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f7])).
% 25.88/3.63  fof(f7,axiom,(
% 25.88/3.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 25.88/3.63  fof(f36,plain,(
% 25.88/3.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 25.88/3.63    inference(definition_unfolding,[],[f23,f27])).
% 25.88/3.63  fof(f27,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f9])).
% 25.88/3.63  fof(f9,axiom,(
% 25.88/3.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 25.88/3.63  fof(f23,plain,(
% 25.88/3.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f8])).
% 25.88/3.63  fof(f8,axiom,(
% 25.88/3.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 25.88/3.63  fof(f30,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f12])).
% 25.88/3.63  fof(f12,axiom,(
% 25.88/3.63    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 25.88/3.63  fof(f47,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f33,f36,f36])).
% 25.88/3.63  fof(f33,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f11])).
% 25.88/3.63  fof(f11,axiom,(
% 25.88/3.63    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 25.88/3.63  fof(f48712,plain,(
% 25.88/3.63    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 25.88/3.63    inference(superposition,[],[f41,f48096])).
% 25.88/3.63  fof(f48096,plain,(
% 25.88/3.63    ( ! [X43,X41,X42,X40] : (k2_enumset1(X40,X41,X42,X43) = k2_enumset1(X40,X42,X41,X43)) )),
% 25.88/3.63    inference(superposition,[],[f488,f76])).
% 25.88/3.63  fof(f76,plain,(
% 25.88/3.63    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X4,X4,X5,X5),k2_enumset1(X6,X6,X6,X7))) )),
% 25.88/3.63    inference(superposition,[],[f40,f65])).
% 25.88/3.63  fof(f65,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 25.88/3.63    inference(superposition,[],[f46,f40])).
% 25.88/3.63  fof(f46,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f32,f27,f37])).
% 25.88/3.63  fof(f32,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f5])).
% 25.88/3.63  fof(f5,axiom,(
% 25.88/3.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 25.88/3.63  fof(f40,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f31,f36,f36])).
% 25.88/3.63  fof(f31,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f2])).
% 25.88/3.63  fof(f2,axiom,(
% 25.88/3.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 25.88/3.63  fof(f488,plain,(
% 25.88/3.63    ( ! [X30,X33,X31,X32] : (k2_xboole_0(k2_enumset1(X33,X33,X30,X30),k2_enumset1(X31,X31,X31,X32)) = k2_enumset1(X33,X31,X30,X32)) )),
% 25.88/3.63    inference(forward_demodulation,[],[f418,f487])).
% 25.88/3.63  fof(f487,plain,(
% 25.88/3.63    ( ! [X28,X26,X29,X27] : (k2_xboole_0(k2_enumset1(X29,X29,X29,X29),k2_enumset1(X27,X26,X28,X28)) = k2_enumset1(X29,X26,X27,X28)) )),
% 25.88/3.63    inference(forward_demodulation,[],[f417,f76])).
% 25.88/3.63  fof(f417,plain,(
% 25.88/3.63    ( ! [X28,X26,X29,X27] : (k2_xboole_0(k2_enumset1(X29,X29,X26,X26),k2_enumset1(X27,X27,X27,X28)) = k2_xboole_0(k2_enumset1(X29,X29,X29,X29),k2_enumset1(X27,X26,X28,X28))) )),
% 25.88/3.63    inference(superposition,[],[f48,f221])).
% 25.88/3.63  fof(f221,plain,(
% 25.88/3.63    ( ! [X10,X8,X9] : (k2_enumset1(X8,X8,X9,X10) = k2_enumset1(X9,X8,X10,X10)) )),
% 25.88/3.63    inference(superposition,[],[f55,f46])).
% 25.88/3.63  fof(f55,plain,(
% 25.88/3.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3))) )),
% 25.88/3.63    inference(superposition,[],[f40,f42])).
% 25.88/3.63  fof(f42,plain,(
% 25.88/3.63    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 25.88/3.63    inference(definition_unfolding,[],[f22,f36,f36])).
% 25.88/3.63  fof(f22,plain,(
% 25.88/3.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f1])).
% 25.88/3.63  fof(f1,axiom,(
% 25.88/3.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 25.88/3.63  fof(f48,plain,(
% 25.88/3.63    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X4))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f35,f38,f27,f36])).
% 25.88/3.63  fof(f38,plain,(
% 25.88/3.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 25.88/3.63    inference(definition_unfolding,[],[f34,f37])).
% 25.88/3.63  fof(f34,plain,(
% 25.88/3.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f6])).
% 25.88/3.63  fof(f6,axiom,(
% 25.88/3.63    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 25.88/3.63  fof(f35,plain,(
% 25.88/3.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 25.88/3.63    inference(cnf_transformation,[],[f3])).
% 25.88/3.63  fof(f3,axiom,(
% 25.88/3.63    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 25.88/3.63  fof(f418,plain,(
% 25.88/3.63    ( ! [X30,X33,X31,X32] : (k2_xboole_0(k2_enumset1(X33,X33,X30,X30),k2_enumset1(X31,X31,X31,X32)) = k2_xboole_0(k2_enumset1(X33,X33,X33,X33),k2_enumset1(X30,X31,X32,X32))) )),
% 25.88/3.63    inference(superposition,[],[f48,f65])).
% 25.88/3.63  fof(f41,plain,(
% 25.88/3.63    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 25.88/3.63    inference(definition_unfolding,[],[f20,f25,f36,f37,f36,f26,f26,f26,f26])).
% 25.88/3.63  fof(f26,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f13])).
% 25.88/3.63  fof(f13,axiom,(
% 25.88/3.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 25.88/3.63  fof(f25,plain,(
% 25.88/3.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 25.88/3.63    inference(cnf_transformation,[],[f14])).
% 25.88/3.63  fof(f14,axiom,(
% 25.88/3.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 25.88/3.63  fof(f20,plain,(
% 25.88/3.63    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 25.88/3.63    inference(cnf_transformation,[],[f19])).
% 25.88/3.63  fof(f19,plain,(
% 25.88/3.63    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 25.88/3.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 25.88/3.63  fof(f18,plain,(
% 25.88/3.63    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 25.88/3.63    introduced(choice_axiom,[])).
% 25.88/3.63  fof(f17,plain,(
% 25.88/3.63    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 25.88/3.63    inference(ennf_transformation,[],[f16])).
% 25.88/3.63  fof(f16,negated_conjecture,(
% 25.88/3.63    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 25.88/3.63    inference(negated_conjecture,[],[f15])).
% 25.88/3.63  fof(f15,conjecture,(
% 25.88/3.63    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 25.88/3.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 25.88/3.63  % SZS output end Proof for theBenchmark
% 25.88/3.63  % (20575)------------------------------
% 25.88/3.63  % (20575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.88/3.63  % (20575)Termination reason: Refutation
% 25.88/3.63  
% 25.88/3.63  % (20575)Memory used [KB]: 26993
% 25.88/3.63  % (20575)Time elapsed: 3.169 s
% 25.88/3.63  % (20575)------------------------------
% 25.88/3.63  % (20575)------------------------------
% 25.88/3.64  % (20565)Success in time 3.284 s
%------------------------------------------------------------------------------
