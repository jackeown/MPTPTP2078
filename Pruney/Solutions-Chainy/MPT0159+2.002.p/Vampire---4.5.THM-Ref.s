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
% DateTime   : Thu Dec  3 12:33:49 EST 2020

% Result     : Theorem 36.71s
% Output     : Refutation 36.71s
% Verified   : 
% Statistics : Number of formulae       :   35 (  51 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  52 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10835,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10833,f10755])).

fof(f10755,plain,(
    ! [X30,X35,X33,X31,X36,X34,X32] : k5_enumset1(X33,X34,X35,X36,X30,X31,X32) = k5_enumset1(X34,X35,X36,X30,X31,X32,X33) ),
    inference(superposition,[],[f1078,f1078])).

fof(f1078,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10) ),
    inference(superposition,[],[f256,f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f256,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) ),
    inference(superposition,[],[f26,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f10833,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK6,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(superposition,[],[f17,f1913])).

fof(f1913,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X13,X7,X8,X9,X10,X11,X12) = k6_enumset1(X7,X7,X8,X9,X10,X11,X12,X13) ),
    inference(forward_demodulation,[],[f1889,f905])).

fof(f905,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f888,f27])).

fof(f888,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_enumset1(X6,X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f57,f356])).

fof(f356,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f342,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f342,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f27,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_enumset1(X6,X7,X8),X9)) = k2_xboole_0(k2_enumset1(X5,X6,X7,X8),X9) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1889,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k1_tarski(X13),k4_enumset1(X7,X8,X9,X10,X11,X12)) = k6_enumset1(X7,X7,X8,X9,X10,X11,X12,X13) ),
    inference(superposition,[],[f482,f18])).

fof(f482,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f17,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:46:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (12318)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (12310)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (12305)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (12319)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (12306)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (12307)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (12313)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (12311)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (12317)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (12309)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (12315)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (12321)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (12314)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (12322)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (12320)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (12316)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (12308)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (12316)Refutation not found, incomplete strategy% (12316)------------------------------
% 0.22/0.51  % (12316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12312)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (12316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12316)Memory used [KB]: 10618
% 0.22/0.52  % (12316)Time elapsed: 0.099 s
% 0.22/0.52  % (12316)------------------------------
% 0.22/0.52  % (12316)------------------------------
% 5.14/1.04  % (12309)Time limit reached!
% 5.14/1.04  % (12309)------------------------------
% 5.14/1.04  % (12309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.04  % (12309)Termination reason: Time limit
% 5.14/1.04  % (12309)Termination phase: Saturation
% 5.14/1.04  
% 5.14/1.04  % (12309)Memory used [KB]: 15351
% 5.14/1.04  % (12309)Time elapsed: 0.600 s
% 5.14/1.04  % (12309)------------------------------
% 5.14/1.04  % (12309)------------------------------
% 12.41/1.96  % (12310)Time limit reached!
% 12.41/1.96  % (12310)------------------------------
% 12.41/1.96  % (12310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.41/1.96  % (12310)Termination reason: Time limit
% 12.41/1.96  
% 12.41/1.96  % (12310)Memory used [KB]: 40553
% 12.41/1.96  % (12310)Time elapsed: 1.531 s
% 12.41/1.96  % (12310)------------------------------
% 12.41/1.96  % (12310)------------------------------
% 12.41/2.01  % (12311)Time limit reached!
% 12.41/2.01  % (12311)------------------------------
% 12.41/2.01  % (12311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.41/2.01  % (12311)Termination reason: Time limit
% 12.41/2.01  % (12311)Termination phase: Saturation
% 12.41/2.01  
% 12.41/2.01  % (12311)Memory used [KB]: 39018
% 12.41/2.01  % (12311)Time elapsed: 1.500 s
% 12.41/2.01  % (12311)------------------------------
% 12.41/2.01  % (12311)------------------------------
% 14.79/2.26  % (12307)Time limit reached!
% 14.79/2.26  % (12307)------------------------------
% 14.79/2.26  % (12307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.79/2.26  % (12307)Termination reason: Time limit
% 14.79/2.26  % (12307)Termination phase: Saturation
% 14.79/2.26  
% 14.79/2.26  % (12307)Memory used [KB]: 37611
% 14.79/2.26  % (12307)Time elapsed: 1.800 s
% 14.79/2.26  % (12307)------------------------------
% 14.79/2.26  % (12307)------------------------------
% 18.02/2.62  % (12317)Time limit reached!
% 18.02/2.62  % (12317)------------------------------
% 18.02/2.62  % (12317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.02/2.62  % (12317)Termination reason: Time limit
% 18.02/2.62  % (12317)Termination phase: Saturation
% 18.02/2.62  
% 18.02/2.62  % (12317)Memory used [KB]: 36715
% 18.02/2.62  % (12317)Time elapsed: 2.200 s
% 18.02/2.62  % (12317)------------------------------
% 18.02/2.62  % (12317)------------------------------
% 36.71/4.99  % (12308)Refutation found. Thanks to Tanya!
% 36.71/4.99  % SZS status Theorem for theBenchmark
% 36.71/4.99  % SZS output start Proof for theBenchmark
% 36.71/4.99  fof(f10835,plain,(
% 36.71/4.99    $false),
% 36.71/4.99    inference(subsumption_resolution,[],[f10833,f10755])).
% 36.71/4.99  fof(f10755,plain,(
% 36.71/4.99    ( ! [X30,X35,X33,X31,X36,X34,X32] : (k5_enumset1(X33,X34,X35,X36,X30,X31,X32) = k5_enumset1(X34,X35,X36,X30,X31,X32,X33)) )),
% 36.71/4.99    inference(superposition,[],[f1078,f1078])).
% 36.71/4.99  fof(f1078,plain,(
% 36.71/4.99    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10)) )),
% 36.71/4.99    inference(superposition,[],[f256,f27])).
% 36.71/4.99  fof(f27,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 36.71/4.99    inference(cnf_transformation,[],[f4])).
% 36.71/4.99  fof(f4,axiom,(
% 36.71/4.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 36.71/4.99  fof(f256,plain,(
% 36.71/4.99    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)) )),
% 36.71/4.99    inference(superposition,[],[f26,f18])).
% 36.71/4.99  fof(f18,plain,(
% 36.71/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 36.71/4.99    inference(cnf_transformation,[],[f1])).
% 36.71/4.99  fof(f1,axiom,(
% 36.71/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 36.71/4.99  fof(f26,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 36.71/4.99    inference(cnf_transformation,[],[f6])).
% 36.71/4.99  fof(f6,axiom,(
% 36.71/4.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 36.71/4.99  fof(f10833,plain,(
% 36.71/4.99    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK6,sK0,sK1,sK2,sK3,sK4,sK5)),
% 36.71/4.99    inference(superposition,[],[f17,f1913])).
% 36.71/4.99  fof(f1913,plain,(
% 36.71/4.99    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X13,X7,X8,X9,X10,X11,X12) = k6_enumset1(X7,X7,X8,X9,X10,X11,X12,X13)) )),
% 36.71/4.99    inference(forward_demodulation,[],[f1889,f905])).
% 36.71/4.99  fof(f905,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)) )),
% 36.71/4.99    inference(forward_demodulation,[],[f888,f27])).
% 36.71/4.99  fof(f888,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_enumset1(X6,X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 36.71/4.99    inference(superposition,[],[f57,f356])).
% 36.71/4.99  fof(f356,plain,(
% 36.71/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 36.71/4.99    inference(forward_demodulation,[],[f342,f25])).
% 36.71/4.99  fof(f25,plain,(
% 36.71/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 36.71/4.99    inference(cnf_transformation,[],[f11])).
% 36.71/4.99  fof(f11,axiom,(
% 36.71/4.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 36.71/4.99  fof(f342,plain,(
% 36.71/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 36.71/4.99    inference(superposition,[],[f27,f20])).
% 36.71/4.99  fof(f20,plain,(
% 36.71/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 36.71/4.99    inference(cnf_transformation,[],[f8])).
% 36.71/4.99  fof(f8,axiom,(
% 36.71/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 36.71/4.99  fof(f57,plain,(
% 36.71/4.99    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_enumset1(X6,X7,X8),X9)) = k2_xboole_0(k2_enumset1(X5,X6,X7,X8),X9)) )),
% 36.71/4.99    inference(superposition,[],[f21,f23])).
% 36.71/4.99  fof(f23,plain,(
% 36.71/4.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 36.71/4.99    inference(cnf_transformation,[],[f5])).
% 36.71/4.99  fof(f5,axiom,(
% 36.71/4.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 36.71/4.99  fof(f21,plain,(
% 36.71/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 36.71/4.99    inference(cnf_transformation,[],[f2])).
% 36.71/4.99  fof(f2,axiom,(
% 36.71/4.99    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 36.71/4.99  fof(f1889,plain,(
% 36.71/4.99    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k1_tarski(X13),k4_enumset1(X7,X8,X9,X10,X11,X12)) = k6_enumset1(X7,X7,X8,X9,X10,X11,X12,X13)) )),
% 36.71/4.99    inference(superposition,[],[f482,f18])).
% 36.71/4.99  fof(f482,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 36.71/4.99    inference(superposition,[],[f28,f25])).
% 36.71/4.99  fof(f28,plain,(
% 36.71/4.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 36.71/4.99    inference(cnf_transformation,[],[f7])).
% 36.71/4.99  fof(f7,axiom,(
% 36.71/4.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 36.71/4.99  fof(f17,plain,(
% 36.71/4.99    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 36.71/4.99    inference(cnf_transformation,[],[f16])).
% 36.71/4.99  fof(f16,plain,(
% 36.71/4.99    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 36.71/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f15])).
% 36.71/4.99  fof(f15,plain,(
% 36.71/4.99    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 36.71/4.99    introduced(choice_axiom,[])).
% 36.71/4.99  fof(f14,plain,(
% 36.71/4.99    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 36.71/4.99    inference(ennf_transformation,[],[f13])).
% 36.71/4.99  fof(f13,negated_conjecture,(
% 36.71/4.99    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 36.71/4.99    inference(negated_conjecture,[],[f12])).
% 36.71/4.99  fof(f12,conjecture,(
% 36.71/4.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 36.71/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 36.71/4.99  % SZS output end Proof for theBenchmark
% 36.71/4.99  % (12308)------------------------------
% 36.71/4.99  % (12308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.71/4.99  % (12308)Termination reason: Refutation
% 36.71/4.99  
% 36.71/4.99  % (12308)Memory used [KB]: 115264
% 36.71/4.99  % (12308)Time elapsed: 4.568 s
% 36.71/4.99  % (12308)------------------------------
% 36.71/4.99  % (12308)------------------------------
% 36.98/5.00  % (12303)Success in time 4.633 s
%------------------------------------------------------------------------------
