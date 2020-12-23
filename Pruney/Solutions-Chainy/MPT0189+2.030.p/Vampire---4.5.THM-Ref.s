%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 303 expanded)
%              Number of leaves         :   11 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          :   50 ( 304 expanded)
%              Number of equality atoms :   49 ( 303 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f956,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f942])).

fof(f942,plain,(
    ! [X30,X28,X31,X29] : k2_enumset1(X28,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31) ),
    inference(superposition,[],[f514,f380])).

fof(f380,plain,(
    ! [X30,X28,X31,X29] : k3_enumset1(X28,X29,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31) ),
    inference(forward_demodulation,[],[f374,f309])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f295,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f295,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f294,f78])).

fof(f78,plain,(
    ! [X21,X19,X20] : k1_enumset1(X19,X20,X21) = k2_enumset1(X19,X19,X21,X20) ),
    inference(superposition,[],[f31,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f294,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f293,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f293,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f292,f32])).

fof(f292,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f291,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f291,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f36,f33])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f374,plain,(
    ! [X30,X28,X31,X29] : k3_enumset1(X28,X29,X29,X30,X31) = k2_xboole_0(k1_enumset1(X29,X30,X28),k1_tarski(X31)) ),
    inference(superposition,[],[f294,f356])).

fof(f356,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X40,X38) ),
    inference(forward_demodulation,[],[f353,f354])).

fof(f354,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f343,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f30,f29])).

fof(f343,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f309,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f353,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40)) ),
    inference(superposition,[],[f309,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f514,plain,(
    ! [X39,X37,X38,X36] : k3_enumset1(X36,X37,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(forward_demodulation,[],[f507,f309])).

fof(f507,plain,(
    ! [X39,X37,X38,X36] : k3_enumset1(X36,X37,X37,X38,X39) = k2_xboole_0(k1_enumset1(X36,X38,X37),k1_tarski(X39)) ),
    inference(superposition,[],[f294,f398])).

fof(f398,plain,(
    ! [X19,X17,X18] : k1_enumset1(X17,X19,X18) = k2_enumset1(X17,X18,X18,X19) ),
    inference(forward_demodulation,[],[f396,f354])).

fof(f396,plain,(
    ! [X19,X17,X18] : k2_enumset1(X17,X18,X18,X19) = k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19)) ),
    inference(superposition,[],[f309,f378])).

fof(f378,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29) ),
    inference(forward_demodulation,[],[f364,f43])).

fof(f364,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28) ),
    inference(superposition,[],[f356,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f23,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (10150)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (10158)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (10151)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10148)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (10162)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10158)Refutation not found, incomplete strategy% (10158)------------------------------
% 0.21/0.48  % (10158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10158)Memory used [KB]: 10618
% 0.21/0.48  % (10158)Time elapsed: 0.058 s
% 0.21/0.48  % (10158)------------------------------
% 0.21/0.48  % (10158)------------------------------
% 0.21/0.48  % (10146)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (10147)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (10154)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10161)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (10159)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (10163)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (10155)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (10153)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (10164)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (10157)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (10156)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10152)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (10160)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.34/0.53  % (10163)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f956,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(subsumption_resolution,[],[f23,f942])).
% 1.34/0.53  fof(f942,plain,(
% 1.34/0.53    ( ! [X30,X28,X31,X29] : (k2_enumset1(X28,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31)) )),
% 1.34/0.53    inference(superposition,[],[f514,f380])).
% 1.34/0.53  fof(f380,plain,(
% 1.34/0.53    ( ! [X30,X28,X31,X29] : (k3_enumset1(X28,X29,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f374,f309])).
% 1.34/0.53  fof(f309,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.34/0.53    inference(forward_demodulation,[],[f295,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.53  fof(f295,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.34/0.53    inference(superposition,[],[f294,f78])).
% 1.34/0.53  fof(f78,plain,(
% 1.34/0.53    ( ! [X21,X19,X20] : (k1_enumset1(X19,X20,X21) = k2_enumset1(X19,X19,X21,X20)) )),
% 1.34/0.53    inference(superposition,[],[f31,f55])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) )),
% 1.34/0.53    inference(superposition,[],[f30,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 1.34/0.53  fof(f294,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.34/0.53    inference(forward_demodulation,[],[f293,f33])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.34/0.53  fof(f293,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.34/0.53    inference(superposition,[],[f292,f32])).
% 1.34/0.53  fof(f292,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.34/0.53    inference(forward_demodulation,[],[f291,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.34/0.53  fof(f291,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.34/0.53    inference(superposition,[],[f36,f33])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 1.34/0.53  fof(f374,plain,(
% 1.34/0.53    ( ! [X30,X28,X31,X29] : (k3_enumset1(X28,X29,X29,X30,X31) = k2_xboole_0(k1_enumset1(X29,X30,X28),k1_tarski(X31))) )),
% 1.34/0.53    inference(superposition,[],[f294,f356])).
% 1.34/0.53  fof(f356,plain,(
% 1.34/0.53    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X40,X38)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f353,f354])).
% 1.34/0.53  fof(f354,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.34/0.53    inference(forward_demodulation,[],[f343,f57])).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 1.34/0.53    inference(superposition,[],[f30,f29])).
% 1.34/0.53  fof(f343,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.34/0.53    inference(superposition,[],[f309,f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.53  fof(f353,plain,(
% 1.34/0.53    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40))) )),
% 1.34/0.53    inference(superposition,[],[f309,f43])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 1.34/0.53    inference(superposition,[],[f28,f25])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.34/0.53  fof(f514,plain,(
% 1.34/0.53    ( ! [X39,X37,X38,X36] : (k3_enumset1(X36,X37,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f507,f309])).
% 1.34/0.53  fof(f507,plain,(
% 1.34/0.53    ( ! [X39,X37,X38,X36] : (k3_enumset1(X36,X37,X37,X38,X39) = k2_xboole_0(k1_enumset1(X36,X38,X37),k1_tarski(X39))) )),
% 1.34/0.53    inference(superposition,[],[f294,f398])).
% 1.34/0.53  fof(f398,plain,(
% 1.34/0.53    ( ! [X19,X17,X18] : (k1_enumset1(X17,X19,X18) = k2_enumset1(X17,X18,X18,X19)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f396,f354])).
% 1.34/0.53  fof(f396,plain,(
% 1.34/0.53    ( ! [X19,X17,X18] : (k2_enumset1(X17,X18,X18,X19) = k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19))) )),
% 1.34/0.53    inference(superposition,[],[f309,f378])).
% 1.34/0.53  fof(f378,plain,(
% 1.34/0.53    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f364,f43])).
% 1.34/0.53  fof(f364,plain,(
% 1.34/0.53    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28)) )),
% 1.34/0.53    inference(superposition,[],[f356,f75])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) )),
% 1.34/0.53    inference(superposition,[],[f31,f29])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.34/0.53    inference(cnf_transformation,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.34/0.53    inference(ennf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.34/0.53    inference(negated_conjecture,[],[f18])).
% 1.34/0.53  fof(f18,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (10163)------------------------------
% 1.34/0.53  % (10163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (10163)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (10163)Memory used [KB]: 6780
% 1.34/0.53  % (10163)Time elapsed: 0.112 s
% 1.34/0.53  % (10163)------------------------------
% 1.34/0.53  % (10163)------------------------------
% 1.34/0.54  % (10142)Success in time 0.182 s
%------------------------------------------------------------------------------
