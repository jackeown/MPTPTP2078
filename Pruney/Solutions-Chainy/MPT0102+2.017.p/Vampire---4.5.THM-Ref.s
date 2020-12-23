%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 171 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :   59 ( 172 expanded)
%              Number of equality atoms :   58 ( 171 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2189,plain,(
    $false ),
    inference(subsumption_resolution,[],[f765,f2184])).

fof(f2184,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k5_xboole_0(k2_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f241,f2182])).

fof(f2182,plain,(
    ! [X43,X41,X42] : k3_xboole_0(X41,X42) = k3_xboole_0(k2_xboole_0(X41,X43),k3_xboole_0(X41,X42)) ),
    inference(forward_demodulation,[],[f2135,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2135,plain,(
    ! [X43,X41,X42] : k3_xboole_0(X41,X42) = k3_xboole_0(k2_xboole_0(k2_xboole_0(X41,X43),k1_xboole_0),k3_xboole_0(X41,X42)) ),
    inference(superposition,[],[f1698,f1035])).

fof(f1035,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),k2_xboole_0(X5,X7)) ),
    inference(superposition,[],[f130,f323])).

fof(f323,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f173,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f173,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f164,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f164,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f24,f145])).

fof(f145,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f131,f16])).

fof(f131,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f24,f43])).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f34,f39])).

fof(f39,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f38,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f33,f16])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f21,f16])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f130,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f24,f21])).

fof(f1698,plain,(
    ! [X19,X20] : k3_xboole_0(k2_xboole_0(X20,k4_xboole_0(X19,X20)),X19) = X19 ),
    inference(superposition,[],[f1469,f275])).

fof(f275,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = X1 ),
    inference(forward_demodulation,[],[f264,f18])).

fof(f264,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f21,f138])).

fof(f138,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f24,f43])).

fof(f1469,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f1193,f19])).

fof(f1193,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f1179,f18])).

fof(f1179,plain,(
    ! [X2,X1] : k3_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f21,f1120])).

fof(f1120,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f1034,f19])).

fof(f1034,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f130,f159])).

fof(f159,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f145,f20])).

fof(f241,plain,(
    ! [X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(superposition,[],[f172,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f172,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f170,f17])).

fof(f170,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f66,f159])).

fof(f66,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f52,f24])).

fof(f52,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f765,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f15,f686])).

fof(f686,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f58,f22])).

fof(f58,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f22,f20])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.42  % (21090)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (21089)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (21098)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.46  % (21093)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (21097)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (21091)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (21101)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (21096)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (21099)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (21100)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (21100)Refutation not found, incomplete strategy% (21100)------------------------------
% 0.22/0.49  % (21100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21100)Memory used [KB]: 10490
% 0.22/0.49  % (21100)Time elapsed: 0.071 s
% 0.22/0.49  % (21100)------------------------------
% 0.22/0.49  % (21100)------------------------------
% 0.22/0.49  % (21105)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (21106)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (21094)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (21092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (21095)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (21103)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (21104)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (21102)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.88/0.61  % (21105)Refutation found. Thanks to Tanya!
% 1.88/0.61  % SZS status Theorem for theBenchmark
% 1.88/0.61  % SZS output start Proof for theBenchmark
% 1.88/0.61  fof(f2189,plain,(
% 1.88/0.61    $false),
% 1.88/0.61    inference(subsumption_resolution,[],[f765,f2184])).
% 1.88/0.61  fof(f2184,plain,(
% 1.88/0.61    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k5_xboole_0(k2_xboole_0(X8,X9),k5_xboole_0(X8,X9))) )),
% 1.88/0.61    inference(backward_demodulation,[],[f241,f2182])).
% 1.88/0.61  fof(f2182,plain,(
% 1.88/0.61    ( ! [X43,X41,X42] : (k3_xboole_0(X41,X42) = k3_xboole_0(k2_xboole_0(X41,X43),k3_xboole_0(X41,X42))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f2135,f17])).
% 1.88/0.61  fof(f17,plain,(
% 1.88/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.88/0.61    inference(cnf_transformation,[],[f5])).
% 1.88/0.61  fof(f5,axiom,(
% 1.88/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.88/0.61  fof(f2135,plain,(
% 1.88/0.61    ( ! [X43,X41,X42] : (k3_xboole_0(X41,X42) = k3_xboole_0(k2_xboole_0(k2_xboole_0(X41,X43),k1_xboole_0),k3_xboole_0(X41,X42))) )),
% 1.88/0.61    inference(superposition,[],[f1698,f1035])).
% 1.88/0.61  fof(f1035,plain,(
% 1.88/0.61    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),k2_xboole_0(X5,X7))) )),
% 1.88/0.61    inference(superposition,[],[f130,f323])).
% 1.88/0.61  fof(f323,plain,(
% 1.88/0.61    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 1.88/0.61    inference(superposition,[],[f173,f20])).
% 1.88/0.61  fof(f20,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f1])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.88/0.61  fof(f173,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f164,f16])).
% 1.88/0.61  fof(f16,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f9])).
% 1.88/0.61  fof(f9,axiom,(
% 1.88/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.88/0.61  fof(f164,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.88/0.61    inference(superposition,[],[f24,f145])).
% 1.88/0.61  fof(f145,plain,(
% 1.88/0.61    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f131,f16])).
% 1.88/0.61  fof(f131,plain,(
% 1.88/0.61    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k1_xboole_0,X6)) )),
% 1.88/0.61    inference(superposition,[],[f24,f43])).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.88/0.61    inference(backward_demodulation,[],[f34,f39])).
% 1.88/0.61  fof(f39,plain,(
% 1.88/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.88/0.61    inference(superposition,[],[f38,f19])).
% 1.88/0.61  fof(f19,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f2])).
% 1.88/0.61  fof(f2,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.88/0.61  fof(f38,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.88/0.61    inference(forward_demodulation,[],[f33,f16])).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.88/0.61    inference(superposition,[],[f21,f16])).
% 1.88/0.61  fof(f21,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f8])).
% 1.88/0.61  fof(f8,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.88/0.61  fof(f34,plain,(
% 1.88/0.61    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 1.88/0.61    inference(superposition,[],[f21,f18])).
% 1.88/0.61  fof(f18,plain,(
% 1.88/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.88/0.61    inference(cnf_transformation,[],[f6])).
% 1.88/0.61  fof(f6,axiom,(
% 1.88/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.88/0.61  fof(f130,plain,(
% 1.88/0.61    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4)) )),
% 1.88/0.61    inference(superposition,[],[f24,f21])).
% 1.88/0.61  fof(f1698,plain,(
% 1.88/0.61    ( ! [X19,X20] : (k3_xboole_0(k2_xboole_0(X20,k4_xboole_0(X19,X20)),X19) = X19) )),
% 1.88/0.61    inference(superposition,[],[f1469,f275])).
% 1.88/0.61  fof(f275,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = X1) )),
% 1.88/0.61    inference(forward_demodulation,[],[f264,f18])).
% 1.88/0.61  fof(f264,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 1.88/0.61    inference(superposition,[],[f21,f138])).
% 1.88/0.61  fof(f138,plain,(
% 1.88/0.61    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 1.88/0.61    inference(superposition,[],[f24,f43])).
% 1.88/0.61  fof(f1469,plain,(
% 1.88/0.61    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 1.88/0.61    inference(superposition,[],[f1193,f19])).
% 1.88/0.61  fof(f1193,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X2)) )),
% 1.88/0.61    inference(forward_demodulation,[],[f1179,f18])).
% 1.88/0.61  fof(f1179,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k3_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) )),
% 1.88/0.61    inference(superposition,[],[f21,f1120])).
% 1.88/0.61  fof(f1120,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1)) )),
% 1.88/0.61    inference(superposition,[],[f1034,f19])).
% 1.88/0.61  fof(f1034,plain,(
% 1.88/0.61    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X3)) )),
% 1.88/0.61    inference(superposition,[],[f130,f159])).
% 1.88/0.61  fof(f159,plain,(
% 1.88/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.88/0.61    inference(superposition,[],[f145,f20])).
% 1.88/0.61  fof(f241,plain,(
% 1.88/0.61    ( ! [X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k5_xboole_0(X8,X9))) )),
% 1.88/0.61    inference(superposition,[],[f172,f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 1.88/0.61  fof(f172,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f170,f17])).
% 1.88/0.61  fof(f170,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0)) )),
% 1.88/0.61    inference(backward_demodulation,[],[f66,f159])).
% 1.88/0.61  fof(f66,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 1.88/0.61    inference(forward_demodulation,[],[f52,f24])).
% 1.88/0.61  fof(f52,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2))) )),
% 1.88/0.61    inference(superposition,[],[f22,f21])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.88/0.61  fof(f765,plain,(
% 1.88/0.61    k3_xboole_0(sK0,sK1) != k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.88/0.61    inference(superposition,[],[f15,f686])).
% 1.88/0.61  fof(f686,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 1.88/0.61    inference(superposition,[],[f58,f22])).
% 1.88/0.61  fof(f58,plain,(
% 1.88/0.61    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) )),
% 1.88/0.61    inference(superposition,[],[f22,f20])).
% 1.88/0.61  fof(f15,plain,(
% 1.88/0.61    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.88/0.61    inference(cnf_transformation,[],[f14])).
% 1.88/0.61  fof(f14,plain,(
% 1.88/0.61    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 1.88/0.61  fof(f13,plain,(
% 1.88/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f12,plain,(
% 1.88/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.88/0.61    inference(ennf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,negated_conjecture,(
% 1.88/0.61    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.88/0.61    inference(negated_conjecture,[],[f10])).
% 1.88/0.61  fof(f10,conjecture,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (21105)------------------------------
% 1.88/0.61  % (21105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (21105)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (21105)Memory used [KB]: 7803
% 1.88/0.61  % (21105)Time elapsed: 0.155 s
% 1.88/0.61  % (21105)------------------------------
% 1.88/0.61  % (21105)------------------------------
% 1.88/0.61  % (21088)Success in time 0.257 s
%------------------------------------------------------------------------------
