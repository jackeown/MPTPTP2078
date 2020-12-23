%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:11 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 159 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   64 ( 160 expanded)
%              Number of equality atoms :   63 ( 159 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f2241])).

fof(f2241,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f1680,f2239])).

fof(f2239,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(forward_demodulation,[],[f2191,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2191,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f2117,f229])).

fof(f229,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f224,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f224,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k1_xboole_0) ),
    inference(superposition,[],[f31,f205])).

fof(f205,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f196,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f28,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f48,f26])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f196,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f87,f73])).

fof(f73,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f65,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f65,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f87,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2117,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2066,f1794])).

fof(f1794,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f205])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2066,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X7))) ),
    inference(superposition,[],[f1920,f106])).

fof(f106,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f101,f31])).

fof(f101,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1920,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f105,f1917])).

fof(f1917,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X6,X5)) = X5 ),
    inference(forward_demodulation,[],[f1894,f27])).

fof(f1894,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f32,f1794])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f100,f29])).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f34])).

fof(f1680,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),X8),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f1395,f32])).

fof(f1395,plain,(
    ! [X10,X9] : k5_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9 ),
    inference(superposition,[],[f1374,f31])).

fof(f1374,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f1356,f1352])).

fof(f1352,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1335,f40])).

fof(f40,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1335,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1356,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f1352,f30])).

fof(f23,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:25 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.47  % (30369)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.48  % (30380)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.48  % (30369)Refutation not found, incomplete strategy% (30369)------------------------------
% 0.22/0.48  % (30369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30369)Memory used [KB]: 10618
% 0.22/0.48  % (30369)Time elapsed: 0.063 s
% 0.22/0.48  % (30369)------------------------------
% 0.22/0.48  % (30369)------------------------------
% 0.22/0.52  % (30365)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (30363)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (30364)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (30381)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (30381)Refutation not found, incomplete strategy% (30381)------------------------------
% 0.22/0.53  % (30381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30381)Memory used [KB]: 10618
% 0.22/0.53  % (30381)Time elapsed: 0.114 s
% 0.22/0.53  % (30381)------------------------------
% 0.22/0.53  % (30381)------------------------------
% 0.22/0.53  % (30361)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (30361)Refutation not found, incomplete strategy% (30361)------------------------------
% 0.22/0.53  % (30361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30361)Memory used [KB]: 1663
% 0.22/0.53  % (30361)Time elapsed: 0.115 s
% 0.22/0.53  % (30361)------------------------------
% 0.22/0.53  % (30361)------------------------------
% 0.22/0.53  % (30373)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (30367)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30377)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (30371)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (30378)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (30378)Refutation not found, incomplete strategy% (30378)------------------------------
% 0.22/0.54  % (30378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30378)Memory used [KB]: 10618
% 0.22/0.54  % (30378)Time elapsed: 0.132 s
% 0.22/0.54  % (30378)------------------------------
% 0.22/0.54  % (30378)------------------------------
% 0.22/0.54  % (30366)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (30374)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (30387)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (30363)Refutation not found, incomplete strategy% (30363)------------------------------
% 0.22/0.54  % (30363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30363)Memory used [KB]: 10618
% 0.22/0.54  % (30363)Time elapsed: 0.128 s
% 0.22/0.54  % (30363)------------------------------
% 0.22/0.54  % (30363)------------------------------
% 0.22/0.54  % (30376)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (30382)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (30372)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (30382)Refutation not found, incomplete strategy% (30382)------------------------------
% 0.22/0.55  % (30382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30382)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30382)Memory used [KB]: 1663
% 0.22/0.55  % (30382)Time elapsed: 0.134 s
% 0.22/0.55  % (30382)------------------------------
% 0.22/0.55  % (30382)------------------------------
% 0.22/0.55  % (30383)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (30385)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (30362)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (30383)Refutation not found, incomplete strategy% (30383)------------------------------
% 0.22/0.55  % (30383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30383)Memory used [KB]: 10618
% 0.22/0.55  % (30383)Time elapsed: 0.116 s
% 0.22/0.55  % (30383)------------------------------
% 0.22/0.55  % (30383)------------------------------
% 0.22/0.55  % (30368)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (30370)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (30389)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (30388)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (30391)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (30384)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (30375)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (30384)Refutation not found, incomplete strategy% (30384)------------------------------
% 0.22/0.56  % (30384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (30384)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (30384)Memory used [KB]: 1663
% 0.22/0.56  % (30384)Time elapsed: 0.140 s
% 0.22/0.56  % (30384)------------------------------
% 0.22/0.56  % (30384)------------------------------
% 0.22/0.56  % (30379)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (30386)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.60  % (30392)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.79/0.60  % (30392)Refutation not found, incomplete strategy% (30392)------------------------------
% 1.79/0.60  % (30392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (30392)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (30392)Memory used [KB]: 6140
% 1.79/0.60  % (30392)Time elapsed: 0.027 s
% 1.79/0.60  % (30392)------------------------------
% 1.79/0.60  % (30392)------------------------------
% 2.00/0.67  % (30394)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.00/0.67  % (30393)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.00/0.68  % (30397)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.00/0.68  % (30395)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.68  % (30396)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.00/0.69  % (30368)Refutation found. Thanks to Tanya!
% 2.00/0.69  % SZS status Theorem for theBenchmark
% 2.00/0.69  % SZS output start Proof for theBenchmark
% 2.00/0.69  fof(f2245,plain,(
% 2.00/0.69    $false),
% 2.00/0.69    inference(subsumption_resolution,[],[f23,f2241])).
% 2.00/0.69  fof(f2241,plain,(
% 2.00/0.69    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) )),
% 2.00/0.69    inference(backward_demodulation,[],[f1680,f2239])).
% 2.00/0.69  fof(f2239,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 2.00/0.69    inference(forward_demodulation,[],[f2191,f27])).
% 2.00/0.69  fof(f27,plain,(
% 2.00/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/0.69    inference(cnf_transformation,[],[f5])).
% 2.00/0.69  fof(f5,axiom,(
% 2.00/0.69    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.00/0.69  fof(f2191,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.00/0.69    inference(superposition,[],[f2117,f229])).
% 2.00/0.69  fof(f229,plain,(
% 2.00/0.69    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 2.00/0.69    inference(forward_demodulation,[],[f224,f26])).
% 2.00/0.69  fof(f26,plain,(
% 2.00/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/0.69    inference(cnf_transformation,[],[f13])).
% 2.00/0.69  fof(f13,axiom,(
% 2.00/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.00/0.69  fof(f224,plain,(
% 2.00/0.69    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k1_xboole_0)) )),
% 2.00/0.69    inference(superposition,[],[f31,f205])).
% 2.00/0.69  fof(f205,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.00/0.69    inference(forward_demodulation,[],[f196,f58])).
% 2.00/0.69  fof(f58,plain,(
% 2.00/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.00/0.69    inference(superposition,[],[f28,f53])).
% 2.00/0.69  fof(f53,plain,(
% 2.00/0.69    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/0.69    inference(forward_demodulation,[],[f48,f26])).
% 2.00/0.69  fof(f48,plain,(
% 2.00/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 2.00/0.69    inference(superposition,[],[f31,f24])).
% 2.00/0.69  fof(f24,plain,(
% 2.00/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f12])).
% 2.00/0.69  fof(f12,axiom,(
% 2.00/0.69    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.00/0.69  fof(f28,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f8])).
% 2.00/0.69  fof(f8,axiom,(
% 2.00/0.69    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.00/0.69  fof(f196,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.00/0.69    inference(superposition,[],[f87,f73])).
% 2.00/0.69  fof(f73,plain,(
% 2.00/0.69    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f65,f33])).
% 2.00/0.69  fof(f33,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f9])).
% 2.00/0.69  fof(f9,axiom,(
% 2.00/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.00/0.69  fof(f65,plain,(
% 2.00/0.69    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.00/0.69    inference(superposition,[],[f32,f32])).
% 2.00/0.69  fof(f32,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f10])).
% 2.00/0.69  fof(f10,axiom,(
% 2.00/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.00/0.69  fof(f87,plain,(
% 2.00/0.69    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.00/0.69    inference(superposition,[],[f33,f29])).
% 2.00/0.69  fof(f29,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f1])).
% 2.00/0.69  fof(f1,axiom,(
% 2.00/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.00/0.69  fof(f31,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f16])).
% 2.00/0.69  fof(f16,axiom,(
% 2.00/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.00/0.69  fof(f2117,plain,(
% 2.00/0.69    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0)) )),
% 2.00/0.69    inference(forward_demodulation,[],[f2066,f1794])).
% 2.00/0.69  fof(f1794,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.00/0.69    inference(superposition,[],[f38,f205])).
% 2.00/0.69  fof(f38,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f7])).
% 2.00/0.69  fof(f7,axiom,(
% 2.00/0.69    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.00/0.69  fof(f2066,plain,(
% 2.00/0.69    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X7)))) )),
% 2.00/0.69    inference(superposition,[],[f1920,f106])).
% 2.00/0.69  fof(f106,plain,(
% 2.00/0.69    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2)) )),
% 2.00/0.69    inference(forward_demodulation,[],[f101,f31])).
% 2.00/0.69  fof(f101,plain,(
% 2.00/0.69    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 2.00/0.69    inference(superposition,[],[f31,f34])).
% 2.00/0.69  fof(f34,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f6])).
% 2.00/0.69  fof(f6,axiom,(
% 2.00/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.00/0.69  fof(f1920,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1) )),
% 2.00/0.69    inference(backward_demodulation,[],[f105,f1917])).
% 2.00/0.69  fof(f1917,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X6,X5)) = X5) )),
% 2.00/0.69    inference(forward_demodulation,[],[f1894,f27])).
% 2.00/0.69  fof(f1894,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 2.00/0.69    inference(superposition,[],[f32,f1794])).
% 2.00/0.69  fof(f105,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(forward_demodulation,[],[f100,f29])).
% 2.00/0.69  fof(f100,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(superposition,[],[f32,f34])).
% 2.00/0.69  fof(f1680,plain,(
% 2.00/0.69    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),X8),k3_xboole_0(X8,X9))) )),
% 2.00/0.69    inference(superposition,[],[f1395,f32])).
% 2.00/0.69  fof(f1395,plain,(
% 2.00/0.69    ( ! [X10,X9] : (k5_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9) )),
% 2.00/0.69    inference(superposition,[],[f1374,f31])).
% 2.00/0.69  fof(f1374,plain,(
% 2.00/0.69    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.00/0.69    inference(superposition,[],[f1356,f1352])).
% 2.00/0.69  fof(f1352,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.00/0.69    inference(forward_demodulation,[],[f1335,f40])).
% 2.00/0.69  fof(f40,plain,(
% 2.00/0.69    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.00/0.69    inference(superposition,[],[f30,f26])).
% 2.00/0.69  fof(f30,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f2])).
% 2.00/0.69  fof(f2,axiom,(
% 2.00/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.00/0.69  fof(f1335,plain,(
% 2.00/0.69    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.00/0.69    inference(superposition,[],[f37,f25])).
% 2.00/0.69  fof(f25,plain,(
% 2.00/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.00/0.69    inference(cnf_transformation,[],[f15])).
% 2.00/0.69  fof(f15,axiom,(
% 2.00/0.69    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.00/0.69  fof(f37,plain,(
% 2.00/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.00/0.69    inference(cnf_transformation,[],[f14])).
% 2.00/0.69  fof(f14,axiom,(
% 2.00/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.00/0.69  fof(f1356,plain,(
% 2.00/0.69    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.00/0.69    inference(superposition,[],[f1352,f30])).
% 2.00/0.69  fof(f23,plain,(
% 2.00/0.69    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.00/0.69    inference(cnf_transformation,[],[f22])).
% 2.00/0.69  fof(f22,plain,(
% 2.00/0.69    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.00/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 2.00/0.69  fof(f21,plain,(
% 2.00/0.69    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.00/0.69    introduced(choice_axiom,[])).
% 2.00/0.69  fof(f19,plain,(
% 2.00/0.69    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/0.69    inference(ennf_transformation,[],[f18])).
% 2.00/0.69  fof(f18,negated_conjecture,(
% 2.00/0.69    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/0.69    inference(negated_conjecture,[],[f17])).
% 2.00/0.69  fof(f17,conjecture,(
% 2.00/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.00/0.69  % SZS output end Proof for theBenchmark
% 2.00/0.69  % (30368)------------------------------
% 2.00/0.69  % (30368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (30368)Termination reason: Refutation
% 2.00/0.69  
% 2.00/0.69  % (30368)Memory used [KB]: 7675
% 2.00/0.69  % (30368)Time elapsed: 0.261 s
% 2.00/0.69  % (30368)------------------------------
% 2.00/0.69  % (30368)------------------------------
% 2.00/0.69  % (30398)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.00/0.69  % (30360)Success in time 0.313 s
%------------------------------------------------------------------------------
