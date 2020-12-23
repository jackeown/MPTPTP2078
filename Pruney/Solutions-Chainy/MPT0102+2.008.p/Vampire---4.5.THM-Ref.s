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
% DateTime   : Thu Dec  3 12:31:57 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 141 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :   53 ( 142 expanded)
%              Number of equality atoms :   52 ( 141 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1602,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1601])).

fof(f1601,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1583,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1583,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1582,f207])).

fof(f207,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f137,f26])).

fof(f137,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X5),X7)) ),
    inference(forward_demodulation,[],[f118,f47])).

fof(f47,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f118,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X5),X7)) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f24,f26])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1582,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1579,f31])).

fof(f1579,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f385,f1577])).

fof(f1577,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X11),k2_xboole_0(X9,X10)) = k4_xboole_0(X11,k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f1535,f37])).

fof(f1535,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X11,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f32,f945])).

fof(f945,plain,(
    ! [X31,X32] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,X32),k2_xboole_0(X31,X32)) ),
    inference(forward_demodulation,[],[f897,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f897,plain,(
    ! [X31,X32] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X31,X32),X32),k2_xboole_0(X31,X32)) ),
    inference(superposition,[],[f750,f317])).

fof(f317,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25 ),
    inference(forward_demodulation,[],[f316,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f316,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0) ),
    inference(forward_demodulation,[],[f288,f40])).

fof(f288,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f750,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f678,f34])).

fof(f678,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f546,f317])).

fof(f546,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X4),X3)) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f385,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f384,f34])).

fof(f384,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f33,f361])).

fof(f361,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6)) ),
    inference(superposition,[],[f31,f317])).

fof(f33,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f27,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (6538)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.47  % (6514)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.48  % (6522)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.48  % (6530)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.49  % (6530)Refutation not found, incomplete strategy% (6530)------------------------------
% 0.22/0.49  % (6530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6530)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (6530)Memory used [KB]: 1663
% 0.22/0.49  % (6530)Time elapsed: 0.095 s
% 0.22/0.49  % (6530)------------------------------
% 0.22/0.49  % (6530)------------------------------
% 0.22/0.49  % (6509)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.49  % (6516)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (6532)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (6524)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (6509)Refutation not found, incomplete strategy% (6509)------------------------------
% 0.22/0.51  % (6509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6509)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6509)Memory used [KB]: 1663
% 0.22/0.51  % (6509)Time elapsed: 0.108 s
% 0.22/0.51  % (6509)------------------------------
% 0.22/0.51  % (6509)------------------------------
% 0.22/0.51  % (6532)Refutation not found, incomplete strategy% (6532)------------------------------
% 0.22/0.51  % (6532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6532)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6532)Memory used [KB]: 1663
% 0.22/0.51  % (6532)Time elapsed: 0.114 s
% 0.22/0.51  % (6532)------------------------------
% 0.22/0.51  % (6532)------------------------------
% 0.22/0.52  % (6520)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (6513)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6511)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (6511)Refutation not found, incomplete strategy% (6511)------------------------------
% 0.22/0.52  % (6511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6511)Memory used [KB]: 10618
% 0.22/0.52  % (6511)Time elapsed: 0.116 s
% 0.22/0.52  % (6511)------------------------------
% 0.22/0.52  % (6511)------------------------------
% 0.22/0.52  % (6512)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (6521)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (6515)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (6531)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (6531)Refutation not found, incomplete strategy% (6531)------------------------------
% 0.22/0.53  % (6531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6531)Memory used [KB]: 10746
% 0.22/0.53  % (6531)Time elapsed: 0.102 s
% 0.22/0.53  % (6531)------------------------------
% 0.22/0.53  % (6531)------------------------------
% 0.22/0.53  % (6537)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (6529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (6528)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (6534)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (6510)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (6523)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (6529)Refutation not found, incomplete strategy% (6529)------------------------------
% 0.22/0.54  % (6529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6517)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (6517)Refutation not found, incomplete strategy% (6517)------------------------------
% 0.22/0.55  % (6517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6517)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6517)Memory used [KB]: 10618
% 0.22/0.55  % (6517)Time elapsed: 0.135 s
% 0.22/0.55  % (6517)------------------------------
% 0.22/0.55  % (6517)------------------------------
% 0.22/0.55  % (6526)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (6529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6529)Memory used [KB]: 10618
% 0.22/0.55  % (6529)Time elapsed: 0.131 s
% 0.22/0.55  % (6529)------------------------------
% 0.22/0.55  % (6529)------------------------------
% 0.22/0.55  % (6526)Refutation not found, incomplete strategy% (6526)------------------------------
% 0.22/0.55  % (6526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6526)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6526)Memory used [KB]: 10618
% 0.22/0.55  % (6526)Time elapsed: 0.140 s
% 0.22/0.55  % (6526)------------------------------
% 0.22/0.55  % (6526)------------------------------
% 1.45/0.55  % (6535)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  % (6518)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (6533)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (6525)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (6519)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.56  % (6519)Refutation not found, incomplete strategy% (6519)------------------------------
% 1.45/0.56  % (6519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (6519)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (6519)Memory used [KB]: 10618
% 1.45/0.56  % (6519)Time elapsed: 0.149 s
% 1.45/0.56  % (6519)------------------------------
% 1.45/0.56  % (6519)------------------------------
% 1.45/0.56  % (6527)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.61/0.61  % (6521)Refutation found. Thanks to Tanya!
% 1.61/0.61  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f1602,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(trivial_inequality_removal,[],[f1601])).
% 1.61/0.61  fof(f1601,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.61/0.61    inference(superposition,[],[f1583,f37])).
% 1.61/0.61  fof(f37,plain,(
% 1.61/0.61    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.61/0.61    inference(superposition,[],[f26,f21])).
% 1.61/0.61  fof(f21,plain,(
% 1.61/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.61    inference(cnf_transformation,[],[f5])).
% 1.61/0.61  fof(f5,axiom,(
% 1.61/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.61/0.61  fof(f26,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.61/0.61  fof(f1583,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.61/0.61    inference(forward_demodulation,[],[f1582,f207])).
% 1.61/0.61  fof(f207,plain,(
% 1.61/0.61    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 1.61/0.61    inference(superposition,[],[f137,f26])).
% 1.61/0.61  fof(f137,plain,(
% 1.61/0.61    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X5),X7))) )),
% 1.61/0.61    inference(forward_demodulation,[],[f118,f47])).
% 1.61/0.61  fof(f47,plain,(
% 1.61/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.61/0.61    inference(superposition,[],[f24,f37])).
% 1.61/0.61  fof(f24,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f11])).
% 1.61/0.61  fof(f11,axiom,(
% 1.61/0.61    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.61/0.61  fof(f118,plain,(
% 1.61/0.61    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X5),X7)) = k4_xboole_0(k1_xboole_0,X7)) )),
% 1.61/0.61    inference(superposition,[],[f31,f40])).
% 1.61/0.61  fof(f40,plain,(
% 1.61/0.61    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 1.61/0.61    inference(superposition,[],[f24,f26])).
% 1.61/0.61  fof(f31,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f9])).
% 1.61/0.61  fof(f9,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.61/0.61  fof(f1582,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.61/0.61    inference(forward_demodulation,[],[f1579,f31])).
% 1.61/0.61  fof(f1579,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.61/0.61    inference(backward_demodulation,[],[f385,f1577])).
% 1.61/0.61  fof(f1577,plain,(
% 1.61/0.61    ( ! [X10,X11,X9] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X11),k2_xboole_0(X9,X10)) = k4_xboole_0(X11,k2_xboole_0(X9,X10))) )),
% 1.61/0.61    inference(forward_demodulation,[],[f1535,f37])).
% 1.61/0.61  fof(f1535,plain,(
% 1.61/0.61    ( ! [X10,X11,X9] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X11),k2_xboole_0(X9,X10)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X11,k2_xboole_0(X9,X10)))) )),
% 1.61/0.61    inference(superposition,[],[f32,f945])).
% 1.61/0.61  fof(f945,plain,(
% 1.61/0.61    ( ! [X31,X32] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,X32),k2_xboole_0(X31,X32))) )),
% 1.61/0.61    inference(forward_demodulation,[],[f897,f28])).
% 1.61/0.61  fof(f28,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f8])).
% 1.61/0.61  fof(f8,axiom,(
% 1.61/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.61/0.61  fof(f897,plain,(
% 1.61/0.61    ( ! [X31,X32] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X31,X32),X32),k2_xboole_0(X31,X32))) )),
% 1.61/0.61    inference(superposition,[],[f750,f317])).
% 1.61/0.61  fof(f317,plain,(
% 1.61/0.61    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25) )),
% 1.61/0.61    inference(forward_demodulation,[],[f316,f22])).
% 1.61/0.61  fof(f22,plain,(
% 1.61/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.61    inference(cnf_transformation,[],[f7])).
% 1.61/0.61  fof(f7,axiom,(
% 1.61/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.61/0.61  fof(f316,plain,(
% 1.61/0.61    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0)) )),
% 1.61/0.61    inference(forward_demodulation,[],[f288,f40])).
% 1.61/0.61  fof(f288,plain,(
% 1.61/0.61    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25))) )),
% 1.61/0.61    inference(superposition,[],[f34,f28])).
% 1.61/0.61  fof(f34,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f25,f27,f27])).
% 1.61/0.61  fof(f27,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f12])).
% 1.61/0.61  fof(f12,axiom,(
% 1.61/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.61  fof(f25,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f2])).
% 1.61/0.61  fof(f2,axiom,(
% 1.61/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.61/0.61  fof(f750,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) )),
% 1.61/0.61    inference(superposition,[],[f678,f34])).
% 1.61/0.61  fof(f678,plain,(
% 1.61/0.61    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X5)) )),
% 1.61/0.61    inference(superposition,[],[f546,f317])).
% 1.61/0.61  fof(f546,plain,(
% 1.61/0.61    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X4),X3))) )),
% 1.61/0.61    inference(superposition,[],[f24,f32])).
% 1.61/0.61  fof(f32,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f10])).
% 1.61/0.61  fof(f10,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.61/0.61  fof(f385,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.61/0.61    inference(forward_demodulation,[],[f384,f34])).
% 1.61/0.61  fof(f384,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 1.61/0.61    inference(backward_demodulation,[],[f33,f361])).
% 1.61/0.61  fof(f361,plain,(
% 1.61/0.61    ( ! [X6,X4,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6))) )),
% 1.61/0.61    inference(superposition,[],[f31,f317])).
% 1.61/0.61  fof(f33,plain,(
% 1.61/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.61/0.61    inference(definition_unfolding,[],[f20,f27,f29,f29])).
% 1.61/0.61  fof(f29,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f3])).
% 1.61/0.61  fof(f3,axiom,(
% 1.61/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.61/0.61  fof(f20,plain,(
% 1.61/0.61    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.61/0.61    inference(cnf_transformation,[],[f19])).
% 1.61/0.61  fof(f19,plain,(
% 1.61/0.61    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 1.61/0.61  fof(f18,plain,(
% 1.61/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f16,plain,(
% 1.61/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.61/0.61    inference(ennf_transformation,[],[f14])).
% 1.61/0.61  fof(f14,negated_conjecture,(
% 1.61/0.61    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.61/0.61    inference(negated_conjecture,[],[f13])).
% 1.61/0.61  fof(f13,conjecture,(
% 1.61/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.61/0.61  % SZS output end Proof for theBenchmark
% 1.61/0.61  % (6521)------------------------------
% 1.61/0.61  % (6521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (6521)Termination reason: Refutation
% 1.61/0.61  
% 1.61/0.61  % (6521)Memory used [KB]: 7164
% 1.61/0.61  % (6521)Time elapsed: 0.185 s
% 1.61/0.61  % (6521)------------------------------
% 1.61/0.61  % (6521)------------------------------
% 1.61/0.62  % (6508)Success in time 0.246 s
%------------------------------------------------------------------------------
