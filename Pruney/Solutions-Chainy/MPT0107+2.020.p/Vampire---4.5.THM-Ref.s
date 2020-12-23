%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:12 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 292 expanded)
%              Number of leaves         :   15 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :   78 ( 297 expanded)
%              Number of equality atoms :   77 ( 296 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2378,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f2377])).

fof(f2377,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f2359,f155])).

fof(f155,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10 ),
    inference(forward_demodulation,[],[f152,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f152,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k1_xboole_0) ),
    inference(superposition,[],[f29,f118])).

fof(f118,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f112,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f112,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(forward_demodulation,[],[f105,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f60,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f30,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f69,f64])).

fof(f64,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f61,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f61,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f30,f30])).

fof(f69,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2359,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(X9,k3_xboole_0(X9,X10)),k3_xboole_0(X9,X10)) ),
    inference(backward_demodulation,[],[f1899,f2352])).

fof(f2352,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(subsumption_resolution,[],[f2319,f1968])).

fof(f1968,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f243,f1966])).

fof(f1966,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f1944,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1944,plain,(
    ! [X10,X9] : k5_xboole_0(X9,X9) = k4_xboole_0(X9,k2_xboole_0(X10,X9)) ),
    inference(superposition,[],[f1501,f1672])).

fof(f1672,plain,(
    ! [X14,X13] : k5_xboole_0(k4_xboole_0(X13,k2_xboole_0(X14,X13)),X13) = X13 ),
    inference(forward_demodulation,[],[f1639,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1639,plain,(
    ! [X14,X13] : k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),X13),X13) = X13 ),
    inference(superposition,[],[f1522,f128])).

fof(f128,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f125,f25])).

fof(f125,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f29,f112])).

fof(f1522,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) = X10 ),
    inference(superposition,[],[f1501,f29])).

fof(f1501,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f1497,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1497,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1480,f46])).

fof(f46,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f28,f25])).

fof(f1480,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f243,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f32,f92])).

fof(f92,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f87,f29])).

fof(f87,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2319,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8))
      | k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ) ),
    inference(superposition,[],[f33,f1968])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1899,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(k3_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10)) ),
    inference(backward_demodulation,[],[f1773,f1898])).

fof(f1898,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f62,f1866])).

fof(f1866,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f1595,f31])).

fof(f1595,plain,(
    ! [X14,X13] : k2_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,X13),X13) ),
    inference(superposition,[],[f1520,f1504])).

fof(f1504,plain,(
    ! [X8,X9] : k4_xboole_0(X9,X8) = k5_xboole_0(X8,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f1497,f29])).

fof(f1520,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f1501,f1501])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f30])).

fof(f1773,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10)) ),
    inference(superposition,[],[f1541,f30])).

fof(f1541,plain,(
    ! [X10,X11] : k5_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = X10 ),
    inference(superposition,[],[f1519,f29])).

fof(f1519,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f1501,f1497])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (25819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (25836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (25828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (25836)Refutation not found, incomplete strategy% (25836)------------------------------
% 0.20/0.52  % (25836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25836)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25836)Memory used [KB]: 10618
% 0.20/0.52  % (25836)Time elapsed: 0.107 s
% 0.20/0.52  % (25836)------------------------------
% 0.20/0.52  % (25836)------------------------------
% 0.20/0.53  % (25820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (25837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (25837)Refutation not found, incomplete strategy% (25837)------------------------------
% 0.20/0.53  % (25837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25837)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25837)Memory used [KB]: 1663
% 0.20/0.53  % (25837)Time elapsed: 0.078 s
% 0.20/0.53  % (25837)------------------------------
% 0.20/0.53  % (25837)------------------------------
% 0.20/0.53  % (25829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (25817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (25816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (25824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (25816)Refutation not found, incomplete strategy% (25816)------------------------------
% 0.20/0.54  % (25816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25816)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25816)Memory used [KB]: 10618
% 0.20/0.54  % (25816)Time elapsed: 0.123 s
% 0.20/0.54  % (25816)------------------------------
% 0.20/0.54  % (25816)------------------------------
% 0.20/0.54  % (25838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (25818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (25821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (25823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (25815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (25835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (25835)Refutation not found, incomplete strategy% (25835)------------------------------
% 0.20/0.54  % (25835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25835)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25835)Memory used [KB]: 1663
% 0.20/0.54  % (25835)Time elapsed: 0.126 s
% 0.20/0.54  % (25835)------------------------------
% 0.20/0.54  % (25835)------------------------------
% 0.20/0.54  % (25814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (25825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (25814)Refutation not found, incomplete strategy% (25814)------------------------------
% 0.20/0.54  % (25814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25814)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25814)Memory used [KB]: 1663
% 0.20/0.54  % (25814)Time elapsed: 0.094 s
% 0.20/0.54  % (25814)------------------------------
% 0.20/0.54  % (25814)------------------------------
% 0.20/0.55  % (25840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (25833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (25827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (25841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (25843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (25822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (25839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (25830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (25831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (25832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (25822)Refutation not found, incomplete strategy% (25822)------------------------------
% 0.20/0.56  % (25822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (25822)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (25822)Memory used [KB]: 10618
% 0.20/0.56  % (25822)Time elapsed: 0.149 s
% 0.20/0.56  % (25822)------------------------------
% 0.20/0.56  % (25822)------------------------------
% 0.20/0.56  % (25831)Refutation not found, incomplete strategy% (25831)------------------------------
% 0.20/0.56  % (25831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (25831)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (25831)Memory used [KB]: 10618
% 0.20/0.57  % (25831)Time elapsed: 0.151 s
% 0.20/0.57  % (25831)------------------------------
% 0.20/0.57  % (25831)------------------------------
% 0.20/0.57  % (25834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (25842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.59  % (25826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (25834)Refutation not found, incomplete strategy% (25834)------------------------------
% 0.20/0.59  % (25834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (25834)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (25834)Memory used [KB]: 10618
% 0.20/0.59  % (25834)Time elapsed: 0.148 s
% 0.20/0.59  % (25834)------------------------------
% 0.20/0.59  % (25834)------------------------------
% 2.21/0.68  % (25847)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.68  % (25847)Refutation not found, incomplete strategy% (25847)------------------------------
% 2.21/0.68  % (25847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (25847)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.68  
% 2.21/0.68  % (25847)Memory used [KB]: 6140
% 2.21/0.68  % (25847)Time elapsed: 0.083 s
% 2.21/0.68  % (25847)------------------------------
% 2.21/0.68  % (25847)------------------------------
% 2.21/0.70  % (25849)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.69/0.75  % (25856)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.69/0.75  % (25848)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.69/0.76  % (25821)Refutation found. Thanks to Tanya!
% 2.69/0.76  % SZS status Theorem for theBenchmark
% 2.69/0.76  % SZS output start Proof for theBenchmark
% 2.69/0.76  fof(f2378,plain,(
% 2.69/0.76    $false),
% 2.69/0.76    inference(subsumption_resolution,[],[f22,f2377])).
% 2.69/0.76  fof(f2377,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10))) )),
% 2.69/0.76    inference(forward_demodulation,[],[f2359,f155])).
% 2.69/0.76  fof(f155,plain,(
% 2.69/0.76    ( ! [X10,X11] : (k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10) )),
% 2.69/0.76    inference(forward_demodulation,[],[f152,f25])).
% 2.69/0.76  fof(f25,plain,(
% 2.69/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.76    inference(cnf_transformation,[],[f12])).
% 2.69/0.76  fof(f12,axiom,(
% 2.69/0.76    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.69/0.76  fof(f152,plain,(
% 2.69/0.76    ( ! [X10,X11] : (k2_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k1_xboole_0)) )),
% 2.69/0.76    inference(superposition,[],[f29,f118])).
% 2.69/0.76  fof(f118,plain,(
% 2.69/0.76    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 2.69/0.76    inference(superposition,[],[f112,f30])).
% 2.69/0.76  fof(f30,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.69/0.76    inference(cnf_transformation,[],[f9])).
% 2.69/0.76  fof(f9,axiom,(
% 2.69/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.69/0.76  fof(f112,plain,(
% 2.69/0.76    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 2.69/0.76    inference(forward_demodulation,[],[f105,f63])).
% 2.69/0.76  fof(f63,plain,(
% 2.69/0.76    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.69/0.76    inference(forward_demodulation,[],[f60,f23])).
% 2.69/0.76  fof(f23,plain,(
% 2.69/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.69/0.76    inference(cnf_transformation,[],[f3])).
% 2.69/0.76  fof(f3,axiom,(
% 2.69/0.76    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.69/0.76  fof(f60,plain,(
% 2.69/0.76    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.69/0.76    inference(superposition,[],[f30,f26])).
% 2.69/0.76  fof(f26,plain,(
% 2.69/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.76    inference(cnf_transformation,[],[f5])).
% 2.69/0.76  fof(f5,axiom,(
% 2.69/0.76    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.69/0.76  fof(f105,plain,(
% 2.69/0.76    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 2.69/0.76    inference(superposition,[],[f69,f64])).
% 2.69/0.76  fof(f64,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.69/0.76    inference(forward_demodulation,[],[f61,f31])).
% 2.69/0.76  fof(f31,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.69/0.76    inference(cnf_transformation,[],[f8])).
% 2.69/0.76  fof(f8,axiom,(
% 2.69/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.69/0.76  fof(f61,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.69/0.76    inference(superposition,[],[f30,f30])).
% 2.69/0.76  fof(f69,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.69/0.76    inference(superposition,[],[f31,f27])).
% 2.69/0.76  fof(f27,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.69/0.76    inference(cnf_transformation,[],[f1])).
% 2.69/0.76  fof(f1,axiom,(
% 2.69/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.69/0.76  fof(f29,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.69/0.76    inference(cnf_transformation,[],[f15])).
% 2.69/0.76  fof(f15,axiom,(
% 2.69/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.69/0.76  fof(f2359,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(X9,k3_xboole_0(X9,X10)),k3_xboole_0(X9,X10))) )),
% 2.69/0.76    inference(backward_demodulation,[],[f1899,f2352])).
% 2.69/0.76  fof(f2352,plain,(
% 2.69/0.76    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7)) )),
% 2.69/0.76    inference(subsumption_resolution,[],[f2319,f1968])).
% 2.69/0.76  fof(f1968,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 2.69/0.76    inference(backward_demodulation,[],[f243,f1966])).
% 2.69/0.76  fof(f1966,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,X9))) )),
% 2.69/0.76    inference(forward_demodulation,[],[f1944,f24])).
% 2.69/0.76  fof(f24,plain,(
% 2.69/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.69/0.76    inference(cnf_transformation,[],[f14])).
% 2.69/0.76  fof(f14,axiom,(
% 2.69/0.76    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.69/0.76  fof(f1944,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k5_xboole_0(X9,X9) = k4_xboole_0(X9,k2_xboole_0(X10,X9))) )),
% 2.69/0.76    inference(superposition,[],[f1501,f1672])).
% 2.69/0.76  fof(f1672,plain,(
% 2.69/0.76    ( ! [X14,X13] : (k5_xboole_0(k4_xboole_0(X13,k2_xboole_0(X14,X13)),X13) = X13) )),
% 2.69/0.76    inference(forward_demodulation,[],[f1639,f36])).
% 2.69/0.76  fof(f36,plain,(
% 2.69/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.69/0.76    inference(cnf_transformation,[],[f7])).
% 2.69/0.76  fof(f7,axiom,(
% 2.69/0.76    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.69/0.76  fof(f1639,plain,(
% 2.69/0.76    ( ! [X14,X13] : (k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),X13),X13) = X13) )),
% 2.69/0.76    inference(superposition,[],[f1522,f128])).
% 2.69/0.76  fof(f128,plain,(
% 2.69/0.76    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 2.69/0.76    inference(forward_demodulation,[],[f125,f25])).
% 2.69/0.76  fof(f125,plain,(
% 2.69/0.76    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.69/0.76    inference(superposition,[],[f29,f112])).
% 2.69/0.76  fof(f1522,plain,(
% 2.69/0.76    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) = X10) )),
% 2.69/0.76    inference(superposition,[],[f1501,f29])).
% 2.69/0.76  fof(f1501,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.69/0.76    inference(superposition,[],[f1497,f28])).
% 2.69/0.76  fof(f28,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.69/0.76    inference(cnf_transformation,[],[f2])).
% 2.69/0.76  fof(f2,axiom,(
% 2.69/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.69/0.76  fof(f1497,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.69/0.76    inference(forward_demodulation,[],[f1480,f46])).
% 2.69/0.76  fof(f46,plain,(
% 2.69/0.76    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.69/0.76    inference(superposition,[],[f28,f25])).
% 2.69/0.76  fof(f1480,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.69/0.76    inference(superposition,[],[f35,f24])).
% 2.69/0.76  fof(f35,plain,(
% 2.69/0.76    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.69/0.76    inference(cnf_transformation,[],[f13])).
% 2.69/0.76  fof(f13,axiom,(
% 2.69/0.76    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.69/0.76  fof(f243,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 2.69/0.76    inference(superposition,[],[f32,f92])).
% 2.69/0.76  fof(f92,plain,(
% 2.69/0.76    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2)) )),
% 2.69/0.76    inference(forward_demodulation,[],[f87,f29])).
% 2.69/0.76  fof(f87,plain,(
% 2.69/0.76    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 2.69/0.76    inference(superposition,[],[f29,f32])).
% 2.69/0.76  fof(f32,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.69/0.76    inference(cnf_transformation,[],[f6])).
% 2.69/0.76  fof(f6,axiom,(
% 2.69/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.69/0.76  fof(f2319,plain,(
% 2.69/0.76    ( ! [X8,X7] : (k1_xboole_0 != k4_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8)) | k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7)) )),
% 2.69/0.76    inference(superposition,[],[f33,f1968])).
% 2.69/0.76  fof(f33,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.69/0.76    inference(cnf_transformation,[],[f19])).
% 2.69/0.76  fof(f19,plain,(
% 2.69/0.76    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.69/0.76    inference(ennf_transformation,[],[f4])).
% 2.69/0.76  fof(f4,axiom,(
% 2.69/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.69/0.76  fof(f1899,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(k3_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10))) )),
% 2.69/0.76    inference(backward_demodulation,[],[f1773,f1898])).
% 2.69/0.76  fof(f1898,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.69/0.76    inference(backward_demodulation,[],[f62,f1866])).
% 2.69/0.76  fof(f1866,plain,(
% 2.69/0.76    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))) )),
% 2.69/0.76    inference(superposition,[],[f1595,f31])).
% 2.69/0.76  fof(f1595,plain,(
% 2.69/0.76    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k5_xboole_0(k4_xboole_0(X14,X13),X13)) )),
% 2.69/0.76    inference(superposition,[],[f1520,f1504])).
% 2.69/0.76  fof(f1504,plain,(
% 2.69/0.76    ( ! [X8,X9] : (k4_xboole_0(X9,X8) = k5_xboole_0(X8,k2_xboole_0(X8,X9))) )),
% 2.69/0.76    inference(superposition,[],[f1497,f29])).
% 2.69/0.76  fof(f1520,plain,(
% 2.69/0.76    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 2.69/0.76    inference(superposition,[],[f1501,f1501])).
% 2.69/0.76  fof(f62,plain,(
% 2.69/0.76    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.69/0.76    inference(superposition,[],[f29,f30])).
% 2.69/0.76  fof(f1773,plain,(
% 2.69/0.76    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10))) )),
% 2.69/0.76    inference(superposition,[],[f1541,f30])).
% 2.69/0.76  fof(f1541,plain,(
% 2.69/0.76    ( ! [X10,X11] : (k5_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)) = X10) )),
% 2.69/0.76    inference(superposition,[],[f1519,f29])).
% 2.69/0.76  fof(f1519,plain,(
% 2.69/0.76    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.69/0.76    inference(superposition,[],[f1501,f1497])).
% 2.69/0.76  fof(f22,plain,(
% 2.69/0.76    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.69/0.76    inference(cnf_transformation,[],[f21])).
% 2.69/0.76  fof(f21,plain,(
% 2.69/0.76    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.69/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 2.69/0.76  fof(f20,plain,(
% 2.69/0.76    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.69/0.76    introduced(choice_axiom,[])).
% 2.69/0.76  fof(f18,plain,(
% 2.69/0.76    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.76    inference(ennf_transformation,[],[f17])).
% 2.69/0.76  fof(f17,negated_conjecture,(
% 2.69/0.76    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.76    inference(negated_conjecture,[],[f16])).
% 2.69/0.76  fof(f16,conjecture,(
% 2.69/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.69/0.76  % SZS output end Proof for theBenchmark
% 2.69/0.76  % (25821)------------------------------
% 2.69/0.76  % (25821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.76  % (25821)Termination reason: Refutation
% 2.69/0.76  
% 2.69/0.76  % (25821)Memory used [KB]: 7675
% 2.69/0.76  % (25821)Time elapsed: 0.299 s
% 2.69/0.76  % (25821)------------------------------
% 2.69/0.76  % (25821)------------------------------
% 2.69/0.76  % (25813)Success in time 0.397 s
%------------------------------------------------------------------------------
