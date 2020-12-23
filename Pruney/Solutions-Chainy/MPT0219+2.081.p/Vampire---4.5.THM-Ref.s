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
% DateTime   : Thu Dec  3 12:35:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 261 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          :   73 ( 314 expanded)
%              Number of equality atoms :   62 ( 246 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(subsumption_resolution,[],[f696,f27])).

fof(f27,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

% (5016)Refutation not found, incomplete strategy% (5016)------------------------------
% (5016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f25,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

% (5016)Termination reason: Refutation not found, incomplete strategy

% (5016)Memory used [KB]: 1663
% (5016)Time elapsed: 0.122 s
% (5016)------------------------------
% (5016)------------------------------
fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f696,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f671,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f671,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f51,f639])).

fof(f639,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f634,f74])).

fof(f74,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f72,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f72,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f36,f49])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f33,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f634,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f37,f601])).

fof(f601,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f597,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f68,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f83,f49])).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f74])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f597,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f359,f574])).

fof(f574,plain,(
    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(superposition,[],[f250,f26])).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f250,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f230,f28])).

fof(f230,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f88,f86])).

fof(f88,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X3,X2),X4)) = k5_xboole_0(k2_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f359,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f100,f358])).

fof(f358,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f84,f351])).

fof(f351,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f330,f85])).

fof(f330,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f76,f329])).

fof(f329,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f305,f28])).

fof(f305,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f89,f86])).

fof(f89,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X6),X7)) = k5_xboole_0(k4_xboole_0(X5,X6),X7) ),
    inference(superposition,[],[f40,f36])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f37])).

fof(f84,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f35,f74])).

fof(f100,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f86])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f32,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5027)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (5005)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (5018)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (5011)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (5007)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (5009)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (5013)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (5028)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (5008)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (5002)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (5029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5018)Refutation not found, incomplete strategy% (5018)------------------------------
% 0.21/0.54  % (5018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5018)Memory used [KB]: 10618
% 0.21/0.54  % (5018)Time elapsed: 0.136 s
% 0.21/0.54  % (5018)------------------------------
% 0.21/0.54  % (5018)------------------------------
% 0.21/0.54  % (5003)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (5021)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (5025)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (5021)Refutation not found, incomplete strategy% (5021)------------------------------
% 0.21/0.54  % (5021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5029)Refutation not found, incomplete strategy% (5029)------------------------------
% 0.21/0.54  % (5029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5021)Memory used [KB]: 1663
% 0.21/0.54  % (5021)Time elapsed: 0.128 s
% 0.21/0.54  % (5021)------------------------------
% 0.21/0.54  % (5021)------------------------------
% 0.21/0.54  % (5030)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (5029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5029)Memory used [KB]: 6140
% 0.21/0.54  % (5029)Time elapsed: 0.127 s
% 0.21/0.54  % (5029)------------------------------
% 0.21/0.54  % (5029)------------------------------
% 0.21/0.55  % (5015)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (5016)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (5023)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (5011)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f697,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f696,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  % (5016)Refutation not found, incomplete strategy% (5016)------------------------------
% 0.21/0.55  % (5016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 0.21/0.55  % (5016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5016)Memory used [KB]: 1663
% 0.21/0.55  % (5016)Time elapsed: 0.122 s
% 0.21/0.55  % (5016)------------------------------
% 0.21/0.55  % (5016)------------------------------
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.55    inference(negated_conjecture,[],[f18])).
% 0.21/0.55  fof(f18,conjecture,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.21/0.55  fof(f696,plain,(
% 0.21/0.55    sK0 = sK1),
% 0.21/0.55    inference(resolution,[],[f671,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.21/0.55  fof(f671,plain,(
% 0.21/0.55    r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f51,f639])).
% 0.21/0.55  fof(f639,plain,(
% 0.21/0.55    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f634,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.21/0.55    inference(forward_demodulation,[],[f72,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f36,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f33,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f30,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f634,plain,(
% 0.21/0.55    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f37,f601])).
% 0.21/0.55  fof(f601,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f597,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f68,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f83,f49])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(superposition,[],[f37,f74])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(superposition,[],[f36,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.55    inference(rectify,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.55  fof(f597,plain,(
% 0.21/0.55    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f359,f574])).
% 0.21/0.55  fof(f574,plain,(
% 0.21/0.55    k1_tarski(sK0) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f250,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = X3) )),
% 0.21/0.55    inference(forward_demodulation,[],[f230,f28])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f88,f86])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X3,X2),X4)) = k5_xboole_0(k2_xboole_0(X2,X3),X4)) )),
% 0.21/0.55    inference(superposition,[],[f40,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.55  fof(f359,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.55    inference(backward_demodulation,[],[f100,f358])).
% 0.21/0.55  fof(f358,plain,(
% 0.21/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.55    inference(backward_demodulation,[],[f84,f351])).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.55    inference(superposition,[],[f330,f85])).
% 0.21/0.55  fof(f330,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.55    inference(backward_demodulation,[],[f76,f329])).
% 0.21/0.55  fof(f329,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f305,f28])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f89,f86])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X6),X7)) = k5_xboole_0(k4_xboole_0(X5,X6),X7)) )),
% 0.21/0.55    inference(superposition,[],[f40,f36])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f35,f37])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(superposition,[],[f35,f74])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f40,f86])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.21/0.55    inference(superposition,[],[f32,f33])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (5011)------------------------------
% 0.21/0.55  % (5011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5011)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (5011)Memory used [KB]: 2174
% 0.21/0.55  % (5011)Time elapsed: 0.139 s
% 0.21/0.55  % (5011)------------------------------
% 0.21/0.55  % (5011)------------------------------
% 0.21/0.55  % (5001)Success in time 0.183 s
%------------------------------------------------------------------------------
