%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:11 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  55 expanded)
%              Number of equality atoms :   40 (  54 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f720,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f719])).

fof(f719,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f696,f42])).

fof(f42,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f39,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f39,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f696,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f680,f24])).

fof(f680,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f421,f660])).

fof(f660,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f434,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f434,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f430,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f430,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f415,f118])).

fof(f118,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(backward_demodulation,[],[f56,f110])).

fof(f110,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f107,f23])).

fof(f107,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f102,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f102,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f56,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = k5_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f25,f21])).

fof(f415,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f421,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (8010)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.52  % (8031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.52  % (8021)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (8020)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (8023)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (8031)Refutation not found, incomplete strategy% (8031)------------------------------
% 1.23/0.53  % (8031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (8031)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (8031)Memory used [KB]: 10618
% 1.23/0.53  % (8031)Time elapsed: 0.080 s
% 1.23/0.53  % (8031)------------------------------
% 1.23/0.53  % (8031)------------------------------
% 1.23/0.53  % (8025)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.53  % (8015)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.54  % (8011)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (8011)Refutation not found, incomplete strategy% (8011)------------------------------
% 1.23/0.54  % (8011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (8011)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (8011)Memory used [KB]: 10618
% 1.23/0.54  % (8011)Time elapsed: 0.126 s
% 1.23/0.54  % (8011)------------------------------
% 1.23/0.54  % (8011)------------------------------
% 1.23/0.54  % (8017)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (8012)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (8017)Refutation not found, incomplete strategy% (8017)------------------------------
% 1.38/0.54  % (8017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (8027)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (8014)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (8017)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (8017)Memory used [KB]: 10618
% 1.38/0.54  % (8017)Time elapsed: 0.140 s
% 1.38/0.54  % (8017)------------------------------
% 1.38/0.54  % (8017)------------------------------
% 1.38/0.55  % (8034)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (8032)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (8032)Refutation not found, incomplete strategy% (8032)------------------------------
% 1.38/0.55  % (8032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (8032)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (8032)Memory used [KB]: 1663
% 1.38/0.55  % (8032)Time elapsed: 0.125 s
% 1.38/0.55  % (8032)------------------------------
% 1.38/0.55  % (8032)------------------------------
% 1.38/0.55  % (8013)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.55  % (8026)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (8009)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (8036)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (8026)Refutation not found, incomplete strategy% (8026)------------------------------
% 1.38/0.55  % (8026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (8026)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (8026)Memory used [KB]: 10618
% 1.38/0.55  % (8026)Time elapsed: 0.147 s
% 1.38/0.55  % (8026)------------------------------
% 1.38/0.55  % (8026)------------------------------
% 1.38/0.55  % (8009)Refutation not found, incomplete strategy% (8009)------------------------------
% 1.38/0.55  % (8009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (8009)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (8009)Memory used [KB]: 1663
% 1.38/0.55  % (8009)Time elapsed: 0.142 s
% 1.38/0.55  % (8009)------------------------------
% 1.38/0.55  % (8009)------------------------------
% 1.38/0.56  % (8037)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.56  % (8018)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.56  % (8019)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.56  % (8035)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.56  % (8029)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.56  % (8016)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (8028)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (8029)Refutation not found, incomplete strategy% (8029)------------------------------
% 1.38/0.56  % (8029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (8029)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (8029)Memory used [KB]: 10618
% 1.38/0.56  % (8029)Time elapsed: 0.161 s
% 1.38/0.56  % (8029)------------------------------
% 1.38/0.56  % (8029)------------------------------
% 1.38/0.57  % (8033)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.58  % (8030)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.58  % (8022)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.58  % (8024)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.58  % (8030)Refutation not found, incomplete strategy% (8030)------------------------------
% 1.38/0.58  % (8030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (8030)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (8030)Memory used [KB]: 1663
% 1.38/0.58  % (8030)Time elapsed: 0.150 s
% 1.38/0.58  % (8030)------------------------------
% 1.38/0.58  % (8030)------------------------------
% 1.38/0.60  % (8016)Refutation found. Thanks to Tanya!
% 1.38/0.60  % SZS status Theorem for theBenchmark
% 1.38/0.60  % SZS output start Proof for theBenchmark
% 1.38/0.60  fof(f720,plain,(
% 1.38/0.60    $false),
% 1.38/0.60    inference(subsumption_resolution,[],[f19,f719])).
% 1.38/0.60  fof(f719,plain,(
% 1.38/0.60    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 1.38/0.60    inference(forward_demodulation,[],[f696,f42])).
% 1.38/0.60  fof(f42,plain,(
% 1.38/0.60    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.38/0.60    inference(forward_demodulation,[],[f39,f26])).
% 1.38/0.60  fof(f26,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f7])).
% 1.38/0.60  fof(f7,axiom,(
% 1.38/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.38/0.60  fof(f39,plain,(
% 1.38/0.60    ( ! [X6,X5] : (k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 1.38/0.60    inference(superposition,[],[f24,f24])).
% 1.38/0.60  fof(f24,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f8])).
% 1.38/0.60  fof(f8,axiom,(
% 1.38/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.60  fof(f696,plain,(
% 1.38/0.60    ( ! [X6,X5] : (k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 1.38/0.60    inference(superposition,[],[f680,f24])).
% 1.38/0.60  fof(f680,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.60    inference(backward_demodulation,[],[f421,f660])).
% 1.38/0.60  fof(f660,plain,(
% 1.38/0.60    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.38/0.60    inference(superposition,[],[f434,f23])).
% 1.38/0.60  fof(f23,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f1])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.38/0.60  fof(f434,plain,(
% 1.38/0.60    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 1.38/0.60    inference(superposition,[],[f430,f25])).
% 1.38/0.60  fof(f25,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f12])).
% 1.38/0.61  fof(f12,axiom,(
% 1.38/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.61  fof(f430,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.38/0.61    inference(forward_demodulation,[],[f415,f118])).
% 1.38/0.61  fof(f118,plain,(
% 1.38/0.61    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) )),
% 1.38/0.61    inference(backward_demodulation,[],[f56,f110])).
% 1.38/0.61  fof(f110,plain,(
% 1.38/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.38/0.61    inference(superposition,[],[f107,f23])).
% 1.38/0.61  fof(f107,plain,(
% 1.38/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.38/0.61    inference(forward_demodulation,[],[f102,f21])).
% 1.38/0.61  fof(f21,plain,(
% 1.38/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.61    inference(cnf_transformation,[],[f3])).
% 1.38/0.61  fof(f3,axiom,(
% 1.38/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.61  fof(f102,plain,(
% 1.38/0.61    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.38/0.61    inference(superposition,[],[f27,f21])).
% 1.38/0.61  fof(f27,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f4])).
% 1.38/0.61  fof(f4,axiom,(
% 1.38/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.38/0.61  fof(f56,plain,(
% 1.38/0.61    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = k5_xboole_0(k1_xboole_0,X7)) )),
% 1.38/0.61    inference(superposition,[],[f25,f21])).
% 1.38/0.61  fof(f415,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.38/0.61    inference(superposition,[],[f30,f20])).
% 1.38/0.61  fof(f20,plain,(
% 1.38/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f10])).
% 1.38/0.61  fof(f10,axiom,(
% 1.38/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.38/0.61  fof(f30,plain,(
% 1.38/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.38/0.61    inference(cnf_transformation,[],[f9])).
% 1.38/0.61  fof(f9,axiom,(
% 1.38/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.38/0.61  fof(f421,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.38/0.61    inference(superposition,[],[f30,f28])).
% 1.38/0.61  fof(f28,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.38/0.61    inference(cnf_transformation,[],[f11])).
% 1.38/0.61  fof(f11,axiom,(
% 1.38/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.38/0.61  fof(f19,plain,(
% 1.38/0.61    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.61    inference(cnf_transformation,[],[f18])).
% 1.38/0.61  fof(f18,plain,(
% 1.38/0.61    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.38/0.61  fof(f17,plain,(
% 1.38/0.61    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.61    introduced(choice_axiom,[])).
% 1.38/0.61  fof(f15,plain,(
% 1.38/0.61    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.61    inference(ennf_transformation,[],[f14])).
% 1.38/0.61  fof(f14,negated_conjecture,(
% 1.38/0.61    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.61    inference(negated_conjecture,[],[f13])).
% 1.38/0.61  fof(f13,conjecture,(
% 1.38/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.61  % SZS output end Proof for theBenchmark
% 1.38/0.61  % (8016)------------------------------
% 1.38/0.61  % (8016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.61  % (8016)Termination reason: Refutation
% 1.38/0.61  
% 1.38/0.61  % (8016)Memory used [KB]: 6780
% 1.38/0.61  % (8016)Time elapsed: 0.189 s
% 1.38/0.61  % (8016)------------------------------
% 1.38/0.61  % (8016)------------------------------
% 1.38/0.61  % (8006)Success in time 0.238 s
%------------------------------------------------------------------------------
