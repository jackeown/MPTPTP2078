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
% DateTime   : Thu Dec  3 12:35:43 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  78 expanded)
%              Number of equality atoms :   38 (  71 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f289,f104])).

fof(f104,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(superposition,[],[f96,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f96,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f84,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f84,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(superposition,[],[f32,f57])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f47,f33])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f289,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f266,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) ),
    inference(unit_resulting_resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f266,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f45,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f32,f33])).

fof(f45,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f42,f24,f43,f42])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (20884)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (20892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (20875)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (20872)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (20872)Refutation not found, incomplete strategy% (20872)------------------------------
% 0.21/0.51  % (20872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20872)Memory used [KB]: 1663
% 0.21/0.51  % (20872)Time elapsed: 0.104 s
% 0.21/0.51  % (20872)------------------------------
% 0.21/0.51  % (20872)------------------------------
% 0.21/0.51  % (20873)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (20874)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (20876)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (20893)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (20891)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (20890)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (20886)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (20900)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.53  % (20885)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.53  % (20900)Refutation not found, incomplete strategy% (20900)------------------------------
% 1.38/0.53  % (20900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (20900)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (20900)Memory used [KB]: 1663
% 1.38/0.53  % (20900)Time elapsed: 0.122 s
% 1.38/0.53  % (20900)------------------------------
% 1.38/0.53  % (20900)------------------------------
% 1.38/0.54  % (20885)Refutation not found, incomplete strategy% (20885)------------------------------
% 1.38/0.54  % (20885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20885)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (20885)Memory used [KB]: 1663
% 1.38/0.54  % (20885)Time elapsed: 0.089 s
% 1.38/0.54  % (20885)------------------------------
% 1.38/0.54  % (20885)------------------------------
% 1.38/0.54  % (20895)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.54  % (20871)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.54  % (20895)Refutation not found, incomplete strategy% (20895)------------------------------
% 1.38/0.54  % (20895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20895)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (20895)Memory used [KB]: 10618
% 1.38/0.54  % (20895)Time elapsed: 0.127 s
% 1.38/0.54  % (20895)------------------------------
% 1.38/0.54  % (20895)------------------------------
% 1.38/0.54  % (20882)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.54  % (20894)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (20889)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.54  % (20889)Refutation not found, incomplete strategy% (20889)------------------------------
% 1.38/0.54  % (20889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20889)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (20889)Memory used [KB]: 1663
% 1.38/0.54  % (20889)Time elapsed: 0.104 s
% 1.38/0.54  % (20889)------------------------------
% 1.38/0.54  % (20889)------------------------------
% 1.38/0.54  % (20882)Refutation not found, incomplete strategy% (20882)------------------------------
% 1.38/0.54  % (20882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20882)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (20882)Memory used [KB]: 6140
% 1.38/0.54  % (20882)Time elapsed: 0.138 s
% 1.38/0.54  % (20882)------------------------------
% 1.38/0.54  % (20882)------------------------------
% 1.38/0.54  % (20896)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.54  % (20896)Refutation not found, incomplete strategy% (20896)------------------------------
% 1.38/0.54  % (20896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20883)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.54  % (20888)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.54  % (20877)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (20879)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.54  % (20883)Refutation not found, incomplete strategy% (20883)------------------------------
% 1.38/0.54  % (20883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (20883)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (20883)Memory used [KB]: 10618
% 1.38/0.54  % (20883)Time elapsed: 0.139 s
% 1.38/0.54  % (20883)------------------------------
% 1.38/0.54  % (20883)------------------------------
% 1.38/0.54  % (20890)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f290,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(subsumption_resolution,[],[f289,f104])).
% 1.38/0.55  fof(f104,plain,(
% 1.38/0.55    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.38/0.55    inference(superposition,[],[f96,f33])).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.38/0.55  fof(f96,plain,(
% 1.38/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.38/0.55    inference(forward_demodulation,[],[f84,f51])).
% 1.38/0.55  fof(f51,plain,(
% 1.38/0.55    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f36,f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.55  fof(f36,plain,(
% 1.38/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.55  fof(f84,plain,(
% 1.38/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1) )),
% 1.38/0.55    inference(superposition,[],[f32,f57])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ( ! [X0] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.38/0.55    inference(superposition,[],[f47,f33])).
% 1.38/0.55  fof(f47,plain,(
% 1.38/0.55    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f26,f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f10])).
% 1.38/0.55  fof(f10,axiom,(
% 1.38/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.38/0.55  fof(f32,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.38/0.55  fof(f289,plain,(
% 1.38/0.55    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)),
% 1.38/0.55    inference(forward_demodulation,[],[f266,f120])).
% 1.38/0.55  fof(f120,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)))) )),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f48,f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f34,f30])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.38/0.55  fof(f48,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f27,f43,f42])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.38/0.55    inference(definition_unfolding,[],[f29,f41])).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f14])).
% 1.38/0.55  fof(f14,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,axiom,(
% 1.38/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.38/0.55    inference(definition_unfolding,[],[f28,f42])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,axiom,(
% 1.38/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f19])).
% 1.38/0.55  fof(f19,axiom,(
% 1.38/0.55    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.38/0.55  fof(f266,plain,(
% 1.38/0.55    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))))),
% 1.38/0.55    inference(superposition,[],[f45,f76])).
% 1.38/0.55  fof(f76,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 1.38/0.55    inference(superposition,[],[f32,f33])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.38/0.55    inference(definition_unfolding,[],[f23,f42,f24,f43,f42])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f21])).
% 1.38/0.55  fof(f21,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.38/0.55    inference(negated_conjecture,[],[f20])).
% 1.38/0.55  fof(f20,conjecture,(
% 1.38/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (20890)------------------------------
% 1.38/0.55  % (20890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (20890)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (20890)Memory used [KB]: 1918
% 1.38/0.55  % (20890)Time elapsed: 0.133 s
% 1.38/0.55  % (20890)------------------------------
% 1.38/0.55  % (20890)------------------------------
% 1.38/0.55  % (20899)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (20887)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (20887)Refutation not found, incomplete strategy% (20887)------------------------------
% 1.38/0.55  % (20887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (20887)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (20887)Memory used [KB]: 10618
% 1.38/0.55  % (20887)Time elapsed: 0.138 s
% 1.38/0.55  % (20887)------------------------------
% 1.38/0.55  % (20887)------------------------------
% 1.38/0.55  % (20899)Refutation not found, incomplete strategy% (20899)------------------------------
% 1.38/0.55  % (20899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (20899)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (20899)Memory used [KB]: 10746
% 1.38/0.55  % (20899)Time elapsed: 0.139 s
% 1.38/0.55  % (20899)------------------------------
% 1.38/0.55  % (20899)------------------------------
% 1.38/0.55  % (20881)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.55  % (20897)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (20888)Refutation not found, incomplete strategy% (20888)------------------------------
% 1.38/0.55  % (20888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (20888)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (20888)Memory used [KB]: 1663
% 1.38/0.55  % (20888)Time elapsed: 0.149 s
% 1.38/0.55  % (20888)------------------------------
% 1.38/0.55  % (20888)------------------------------
% 1.38/0.55  % (20896)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (20896)Memory used [KB]: 6140
% 1.38/0.55  % (20896)Time elapsed: 0.140 s
% 1.38/0.55  % (20896)------------------------------
% 1.38/0.55  % (20896)------------------------------
% 1.38/0.55  % (20897)Refutation not found, incomplete strategy% (20897)------------------------------
% 1.38/0.55  % (20897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (20878)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (20897)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (20897)Memory used [KB]: 6140
% 1.38/0.55  % (20897)Time elapsed: 0.147 s
% 1.38/0.55  % (20897)------------------------------
% 1.38/0.55  % (20897)------------------------------
% 1.38/0.55  % (20880)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.62/0.55  % (20881)Refutation not found, incomplete strategy% (20881)------------------------------
% 1.62/0.55  % (20881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.55  % (20881)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.55  
% 1.62/0.55  % (20881)Memory used [KB]: 10746
% 1.62/0.55  % (20881)Time elapsed: 0.148 s
% 1.62/0.55  % (20881)------------------------------
% 1.62/0.55  % (20881)------------------------------
% 1.62/0.56  % (20898)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.62/0.57  % (20870)Success in time 0.207 s
%------------------------------------------------------------------------------
