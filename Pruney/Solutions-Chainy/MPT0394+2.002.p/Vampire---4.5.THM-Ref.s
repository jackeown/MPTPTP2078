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
% DateTime   : Thu Dec  3 12:45:56 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  88 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(subsumption_resolution,[],[f431,f83])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(forward_demodulation,[],[f81,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f76,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f57,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f431,plain,(
    k1_xboole_0 = k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f426,f82])).

fof(f426,plain,(
    k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f164,f424])).

fof(f424,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(forward_demodulation,[],[f423,f47])).

fof(f47,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f423,plain,(
    ! [X0,X1] : k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k4_xboole_0(k1_setfam_1(k1_tarski(X0)),X1)) ),
    inference(forward_demodulation,[],[f404,f47])).

fof(f404,plain,(
    ! [X0,X1] : k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k1_tarski(X1)))) ),
    inference(unit_resulting_resolution,[],[f83,f83,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f164,plain,(
    k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_tarski(k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))) ),
    inference(unit_resulting_resolution,[],[f66,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f34,f41,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f34,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (28086)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (28088)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (28105)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (28105)Refutation not found, incomplete strategy% (28105)------------------------------
% 0.22/0.57  % (28105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (28105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (28105)Memory used [KB]: 6268
% 0.22/0.57  % (28105)Time elapsed: 0.137 s
% 0.22/0.57  % (28105)------------------------------
% 0.22/0.57  % (28105)------------------------------
% 0.22/0.57  % (28104)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (28089)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (28102)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (28089)Refutation not found, incomplete strategy% (28089)------------------------------
% 0.22/0.57  % (28089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (28097)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (28089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (28089)Memory used [KB]: 10746
% 0.22/0.57  % (28089)Time elapsed: 0.136 s
% 0.22/0.57  % (28089)------------------------------
% 0.22/0.57  % (28089)------------------------------
% 0.22/0.57  % (28094)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (28096)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.58  % (28096)Refutation not found, incomplete strategy% (28096)------------------------------
% 0.22/0.58  % (28096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (28096)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (28096)Memory used [KB]: 1663
% 0.22/0.58  % (28096)Time elapsed: 0.144 s
% 0.22/0.58  % (28096)------------------------------
% 0.22/0.58  % (28096)------------------------------
% 0.22/0.58  % (28090)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.58  % (28097)Refutation not found, incomplete strategy% (28097)------------------------------
% 0.22/0.58  % (28097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (28097)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (28097)Memory used [KB]: 1663
% 0.22/0.58  % (28097)Time elapsed: 0.145 s
% 0.22/0.58  % (28097)------------------------------
% 0.22/0.58  % (28097)------------------------------
% 0.22/0.58  % (28083)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (28098)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (28091)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.59  % (28107)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.59  % (28103)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.59  % (28084)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.59  % (28091)Refutation not found, incomplete strategy% (28091)------------------------------
% 0.22/0.59  % (28091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (28103)Refutation not found, incomplete strategy% (28103)------------------------------
% 0.22/0.59  % (28103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (28103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (28103)Memory used [KB]: 10618
% 0.22/0.59  % (28103)Time elapsed: 0.167 s
% 0.22/0.59  % (28103)------------------------------
% 0.22/0.59  % (28103)------------------------------
% 0.22/0.59  % (28099)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.59  % (28091)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (28091)Memory used [KB]: 10618
% 0.22/0.59  % (28091)Time elapsed: 0.161 s
% 0.22/0.59  % (28091)------------------------------
% 0.22/0.59  % (28091)------------------------------
% 0.22/0.59  % (28080)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.59  % (28080)Refutation not found, incomplete strategy% (28080)------------------------------
% 0.22/0.59  % (28080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (28080)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (28080)Memory used [KB]: 1663
% 0.22/0.59  % (28080)Time elapsed: 0.159 s
% 0.22/0.59  % (28080)------------------------------
% 0.22/0.59  % (28080)------------------------------
% 0.22/0.59  % (28100)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.59  % (28095)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.59  % (28092)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.59  % (28095)Refutation not found, incomplete strategy% (28095)------------------------------
% 0.22/0.59  % (28095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (28095)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (28095)Memory used [KB]: 10618
% 0.22/0.59  % (28095)Time elapsed: 0.163 s
% 0.22/0.59  % (28095)------------------------------
% 0.22/0.59  % (28095)------------------------------
% 1.81/0.60  % (28081)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.81/0.60  % (28085)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.81/0.60  % (28107)Refutation not found, incomplete strategy% (28107)------------------------------
% 1.81/0.60  % (28107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (28107)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (28107)Memory used [KB]: 10746
% 1.81/0.60  % (28107)Time elapsed: 0.174 s
% 1.81/0.60  % (28107)------------------------------
% 1.81/0.60  % (28107)------------------------------
% 1.81/0.60  % (28108)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.81/0.60  % (28108)Refutation not found, incomplete strategy% (28108)------------------------------
% 1.81/0.60  % (28108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (28106)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.81/0.60  % (28087)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.81/0.60  % (28082)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.81/0.60  % (28106)Refutation not found, incomplete strategy% (28106)------------------------------
% 1.81/0.60  % (28106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (28106)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (28106)Memory used [KB]: 6140
% 1.81/0.60  % (28106)Time elapsed: 0.173 s
% 1.81/0.60  % (28106)------------------------------
% 1.81/0.60  % (28106)------------------------------
% 1.81/0.61  % (28101)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.81/0.61  % (28093)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.81/0.61  % (28098)Refutation found. Thanks to Tanya!
% 1.81/0.61  % SZS status Theorem for theBenchmark
% 1.95/0.61  % (28093)Refutation not found, incomplete strategy% (28093)------------------------------
% 1.95/0.61  % (28093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.61  % (28093)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.61  
% 1.95/0.61  % (28093)Memory used [KB]: 1663
% 1.95/0.61  % (28093)Time elapsed: 0.183 s
% 1.95/0.61  % (28093)------------------------------
% 1.95/0.61  % (28093)------------------------------
% 1.95/0.61  % (28108)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.61  
% 1.95/0.61  % (28108)Memory used [KB]: 1663
% 1.95/0.61  % (28108)Time elapsed: 0.143 s
% 1.95/0.61  % (28108)------------------------------
% 1.95/0.61  % (28108)------------------------------
% 1.95/0.61  % (28079)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.06/0.63  % SZS output start Proof for theBenchmark
% 2.06/0.63  fof(f432,plain,(
% 2.06/0.63    $false),
% 2.06/0.63    inference(subsumption_resolution,[],[f431,f83])).
% 2.06/0.63  fof(f83,plain,(
% 2.06/0.63    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 2.06/0.63    inference(forward_demodulation,[],[f81,f82])).
% 2.06/0.63  fof(f82,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.06/0.63    inference(backward_demodulation,[],[f76,f58])).
% 2.06/0.63  fof(f58,plain,(
% 2.06/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f8])).
% 2.06/0.63  fof(f8,axiom,(
% 2.06/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.06/0.63  fof(f76,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.06/0.63    inference(definition_unfolding,[],[f57,f41])).
% 2.06/0.63  fof(f41,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f12])).
% 2.06/0.63  fof(f12,axiom,(
% 2.06/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.06/0.63  fof(f57,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f6])).
% 2.06/0.63  fof(f6,axiom,(
% 2.06/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 2.06/0.63    inference(equality_resolution,[],[f64])).
% 2.06/0.63  fof(f64,plain,(
% 2.06/0.63    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f22])).
% 2.06/0.63  fof(f22,axiom,(
% 2.06/0.63    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.06/0.63  fof(f431,plain,(
% 2.06/0.63    k1_xboole_0 = k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.06/0.63    inference(forward_demodulation,[],[f426,f82])).
% 2.06/0.63  fof(f426,plain,(
% 2.06/0.63    k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.06/0.63    inference(backward_demodulation,[],[f164,f424])).
% 2.06/0.63  fof(f424,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 2.06/0.63    inference(forward_demodulation,[],[f423,f47])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  fof(f24,axiom,(
% 2.06/0.63    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.06/0.63  fof(f423,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k4_xboole_0(k1_setfam_1(k1_tarski(X0)),X1))) )),
% 2.06/0.63    inference(forward_demodulation,[],[f404,f47])).
% 2.06/0.63  fof(f404,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k4_xboole_0(k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k1_tarski(X1))))) )),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f83,f83,f71])).
% 2.06/0.63  fof(f71,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(definition_unfolding,[],[f45,f41])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f30])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.06/0.63    inference(ennf_transformation,[],[f23])).
% 2.06/0.63  fof(f23,axiom,(
% 2.06/0.63    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 2.06/0.63  fof(f164,plain,(
% 2.06/0.63    k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_tarski(k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f66,f63])).
% 2.06/0.63  fof(f63,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.06/0.63    inference(cnf_transformation,[],[f22])).
% 2.06/0.63  fof(f66,plain,(
% 2.06/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.06/0.63    inference(definition_unfolding,[],[f34,f41,f55])).
% 2.06/0.63  fof(f55,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f20])).
% 2.06/0.63  fof(f20,axiom,(
% 2.06/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.06/0.63    inference(cnf_transformation,[],[f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 2.06/0.63    inference(ennf_transformation,[],[f27])).
% 2.06/0.63  fof(f27,negated_conjecture,(
% 2.06/0.63    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.06/0.63    inference(negated_conjecture,[],[f26])).
% 2.06/0.63  fof(f26,conjecture,(
% 2.06/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (28098)------------------------------
% 2.06/0.63  % (28098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (28098)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (28098)Memory used [KB]: 2046
% 2.06/0.63  % (28098)Time elapsed: 0.188 s
% 2.06/0.63  % (28098)------------------------------
% 2.06/0.63  % (28098)------------------------------
% 2.06/0.63  % (28078)Success in time 0.259 s
%------------------------------------------------------------------------------
