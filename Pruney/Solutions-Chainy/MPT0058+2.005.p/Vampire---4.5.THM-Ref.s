%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:10 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 151 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 240 expanded)
%              Number of equality atoms :   27 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f851,plain,(
    $false ),
    inference(global_subsumption,[],[f55,f816])).

fof(f816,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f33,f733])).

fof(f733,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f695,f695,f721,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(sK2(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f24,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(sK2(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f721,plain,(
    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f701,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f701,plain,(
    sP5(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f695,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f695,plain,(
    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f694])).

fof(f694,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | r1_tarski(X1,X0) ) ),
    inference(factoring,[],[f224])).

fof(f224,plain,(
    ! [X14,X15,X16] :
      ( r2_hidden(sK2(X14,X15,X16),X16)
      | r1_tarski(X16,X14)
      | r2_hidden(sK2(X14,X15,X16),X15) ) ),
    inference(superposition,[],[f33,f185])).

fof(f185,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,k4_xboole_0(X3,X4)) = X5
      | r2_hidden(sK2(X3,X4,X5),X5)
      | r2_hidden(sK2(X3,X4,X5),X4) ) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f23,f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f53,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f43,f16])).

fof(f43,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f32,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f12,f15])).

fof(f12,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (11888)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (11888)Refutation not found, incomplete strategy% (11888)------------------------------
% 0.21/0.57  % (11888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (11887)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (11896)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (11904)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (11888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (11888)Memory used [KB]: 10618
% 0.21/0.57  % (11888)Time elapsed: 0.123 s
% 0.21/0.57  % (11888)------------------------------
% 0.21/0.57  % (11888)------------------------------
% 0.21/0.58  % (11886)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (11895)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (11895)Refutation not found, incomplete strategy% (11895)------------------------------
% 0.21/0.58  % (11895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (11895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (11895)Memory used [KB]: 6140
% 0.21/0.58  % (11895)Time elapsed: 0.001 s
% 0.21/0.58  % (11895)------------------------------
% 0.21/0.58  % (11895)------------------------------
% 0.21/0.58  % (11903)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (11902)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (11894)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.59  % (11885)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.59  % (11905)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.59  % (11889)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.76/0.60  % (11905)Refutation not found, incomplete strategy% (11905)------------------------------
% 1.76/0.60  % (11905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11905)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (11905)Memory used [KB]: 6268
% 1.76/0.60  % (11905)Time elapsed: 0.122 s
% 1.76/0.60  % (11905)------------------------------
% 1.76/0.60  % (11905)------------------------------
% 1.76/0.60  % (11897)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.76/0.60  % (11897)Refutation not found, incomplete strategy% (11897)------------------------------
% 1.76/0.60  % (11897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11897)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (11897)Memory used [KB]: 10618
% 1.76/0.60  % (11897)Time elapsed: 0.110 s
% 1.76/0.60  % (11897)------------------------------
% 1.76/0.60  % (11897)------------------------------
% 1.76/0.60  % (11906)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.76/0.60  % (11882)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.76/0.60  % (11881)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.76/0.60  % (11882)Refutation not found, incomplete strategy% (11882)------------------------------
% 1.76/0.60  % (11882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11889)Refutation not found, incomplete strategy% (11889)------------------------------
% 1.76/0.60  % (11889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11889)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (11889)Memory used [KB]: 10618
% 1.76/0.60  % (11889)Time elapsed: 0.122 s
% 1.76/0.60  % (11889)------------------------------
% 1.76/0.60  % (11889)------------------------------
% 1.76/0.60  % (11901)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.76/0.60  % (11898)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.76/0.60  % (11893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.76/0.61  % (11882)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.61  
% 1.76/0.61  % (11882)Memory used [KB]: 10618
% 1.76/0.61  % (11882)Time elapsed: 0.157 s
% 1.76/0.61  % (11882)------------------------------
% 1.76/0.61  % (11882)------------------------------
% 1.76/0.61  % (11901)Refutation not found, incomplete strategy% (11901)------------------------------
% 1.76/0.61  % (11901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (11909)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.89/0.61  % (11884)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.89/0.61  % (11902)Refutation not found, incomplete strategy% (11902)------------------------------
% 1.89/0.61  % (11902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (11902)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (11902)Memory used [KB]: 10746
% 1.89/0.61  % (11902)Time elapsed: 0.165 s
% 1.89/0.61  % (11902)------------------------------
% 1.89/0.61  % (11902)------------------------------
% 1.89/0.61  % (11884)Refutation not found, incomplete strategy% (11884)------------------------------
% 1.89/0.61  % (11884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (11884)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (11884)Memory used [KB]: 6140
% 1.89/0.61  % (11884)Time elapsed: 0.168 s
% 1.89/0.61  % (11884)------------------------------
% 1.89/0.61  % (11884)------------------------------
% 1.89/0.62  % (11890)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.89/0.62  % (11901)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (11901)Memory used [KB]: 1663
% 1.89/0.62  % (11901)Time elapsed: 0.172 s
% 1.89/0.62  % (11901)------------------------------
% 1.89/0.62  % (11901)------------------------------
% 1.89/0.62  % (11890)Refutation not found, incomplete strategy% (11890)------------------------------
% 1.89/0.62  % (11890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (11890)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (11890)Memory used [KB]: 10618
% 1.89/0.62  % (11890)Time elapsed: 0.178 s
% 1.89/0.62  % (11890)------------------------------
% 1.89/0.62  % (11890)------------------------------
% 1.89/0.62  % (11883)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.89/0.62  % (11900)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.04/0.63  % (11908)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.04/0.63  % (11880)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.04/0.63  % (11880)Refutation not found, incomplete strategy% (11880)------------------------------
% 2.04/0.63  % (11880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (11880)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.63  
% 2.04/0.63  % (11880)Memory used [KB]: 1663
% 2.04/0.63  % (11880)Time elapsed: 0.192 s
% 2.04/0.63  % (11880)------------------------------
% 2.04/0.63  % (11880)------------------------------
% 2.04/0.63  % (11907)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.04/0.63  % (11899)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.04/0.63  % (11892)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.04/0.63  % (11891)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.04/0.64  % (11900)Refutation not found, incomplete strategy% (11900)------------------------------
% 2.04/0.64  % (11900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (11900)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.64  
% 2.04/0.64  % (11900)Memory used [KB]: 10618
% 2.04/0.64  % (11900)Time elapsed: 0.192 s
% 2.04/0.64  % (11900)------------------------------
% 2.04/0.64  % (11900)------------------------------
% 2.04/0.67  % (11904)Refutation found. Thanks to Tanya!
% 2.04/0.67  % SZS status Theorem for theBenchmark
% 2.04/0.67  % SZS output start Proof for theBenchmark
% 2.04/0.67  fof(f851,plain,(
% 2.04/0.67    $false),
% 2.04/0.67    inference(global_subsumption,[],[f55,f816])).
% 2.04/0.67  fof(f816,plain,(
% 2.04/0.67    r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 2.04/0.67    inference(superposition,[],[f33,f733])).
% 2.04/0.67  fof(f733,plain,(
% 2.04/0.67    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f695,f695,f721,f171])).
% 2.04/0.67  fof(f171,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0)) )),
% 2.04/0.67    inference(resolution,[],[f34,f18])).
% 2.04/0.67  fof(f18,plain,(
% 2.04/0.67    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f2])).
% 2.04/0.67  fof(f2,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.04/0.67  fof(f34,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~sP3(sK2(X0,X1,X2),X1,X0) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.04/0.67    inference(definition_unfolding,[],[f24,f15])).
% 2.04/0.67  fof(f15,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f7])).
% 2.04/0.67  fof(f7,axiom,(
% 2.04/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.04/0.67  fof(f24,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~sP3(sK2(X0,X1,X2),X1,X0) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.04/0.67    inference(cnf_transformation,[],[f2])).
% 2.04/0.67  fof(f721,plain,(
% 2.04/0.67    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f701,f26])).
% 2.04/0.67  fof(f26,plain,(
% 2.04/0.67    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f3])).
% 2.04/0.67  fof(f3,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.04/0.67  fof(f701,plain,(
% 2.04/0.67    sP5(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1,sK0)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f695,f40])).
% 2.04/0.67  fof(f40,plain,(
% 2.04/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 2.04/0.67    inference(equality_resolution,[],[f29])).
% 2.04/0.67  fof(f29,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.04/0.67    inference(cnf_transformation,[],[f3])).
% 2.04/0.67  fof(f695,plain,(
% 2.04/0.67    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f55,f694])).
% 2.04/0.67  fof(f694,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | r1_tarski(X1,X0)) )),
% 2.04/0.67    inference(factoring,[],[f224])).
% 2.04/0.67  fof(f224,plain,(
% 2.04/0.67    ( ! [X14,X15,X16] : (r2_hidden(sK2(X14,X15,X16),X16) | r1_tarski(X16,X14) | r2_hidden(sK2(X14,X15,X16),X15)) )),
% 2.04/0.67    inference(superposition,[],[f33,f185])).
% 2.04/0.67  fof(f185,plain,(
% 2.04/0.67    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = X5 | r2_hidden(sK2(X3,X4,X5),X5) | r2_hidden(sK2(X3,X4,X5),X4)) )),
% 2.04/0.67    inference(resolution,[],[f35,f20])).
% 2.04/0.67  fof(f20,plain,(
% 2.04/0.67    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f2])).
% 2.04/0.67  fof(f35,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.04/0.67    inference(definition_unfolding,[],[f23,f15])).
% 2.04/0.67  fof(f23,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.04/0.67    inference(cnf_transformation,[],[f2])).
% 2.04/0.67  fof(f33,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.04/0.67    inference(definition_unfolding,[],[f13,f15])).
% 2.04/0.67  fof(f13,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f4])).
% 2.04/0.67  fof(f4,axiom,(
% 2.04/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.04/0.67  fof(f55,plain,(
% 2.04/0.67    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f53,f42])).
% 2.04/0.67  fof(f42,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.67    inference(forward_demodulation,[],[f17,f16])).
% 2.04/0.67  fof(f16,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f5])).
% 2.04/0.67  fof(f5,axiom,(
% 2.04/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.04/0.67  fof(f17,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 2.04/0.67    inference(cnf_transformation,[],[f11])).
% 2.04/0.67  fof(f11,plain,(
% 2.04/0.67    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.04/0.67    inference(ennf_transformation,[],[f6])).
% 2.04/0.67  fof(f6,axiom,(
% 2.04/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 2.04/0.67  fof(f53,plain,(
% 2.04/0.67    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 2.04/0.67    inference(superposition,[],[f43,f16])).
% 2.04/0.67  fof(f43,plain,(
% 2.04/0.67    sK0 != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.04/0.67    inference(superposition,[],[f32,f14])).
% 2.04/0.67  fof(f14,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f1])).
% 2.04/0.67  fof(f1,axiom,(
% 2.04/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.04/0.67  fof(f32,plain,(
% 2.04/0.67    sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.04/0.67    inference(definition_unfolding,[],[f12,f15])).
% 2.04/0.67  fof(f12,plain,(
% 2.04/0.67    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 2.04/0.67    inference(cnf_transformation,[],[f10])).
% 2.04/0.67  fof(f10,plain,(
% 2.04/0.67    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0),
% 2.04/0.67    inference(ennf_transformation,[],[f9])).
% 2.04/0.67  fof(f9,negated_conjecture,(
% 2.04/0.67    ~! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.04/0.67    inference(negated_conjecture,[],[f8])).
% 2.04/0.67  fof(f8,conjecture,(
% 2.04/0.67    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.04/0.67  % SZS output end Proof for theBenchmark
% 2.04/0.67  % (11904)------------------------------
% 2.04/0.67  % (11904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (11904)Termination reason: Refutation
% 2.04/0.67  
% 2.04/0.67  % (11904)Memory used [KB]: 7291
% 2.04/0.67  % (11904)Time elapsed: 0.231 s
% 2.04/0.67  % (11904)------------------------------
% 2.04/0.67  % (11904)------------------------------
% 2.04/0.67  % (11879)Success in time 0.294 s
%------------------------------------------------------------------------------
