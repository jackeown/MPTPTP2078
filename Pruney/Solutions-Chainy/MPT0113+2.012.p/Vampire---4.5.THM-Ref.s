%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 169 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f781,f1341])).

fof(f1341,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1340])).

fof(f1340,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f1309,f92])).

fof(f92,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f85,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f85,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1309,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f100,f831])).

fof(f831,plain,
    ( ! [X5] : k3_xboole_0(sK0,X5) = k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f830,f63])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f830,plain,
    ( ! [X5] : k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k3_xboole_0(sK0,k5_xboole_0(X5,k1_xboole_0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f829,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f829,plain,
    ( ! [X5] : k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f820,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f59,f67,f67])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f820,plain,
    ( ! [X5] : k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X5),k3_xboole_0(k3_xboole_0(sK0,X5),k1_xboole_0))
    | ~ spl3_1 ),
    inference(superposition,[],[f75,f783])).

fof(f783,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f80,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f58,f67,f67])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f100,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f69,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f43,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f781,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f780])).

fof(f780,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f779,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f779,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f774,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f774,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | spl3_1 ),
    inference(resolution,[],[f734,f72])).

fof(f734,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f81,f616])).

fof(f616,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f262,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f262,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
      | r1_xboole_0(sK0,X3) ) ),
    inference(forward_demodulation,[],[f253,f63])).

fof(f253,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,k5_xboole_0(X3,k1_xboole_0))
      | ~ r1_xboole_0(X3,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ) ),
    inference(superposition,[],[f101,f48])).

fof(f101,plain,(
    ! [X0] : r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f69,f71])).

fof(f81,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f83,f79])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (16998)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (17000)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (16993)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (17014)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (16999)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (16995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (16996)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (17018)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (17013)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (16994)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (17005)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (16991)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (17019)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (17017)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (16992)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (17012)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (16997)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (17009)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (17013)Refutation not found, incomplete strategy% (17013)------------------------------
% 0.22/0.55  % (17013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17013)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17013)Memory used [KB]: 10746
% 0.22/0.55  % (17013)Time elapsed: 0.091 s
% 0.22/0.55  % (17013)------------------------------
% 0.22/0.55  % (17013)------------------------------
% 0.22/0.55  % (17006)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (17011)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (17010)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (17015)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (17004)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (17001)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (17016)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (17002)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (17007)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (17003)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (17008)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (17020)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.59  % (17000)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1352,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f86,f781,f1341])).
% 0.22/0.59  fof(f1341,plain,(
% 0.22/0.59    ~spl3_1 | spl3_2),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1340])).
% 0.22/0.59  fof(f1340,plain,(
% 0.22/0.59    $false | (~spl3_1 | spl3_2)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1309,f92])).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f85,f72])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f54,f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f83])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.59  fof(f1309,plain,(
% 0.22/0.59    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.22/0.59    inference(superposition,[],[f100,f831])).
% 0.22/0.59  fof(f831,plain,(
% 0.22/0.59    ( ! [X5] : (k3_xboole_0(sK0,X5) = k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2)))) ) | ~spl3_1),
% 0.22/0.59    inference(forward_demodulation,[],[f830,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,axiom,(
% 0.22/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.59  fof(f830,plain,(
% 0.22/0.59    ( ! [X5] : (k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k3_xboole_0(sK0,k5_xboole_0(X5,k1_xboole_0))) ) | ~spl3_1),
% 0.22/0.59    inference(forward_demodulation,[],[f829,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.59  fof(f829,plain,(
% 0.22/0.59    ( ! [X5] : (k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)))) ) | ~spl3_1),
% 0.22/0.59    inference(forward_demodulation,[],[f820,f76])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f59,f67,f67])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.59  fof(f820,plain,(
% 0.22/0.59    ( ! [X5] : (k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X5),k3_xboole_0(k3_xboole_0(sK0,X5),k1_xboole_0))) ) | ~spl3_1),
% 0.22/0.59    inference(superposition,[],[f75,f783])).
% 0.22/0.59  fof(f783,plain,(
% 0.22/0.59    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f80,f48])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f58,f67,f67])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f69,f73])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f53,f67])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.59    inference(definition_unfolding,[],[f43,f67])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.59    inference(negated_conjecture,[],[f32])).
% 0.22/0.59  fof(f32,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.59  fof(f781,plain,(
% 0.22/0.59    spl3_1),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f780])).
% 0.22/0.59  fof(f780,plain,(
% 0.22/0.59    $false | spl3_1),
% 0.22/0.59    inference(subsumption_resolution,[],[f779,f64])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.59  fof(f779,plain,(
% 0.22/0.59    k1_xboole_0 != k5_xboole_0(sK2,sK2) | spl3_1),
% 0.22/0.59    inference(forward_demodulation,[],[f774,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    inference(rectify,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.59  fof(f774,plain,(
% 0.22/0.59    k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) | spl3_1),
% 0.22/0.59    inference(resolution,[],[f734,f72])).
% 0.22/0.59  fof(f734,plain,(
% 0.22/0.59    ~r1_tarski(sK2,sK2) | spl3_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f81,f616])).
% 0.22/0.59  fof(f616,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(sK0,X0)) )),
% 0.22/0.59    inference(resolution,[],[f262,f71])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f46,f67])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.59  fof(f262,plain,(
% 0.22/0.59    ( ! [X3] : (~r1_xboole_0(X3,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | r1_xboole_0(sK0,X3)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f253,f63])).
% 0.22/0.59  fof(f253,plain,(
% 0.22/0.59    ( ! [X3] : (r1_xboole_0(sK0,k5_xboole_0(X3,k1_xboole_0)) | ~r1_xboole_0(X3,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) )),
% 0.22/0.59    inference(superposition,[],[f101,f48])).
% 0.22/0.59  fof(f101,plain,(
% 0.22/0.59    ( ! [X0] : (r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f69,f71])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f79])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ~spl3_1 | ~spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f42,f83,f79])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (17000)------------------------------
% 0.22/0.59  % (17000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (17000)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (17000)Memory used [KB]: 11257
% 0.22/0.59  % (17000)Time elapsed: 0.179 s
% 0.22/0.59  % (17000)------------------------------
% 0.22/0.59  % (17000)------------------------------
% 0.22/0.60  % (16990)Success in time 0.231 s
%------------------------------------------------------------------------------
