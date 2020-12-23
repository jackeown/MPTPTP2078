%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:51 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   32 (  42 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1938,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1936,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1936,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1920,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1920,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f1919,f701])).

fof(f701,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1919,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1918,f27])).

fof(f1918,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f1859,f33])).

fof(f1859,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f39,f415])).

fof(f415,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k2_xboole_0(X3,X2),X4) = k2_xboole_0(X2,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f36,f27])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f39,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f34,f31])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (27269)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (27288)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (27288)Refutation not found, incomplete strategy% (27288)------------------------------
% 0.21/0.55  % (27288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27288)Memory used [KB]: 1663
% 0.21/0.55  % (27288)Time elapsed: 0.125 s
% 0.21/0.55  % (27288)------------------------------
% 0.21/0.55  % (27288)------------------------------
% 0.21/0.56  % (27271)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (27268)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (27268)Refutation not found, incomplete strategy% (27268)------------------------------
% 0.21/0.57  % (27268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27268)Memory used [KB]: 10618
% 0.21/0.57  % (27268)Time elapsed: 0.140 s
% 0.21/0.57  % (27268)------------------------------
% 0.21/0.57  % (27268)------------------------------
% 0.21/0.57  % (27274)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (27274)Refutation not found, incomplete strategy% (27274)------------------------------
% 0.21/0.57  % (27274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27274)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27274)Memory used [KB]: 10618
% 0.21/0.57  % (27274)Time elapsed: 0.141 s
% 0.21/0.57  % (27274)------------------------------
% 0.21/0.57  % (27274)------------------------------
% 0.21/0.57  % (27266)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (27272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (27284)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (27266)Refutation not found, incomplete strategy% (27266)------------------------------
% 0.21/0.57  % (27266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27266)Memory used [KB]: 1663
% 0.21/0.57  % (27266)Time elapsed: 0.116 s
% 0.21/0.57  % (27266)------------------------------
% 0.21/0.57  % (27266)------------------------------
% 0.21/0.57  % (27278)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (27282)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (27270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.58  % (27281)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (27270)Refutation not found, incomplete strategy% (27270)------------------------------
% 0.21/0.58  % (27270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (27270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (27270)Memory used [KB]: 6140
% 0.21/0.58  % (27270)Time elapsed: 0.159 s
% 0.21/0.58  % (27270)------------------------------
% 0.21/0.58  % (27270)------------------------------
% 0.21/0.58  % (27277)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (27281)Refutation not found, incomplete strategy% (27281)------------------------------
% 0.21/0.58  % (27281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (27281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (27281)Memory used [KB]: 6140
% 0.21/0.58  % (27281)Time elapsed: 0.122 s
% 0.21/0.58  % (27281)------------------------------
% 0.21/0.58  % (27281)------------------------------
% 0.21/0.59  % (27293)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.59  % (27273)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.59  % (27290)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (27290)Refutation not found, incomplete strategy% (27290)------------------------------
% 0.21/0.60  % (27290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (27290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (27290)Memory used [KB]: 1663
% 0.21/0.60  % (27290)Time elapsed: 0.132 s
% 0.21/0.60  % (27290)------------------------------
% 0.21/0.60  % (27290)------------------------------
% 0.21/0.60  % (27267)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.61  % (27280)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.61  % (27293)Refutation not found, incomplete strategy% (27293)------------------------------
% 0.21/0.61  % (27293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (27289)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.62  % (27289)Refutation not found, incomplete strategy% (27289)------------------------------
% 0.21/0.62  % (27289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (27293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (27293)Memory used [KB]: 10618
% 0.21/0.62  % (27293)Time elapsed: 0.181 s
% 0.21/0.62  % (27293)------------------------------
% 0.21/0.62  % (27293)------------------------------
% 0.21/0.62  % (27285)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.62  % (27289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (27289)Memory used [KB]: 10746
% 0.21/0.62  % (27289)Time elapsed: 0.191 s
% 0.21/0.62  % (27289)------------------------------
% 0.21/0.62  % (27289)------------------------------
% 2.01/0.64  % (27275)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.01/0.64  % (27269)Refutation found. Thanks to Tanya!
% 2.01/0.64  % SZS status Theorem for theBenchmark
% 2.01/0.64  % (27291)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.18/0.64  % SZS output start Proof for theBenchmark
% 2.18/0.64  fof(f1938,plain,(
% 2.18/0.64    $false),
% 2.18/0.64    inference(subsumption_resolution,[],[f1936,f33])).
% 2.18/0.64  fof(f33,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f7])).
% 2.18/0.64  fof(f7,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.18/0.64  fof(f1936,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.18/0.64    inference(superposition,[],[f1920,f27])).
% 2.18/0.64  fof(f27,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f1])).
% 2.18/0.64  fof(f1,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.18/0.64  fof(f1920,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 2.18/0.64    inference(forward_demodulation,[],[f1919,f701])).
% 2.18/0.64  fof(f701,plain,(
% 2.18/0.64    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 2.18/0.64    inference(superposition,[],[f42,f44])).
% 2.18/0.64  fof(f44,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f32,f31])).
% 2.18/0.64  fof(f31,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f11])).
% 2.18/0.64  fof(f11,axiom,(
% 2.18/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.18/0.64  fof(f32,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f10])).
% 2.18/0.64  fof(f10,axiom,(
% 2.18/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.18/0.64  fof(f42,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.18/0.64    inference(definition_unfolding,[],[f29,f31])).
% 2.18/0.64  fof(f29,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.18/0.64    inference(cnf_transformation,[],[f5])).
% 2.18/0.64  fof(f5,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.18/0.64  fof(f1919,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.18/0.64    inference(forward_demodulation,[],[f1918,f27])).
% 2.18/0.64  fof(f1918,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 2.18/0.64    inference(forward_demodulation,[],[f1859,f33])).
% 2.18/0.64  fof(f1859,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.18/0.64    inference(superposition,[],[f39,f415])).
% 2.18/0.64  fof(f415,plain,(
% 2.18/0.64    ( ! [X4,X2,X3] : (k2_xboole_0(k2_xboole_0(X3,X2),X4) = k2_xboole_0(X2,k2_xboole_0(X3,X4))) )),
% 2.18/0.64    inference(superposition,[],[f36,f27])).
% 2.18/0.64  fof(f36,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f12])).
% 2.18/0.64  fof(f12,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.18/0.64  fof(f39,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.18/0.64    inference(definition_unfolding,[],[f23,f34,f31])).
% 2.18/0.64  fof(f34,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f2])).
% 2.18/0.64  fof(f2,axiom,(
% 2.18/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.18/0.64  fof(f23,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    inference(cnf_transformation,[],[f22])).
% 2.18/0.64  fof(f22,plain,(
% 2.18/0.64    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).
% 2.18/0.64  fof(f21,plain,(
% 2.18/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    introduced(choice_axiom,[])).
% 2.18/0.64  fof(f18,plain,(
% 2.18/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    inference(ennf_transformation,[],[f17])).
% 2.18/0.64  fof(f17,negated_conjecture,(
% 2.18/0.64    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    inference(negated_conjecture,[],[f16])).
% 2.18/0.64  fof(f16,conjecture,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.18/0.65  % SZS output end Proof for theBenchmark
% 2.18/0.65  % (27269)------------------------------
% 2.18/0.65  % (27269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (27269)Termination reason: Refutation
% 2.18/0.65  
% 2.18/0.65  % (27269)Memory used [KB]: 11897
% 2.18/0.65  % (27269)Time elapsed: 0.204 s
% 2.18/0.65  % (27269)------------------------------
% 2.18/0.65  % (27269)------------------------------
% 2.20/0.65  % (27279)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.20/0.65  % (27265)Success in time 0.277 s
%------------------------------------------------------------------------------
