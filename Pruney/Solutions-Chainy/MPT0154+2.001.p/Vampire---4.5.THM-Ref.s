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
% DateTime   : Thu Dec  3 12:33:31 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  55 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   38 (  60 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f153])).

fof(f153,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f149,f67])).

fof(f67,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f40,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f40,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_tarski(X3,X4) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f149,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK1,sK0)
    | spl2_1 ),
    inference(superposition,[],[f36,f116])).

fof(f116,plain,(
    ! [X6,X7] : k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7) ),
    inference(forward_demodulation,[],[f113,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(forward_demodulation,[],[f45,f25])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f113,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X6,X6) ),
    inference(superposition,[],[f56,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f57,f31])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_enumset1(X0,X1,X1,X2) ),
    inference(forward_demodulation,[],[f51,f46])).

fof(f46,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f31,f26])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_enumset1(X0,X1,X1,X2) ),
    inference(superposition,[],[f30,f50])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f36,plain,
    ( k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f37,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (11461)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.48  % (11444)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (11461)Refutation not found, incomplete strategy% (11461)------------------------------
% 0.20/0.49  % (11461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (11461)Memory used [KB]: 10746
% 0.20/0.49  % (11461)Time elapsed: 0.008 s
% 0.20/0.49  % (11461)------------------------------
% 0.20/0.49  % (11461)------------------------------
% 0.20/0.50  % (11443)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (11466)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (11441)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (11442)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11440)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11442)Refutation not found, incomplete strategy% (11442)------------------------------
% 0.20/0.51  % (11442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11442)Memory used [KB]: 6140
% 0.20/0.51  % (11442)Time elapsed: 0.097 s
% 0.20/0.51  % (11442)------------------------------
% 0.20/0.51  % (11442)------------------------------
% 0.20/0.51  % (11439)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (11458)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (11456)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (11465)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (11464)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (11449)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (11448)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (11448)Refutation not found, incomplete strategy% (11448)------------------------------
% 0.20/0.53  % (11448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11448)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11448)Memory used [KB]: 10618
% 0.20/0.53  % (11448)Time elapsed: 0.123 s
% 0.20/0.53  % (11448)------------------------------
% 0.20/0.53  % (11448)------------------------------
% 0.20/0.53  % (11457)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (11440)Refutation not found, incomplete strategy% (11440)------------------------------
% 0.20/0.53  % (11440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11440)Memory used [KB]: 10746
% 0.20/0.53  % (11440)Time elapsed: 0.127 s
% 0.20/0.53  % (11440)------------------------------
% 0.20/0.53  % (11440)------------------------------
% 0.20/0.53  % (11463)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (11449)Refutation not found, incomplete strategy% (11449)------------------------------
% 0.20/0.53  % (11449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11467)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (11449)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11449)Memory used [KB]: 10618
% 0.20/0.53  % (11449)Time elapsed: 0.134 s
% 0.20/0.53  % (11449)------------------------------
% 0.20/0.53  % (11449)------------------------------
% 0.20/0.54  % (11456)Refutation not found, incomplete strategy% (11456)------------------------------
% 0.20/0.54  % (11456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11456)Memory used [KB]: 10618
% 0.20/0.54  % (11456)Time elapsed: 0.133 s
% 0.20/0.54  % (11456)------------------------------
% 0.20/0.54  % (11456)------------------------------
% 1.40/0.54  % (11450)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (11464)Refutation not found, incomplete strategy% (11464)------------------------------
% 1.40/0.54  % (11464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (11464)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (11464)Memory used [KB]: 6268
% 1.40/0.54  % (11464)Time elapsed: 0.132 s
% 1.40/0.54  % (11464)------------------------------
% 1.40/0.54  % (11464)------------------------------
% 1.40/0.54  % (11445)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.54  % (11459)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (11455)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.54  % (11459)Refutation not found, incomplete strategy% (11459)------------------------------
% 1.40/0.54  % (11459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (11459)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (11459)Memory used [KB]: 10746
% 1.40/0.54  % (11459)Time elapsed: 0.140 s
% 1.40/0.54  % (11459)------------------------------
% 1.40/0.54  % (11459)------------------------------
% 1.40/0.54  % (11438)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.54  % (11438)Refutation not found, incomplete strategy% (11438)------------------------------
% 1.40/0.54  % (11438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (11438)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (11438)Memory used [KB]: 1663
% 1.40/0.54  % (11438)Time elapsed: 0.135 s
% 1.40/0.54  % (11438)------------------------------
% 1.40/0.54  % (11438)------------------------------
% 1.40/0.54  % (11447)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (11447)Refutation not found, incomplete strategy% (11447)------------------------------
% 1.40/0.55  % (11447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11447)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (11447)Memory used [KB]: 10618
% 1.40/0.55  % (11447)Time elapsed: 0.141 s
% 1.40/0.55  % (11447)------------------------------
% 1.40/0.55  % (11447)------------------------------
% 1.40/0.55  % (11446)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (11446)Refutation not found, incomplete strategy% (11446)------------------------------
% 1.40/0.55  % (11446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11468)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (11460)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.56  % (11453)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.56  % (11446)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (11446)Memory used [KB]: 10746
% 1.58/0.56  % (11446)Time elapsed: 0.142 s
% 1.58/0.56  % (11446)------------------------------
% 1.58/0.56  % (11446)------------------------------
% 1.58/0.56  % (11454)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.56  % (11452)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.56  % (11460)Refutation not found, incomplete strategy% (11460)------------------------------
% 1.58/0.56  % (11460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (11462)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.57  % (11462)Refutation not found, incomplete strategy% (11462)------------------------------
% 1.58/0.57  % (11462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (11462)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (11462)Memory used [KB]: 1663
% 1.58/0.57  % (11462)Time elapsed: 0.164 s
% 1.58/0.57  % (11462)------------------------------
% 1.58/0.57  % (11462)------------------------------
% 1.58/0.58  % (11465)Refutation not found, incomplete strategy% (11465)------------------------------
% 1.58/0.58  % (11465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (11465)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (11465)Memory used [KB]: 11001
% 1.58/0.58  % (11465)Time elapsed: 0.172 s
% 1.58/0.58  % (11465)------------------------------
% 1.58/0.58  % (11465)------------------------------
% 1.58/0.58  % (11460)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (11460)Memory used [KB]: 1791
% 1.58/0.58  % (11460)Time elapsed: 0.161 s
% 1.58/0.58  % (11460)------------------------------
% 1.58/0.58  % (11460)------------------------------
% 1.58/0.59  % (11489)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.58/0.59  % (11489)Refutation not found, incomplete strategy% (11489)------------------------------
% 1.58/0.59  % (11489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (11489)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (11489)Memory used [KB]: 6140
% 1.58/0.59  % (11489)Time elapsed: 0.060 s
% 1.58/0.59  % (11489)------------------------------
% 1.58/0.59  % (11489)------------------------------
% 1.93/0.64  % (11494)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.93/0.64  % (11495)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 1.93/0.65  % (11490)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.93/0.66  % (11491)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.13/0.67  % (11492)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.13/0.67  % (11439)Refutation found. Thanks to Tanya!
% 2.13/0.67  % SZS status Theorem for theBenchmark
% 2.13/0.67  % SZS output start Proof for theBenchmark
% 2.13/0.67  fof(f156,plain,(
% 2.13/0.67    $false),
% 2.13/0.67    inference(avatar_sat_refutation,[],[f37,f153])).
% 2.13/0.67  fof(f153,plain,(
% 2.13/0.67    spl2_1),
% 2.13/0.67    inference(avatar_contradiction_clause,[],[f152])).
% 2.13/0.67  fof(f152,plain,(
% 2.13/0.67    $false | spl2_1),
% 2.13/0.67    inference(subsumption_resolution,[],[f149,f67])).
% 2.13/0.67  fof(f67,plain,(
% 2.13/0.67    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 2.13/0.67    inference(superposition,[],[f40,f25])).
% 2.13/0.67  fof(f25,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f15])).
% 2.13/0.67  fof(f15,axiom,(
% 2.13/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 2.13/0.67  fof(f40,plain,(
% 2.13/0.67    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_tarski(X3,X4)) )),
% 2.13/0.67    inference(superposition,[],[f25,f26])).
% 2.13/0.67  fof(f26,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f1])).
% 2.13/0.67  fof(f1,axiom,(
% 2.13/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.13/0.67  fof(f149,plain,(
% 2.13/0.67    k2_tarski(sK0,sK1) != k2_tarski(sK1,sK0) | spl2_1),
% 2.13/0.67    inference(superposition,[],[f36,f116])).
% 2.13/0.67  fof(f116,plain,(
% 2.13/0.67    ( ! [X6,X7] : (k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f113,f50])).
% 2.13/0.67  fof(f50,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f45,f25])).
% 2.13/0.67  fof(f45,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0)) )),
% 2.13/0.67    inference(superposition,[],[f31,f29])).
% 2.13/0.67  fof(f29,plain,(
% 2.13/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f18])).
% 2.13/0.67  fof(f18,axiom,(
% 2.13/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.13/0.67  fof(f31,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f16])).
% 2.13/0.67  fof(f16,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 2.13/0.67  fof(f113,plain,(
% 2.13/0.67    ( ! [X6,X7] : (k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X6,X6)) )),
% 2.13/0.67    inference(superposition,[],[f56,f65])).
% 2.13/0.67  fof(f65,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f57,f31])).
% 2.13/0.67  fof(f57,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.13/0.67    inference(superposition,[],[f32,f29])).
% 2.13/0.67  fof(f32,plain,(
% 2.13/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f14])).
% 2.13/0.67  fof(f14,axiom,(
% 2.13/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 2.13/0.67  fof(f56,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_enumset1(X0,X1,X1,X2)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f51,f46])).
% 2.13/0.67  fof(f46,plain,(
% 2.13/0.67    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 2.13/0.67    inference(superposition,[],[f31,f26])).
% 2.13/0.67  fof(f51,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_enumset1(X0,X1,X1,X2)) )),
% 2.13/0.67    inference(superposition,[],[f30,f50])).
% 2.13/0.67  fof(f30,plain,(
% 2.13/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f17])).
% 2.13/0.67  fof(f17,axiom,(
% 2.13/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 2.13/0.67  fof(f36,plain,(
% 2.13/0.67    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) | spl2_1),
% 2.13/0.67    inference(avatar_component_clause,[],[f34])).
% 2.13/0.67  fof(f34,plain,(
% 2.13/0.67    spl2_1 <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 2.13/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.13/0.67  fof(f37,plain,(
% 2.13/0.67    ~spl2_1),
% 2.13/0.67    inference(avatar_split_clause,[],[f23,f34])).
% 2.13/0.67  fof(f23,plain,(
% 2.13/0.67    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.13/0.67    inference(cnf_transformation,[],[f22])).
% 2.13/0.67  fof(f22,plain,(
% 2.13/0.67    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 2.13/0.67    inference(ennf_transformation,[],[f20])).
% 2.13/0.67  fof(f20,negated_conjecture,(
% 2.13/0.67    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.13/0.67    inference(negated_conjecture,[],[f19])).
% 2.13/0.67  fof(f19,conjecture,(
% 2.13/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.13/0.67  % SZS output end Proof for theBenchmark
% 2.13/0.67  % (11439)------------------------------
% 2.13/0.67  % (11439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (11439)Termination reason: Refutation
% 2.13/0.67  
% 2.13/0.67  % (11439)Memory used [KB]: 6268
% 2.13/0.67  % (11439)Time elapsed: 0.261 s
% 2.13/0.67  % (11439)------------------------------
% 2.13/0.67  % (11439)------------------------------
% 2.13/0.68  % (11434)Success in time 0.308 s
%------------------------------------------------------------------------------
