%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  72 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :   36 (  73 expanded)
%              Number of equality atoms :   35 (  72 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(subsumption_resolution,[],[f305,f139])).

% (11191)Refutation not found, incomplete strategy% (11191)------------------------------
% (11191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11191)Termination reason: Refutation not found, incomplete strategy

% (11191)Memory used [KB]: 10618
% (11191)Time elapsed: 0.131 s
% (11191)------------------------------
% (11191)------------------------------
fof(f139,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f106,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_tarski(X3,X4) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f305,plain,(
    k2_tarski(sK1,sK2) != k2_tarski(sK2,sK1) ),
    inference(superposition,[],[f37,f301])).

fof(f301,plain,(
    ! [X6,X7] : k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7) ),
    inference(forward_demodulation,[],[f297,f154])).

fof(f154,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(forward_demodulation,[],[f147,f47])).

fof(f147,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f51,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f297,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X6,X6) ),
    inference(superposition,[],[f293,f273])).

fof(f273,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f261,f51])).

fof(f261,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f61,f40])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f293,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X1,X0) = k2_enumset1(X0,X1,X1,X2) ),
    inference(forward_demodulation,[],[f285,f150])).

fof(f150,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f51,f44])).

fof(f285,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X2)) ),
    inference(superposition,[],[f62,f281])).

fof(f281,plain,(
    ! [X4,X5] : k2_tarski(X5,X4) = k1_enumset1(X4,X5,X5) ),
    inference(forward_demodulation,[],[f278,f154])).

fof(f278,plain,(
    ! [X4,X5] : k1_enumset1(X4,X5,X5) = k1_enumset1(X5,X4,X4) ),
    inference(superposition,[],[f274,f273])).

fof(f274,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0) ),
    inference(forward_demodulation,[],[f264,f150])).

fof(f264,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k2_enumset1(X1,X2,X0,X0) ),
    inference(superposition,[],[f61,f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f37,plain,(
    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11181)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.46  % (11181)Refutation not found, incomplete strategy% (11181)------------------------------
% 0.21/0.46  % (11181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11181)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (11181)Memory used [KB]: 10746
% 0.21/0.46  % (11181)Time elapsed: 0.073 s
% 0.21/0.46  % (11181)------------------------------
% 0.21/0.46  % (11181)------------------------------
% 0.21/0.48  % (11202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.48  % (11193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.48  % (11176)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (11185)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11184)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (11182)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (11184)Refutation not found, incomplete strategy% (11184)------------------------------
% 0.21/0.51  % (11184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11182)Refutation not found, incomplete strategy% (11182)------------------------------
% 0.21/0.51  % (11182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11182)Memory used [KB]: 10618
% 0.21/0.51  % (11182)Time elapsed: 0.106 s
% 0.21/0.51  % (11182)------------------------------
% 0.21/0.51  % (11182)------------------------------
% 0.21/0.51  % (11184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11184)Memory used [KB]: 10618
% 0.21/0.51  % (11184)Time elapsed: 0.114 s
% 0.21/0.51  % (11184)------------------------------
% 0.21/0.51  % (11184)------------------------------
% 0.21/0.51  % (11201)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (11177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11177)Refutation not found, incomplete strategy% (11177)------------------------------
% 0.21/0.51  % (11177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11177)Memory used [KB]: 6140
% 0.21/0.51  % (11177)Time elapsed: 0.109 s
% 0.21/0.51  % (11177)------------------------------
% 0.21/0.51  % (11177)------------------------------
% 0.21/0.51  % (11201)Refutation not found, incomplete strategy% (11201)------------------------------
% 0.21/0.51  % (11201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11201)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11201)Memory used [KB]: 10746
% 0.21/0.51  % (11201)Time elapsed: 0.109 s
% 0.21/0.51  % (11201)------------------------------
% 0.21/0.51  % (11201)------------------------------
% 0.21/0.51  % (11180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11175)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11175)Refutation not found, incomplete strategy% (11175)------------------------------
% 0.21/0.52  % (11175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11175)Memory used [KB]: 10746
% 0.21/0.52  % (11175)Time elapsed: 0.107 s
% 0.21/0.52  % (11175)------------------------------
% 0.21/0.52  % (11175)------------------------------
% 0.21/0.52  % (11204)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (11198)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (11198)Refutation not found, incomplete strategy% (11198)------------------------------
% 0.21/0.52  % (11198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11198)Memory used [KB]: 1663
% 0.21/0.52  % (11198)Time elapsed: 0.078 s
% 0.21/0.52  % (11198)------------------------------
% 0.21/0.52  % (11198)------------------------------
% 0.21/0.52  % (11194)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (11199)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (11188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (11174)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (11203)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (11179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (11195)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (11173)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (11173)Refutation not found, incomplete strategy% (11173)------------------------------
% 0.21/0.53  % (11173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11173)Memory used [KB]: 1663
% 0.21/0.53  % (11173)Time elapsed: 0.128 s
% 0.21/0.53  % (11173)------------------------------
% 0.21/0.53  % (11173)------------------------------
% 0.21/0.53  % (11187)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11200)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (11197)Refutation not found, incomplete strategy% (11197)------------------------------
% 0.21/0.53  % (11197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11191)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (11180)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f305,f139])).
% 0.21/0.53  % (11191)Refutation not found, incomplete strategy% (11191)------------------------------
% 0.21/0.53  % (11191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11191)Memory used [KB]: 10618
% 0.21/0.53  % (11191)Time elapsed: 0.131 s
% 0.21/0.53  % (11191)------------------------------
% 0.21/0.53  % (11191)------------------------------
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 0.21/0.53    inference(superposition,[],[f106,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_tarski(X3,X4)) )),
% 0.21/0.53    inference(superposition,[],[f47,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    k2_tarski(sK1,sK2) != k2_tarski(sK2,sK1)),
% 0.21/0.53    inference(superposition,[],[f37,f301])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f297,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f147,f47])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f51,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X6,X6)) )),
% 0.21/0.53    inference(superposition,[],[f293,f273])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f261,f51])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(superposition,[],[f61,f40])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X2,X1,X0) = k2_enumset1(X0,X1,X1,X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f285,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 0.21/0.53    inference(superposition,[],[f51,f44])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X2))) )),
% 0.21/0.53    inference(superposition,[],[f62,f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k2_tarski(X5,X4) = k1_enumset1(X4,X5,X5)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f278,f154])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k1_enumset1(X4,X5,X5) = k1_enumset1(X5,X4,X4)) )),
% 0.21/0.53    inference(superposition,[],[f274,f273])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f264,f150])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k2_enumset1(X1,X2,X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f61,f40])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    inference(negated_conjecture,[],[f18])).
% 0.21/0.53  fof(f18,conjecture,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11180)------------------------------
% 0.21/0.53  % (11180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11180)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11180)Memory used [KB]: 6396
% 0.21/0.53  % (11180)Time elapsed: 0.114 s
% 0.21/0.53  % (11180)------------------------------
% 0.21/0.53  % (11180)------------------------------
% 0.21/0.54  % (11171)Success in time 0.176 s
%------------------------------------------------------------------------------
