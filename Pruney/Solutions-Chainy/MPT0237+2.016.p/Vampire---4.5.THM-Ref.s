%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:31 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  83 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f835,plain,(
    $false ),
    inference(subsumption_resolution,[],[f834,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f834,plain,(
    k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f832,f248])).

fof(f248,plain,(
    ! [X4] : k1_tarski(X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f235,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f235,plain,(
    ! [X4] : k2_xboole_0(k1_tarski(X4),k1_tarski(X4)) = k5_xboole_0(k1_tarski(X4),k1_xboole_0) ),
    inference(superposition,[],[f221,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f221,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f210,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f48,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f210,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f55,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f832,plain,(
    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f108,f831])).

fof(f831,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f826,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f826,plain,
    ( k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK1 = sK2 ),
    inference(superposition,[],[f108,f284])).

fof(f284,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) = k5_xboole_0(k1_tarski(X2),k1_tarski(X1))
      | X1 = X2 ) ),
    inference(superposition,[],[f221,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f108,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:20:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (9589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (9597)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (9588)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (9605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (9583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (9583)Refutation not found, incomplete strategy% (9583)------------------------------
% 0.22/0.53  % (9583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9583)Memory used [KB]: 1663
% 0.22/0.53  % (9583)Time elapsed: 0.111 s
% 0.22/0.53  % (9583)------------------------------
% 0.22/0.53  % (9583)------------------------------
% 0.22/0.53  % (9585)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9586)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (9584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (9604)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (9587)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (9604)Refutation not found, incomplete strategy% (9604)------------------------------
% 0.22/0.54  % (9604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9604)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9604)Memory used [KB]: 1791
% 0.22/0.54  % (9604)Time elapsed: 0.133 s
% 0.22/0.54  % (9604)------------------------------
% 0.22/0.54  % (9604)------------------------------
% 0.22/0.54  % (9610)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (9595)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (9612)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (9602)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (9591)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (9593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (9591)Refutation not found, incomplete strategy% (9591)------------------------------
% 1.41/0.55  % (9591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9591)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9591)Memory used [KB]: 10746
% 1.41/0.55  % (9591)Time elapsed: 0.136 s
% 1.41/0.55  % (9591)------------------------------
% 1.41/0.55  % (9591)------------------------------
% 1.41/0.55  % (9593)Refutation not found, incomplete strategy% (9593)------------------------------
% 1.41/0.55  % (9593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9593)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9593)Memory used [KB]: 10618
% 1.41/0.55  % (9593)Time elapsed: 0.137 s
% 1.41/0.55  % (9593)------------------------------
% 1.41/0.55  % (9593)------------------------------
% 1.41/0.55  % (9603)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (9608)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (9603)Refutation not found, incomplete strategy% (9603)------------------------------
% 1.41/0.55  % (9603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9603)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9603)Memory used [KB]: 10746
% 1.41/0.55  % (9603)Time elapsed: 0.149 s
% 1.41/0.55  % (9603)------------------------------
% 1.41/0.55  % (9603)------------------------------
% 1.41/0.55  % (9596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (9601)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (9594)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (9611)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (9594)Refutation not found, incomplete strategy% (9594)------------------------------
% 1.41/0.55  % (9594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9594)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9594)Memory used [KB]: 10618
% 1.41/0.55  % (9594)Time elapsed: 0.147 s
% 1.41/0.55  % (9594)------------------------------
% 1.41/0.55  % (9594)------------------------------
% 1.41/0.56  % (9599)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (9592)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (9600)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (9607)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.61/0.57  % (9609)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.57  % (9585)Refutation not found, incomplete strategy% (9585)------------------------------
% 1.61/0.57  % (9585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (9585)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (9585)Memory used [KB]: 10746
% 1.61/0.57  % (9585)Time elapsed: 0.152 s
% 1.61/0.57  % (9585)------------------------------
% 1.61/0.57  % (9585)------------------------------
% 1.61/0.57  % (9600)Refutation not found, incomplete strategy% (9600)------------------------------
% 1.61/0.57  % (9600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (9600)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (9600)Memory used [KB]: 10618
% 1.61/0.57  % (9600)Time elapsed: 0.157 s
% 1.61/0.57  % (9600)------------------------------
% 1.61/0.57  % (9600)------------------------------
% 1.61/0.57  % (9606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.57  % (9590)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.57  % (9598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.58  % (9606)Refutation not found, incomplete strategy% (9606)------------------------------
% 1.61/0.58  % (9606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (9598)Refutation not found, incomplete strategy% (9598)------------------------------
% 1.61/0.58  % (9598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (9606)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (9606)Memory used [KB]: 1663
% 1.61/0.58  % (9606)Time elapsed: 0.084 s
% 1.61/0.58  % (9606)------------------------------
% 1.61/0.58  % (9606)------------------------------
% 1.61/0.58  % (9598)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (9598)Memory used [KB]: 6140
% 1.61/0.58  % (9598)Time elapsed: 0.082 s
% 1.61/0.58  % (9598)------------------------------
% 1.61/0.58  % (9598)------------------------------
% 1.99/0.64  % (9590)Refutation found. Thanks to Tanya!
% 1.99/0.64  % SZS status Theorem for theBenchmark
% 1.99/0.64  % SZS output start Proof for theBenchmark
% 1.99/0.64  fof(f835,plain,(
% 1.99/0.64    $false),
% 1.99/0.64    inference(subsumption_resolution,[],[f834,f42])).
% 1.99/0.64  fof(f42,plain,(
% 1.99/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/0.64    inference(cnf_transformation,[],[f8])).
% 1.99/0.64  fof(f8,axiom,(
% 1.99/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.99/0.64  fof(f834,plain,(
% 1.99/0.64    k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 1.99/0.64    inference(forward_demodulation,[],[f832,f248])).
% 1.99/0.64  fof(f248,plain,(
% 1.99/0.64    ( ! [X4] : (k1_tarski(X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X4))) )),
% 1.99/0.64    inference(forward_demodulation,[],[f235,f41])).
% 1.99/0.64  fof(f41,plain,(
% 1.99/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.64    inference(cnf_transformation,[],[f3])).
% 1.99/0.64  fof(f3,axiom,(
% 1.99/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.99/0.64  fof(f235,plain,(
% 1.99/0.64    ( ! [X4] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X4)) = k5_xboole_0(k1_tarski(X4),k1_xboole_0)) )),
% 1.99/0.64    inference(superposition,[],[f221,f77])).
% 1.99/0.64  fof(f77,plain,(
% 1.99/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.99/0.64    inference(superposition,[],[f44,f42])).
% 1.99/0.64  fof(f44,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.99/0.64    inference(cnf_transformation,[],[f19])).
% 1.99/0.64  fof(f19,axiom,(
% 1.99/0.64    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 1.99/0.64  fof(f221,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.99/0.64    inference(forward_demodulation,[],[f210,f97])).
% 1.99/0.64  fof(f97,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.99/0.64    inference(superposition,[],[f48,f43])).
% 1.99/0.64  fof(f43,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.99/0.64    inference(cnf_transformation,[],[f1])).
% 1.99/0.64  fof(f1,axiom,(
% 1.99/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.99/0.64  fof(f48,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.99/0.64    inference(cnf_transformation,[],[f2])).
% 1.99/0.64  fof(f2,axiom,(
% 1.99/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.99/0.64  fof(f210,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.99/0.64    inference(superposition,[],[f55,f49])).
% 1.99/0.64  fof(f49,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.99/0.64    inference(cnf_transformation,[],[f6])).
% 1.99/0.64  fof(f6,axiom,(
% 1.99/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.99/0.64  fof(f55,plain,(
% 1.99/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.99/0.64    inference(cnf_transformation,[],[f5])).
% 1.99/0.64  fof(f5,axiom,(
% 1.99/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.99/0.64  fof(f832,plain,(
% 1.99/0.64    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.99/0.64    inference(backward_demodulation,[],[f108,f831])).
% 1.99/0.64  fof(f831,plain,(
% 1.99/0.64    sK1 = sK2),
% 1.99/0.64    inference(subsumption_resolution,[],[f826,f51])).
% 1.99/0.64  fof(f51,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.99/0.64    inference(cnf_transformation,[],[f26])).
% 1.99/0.64  fof(f26,plain,(
% 1.99/0.64    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.99/0.64    inference(ennf_transformation,[],[f20])).
% 1.99/0.64  fof(f20,axiom,(
% 1.99/0.64    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.99/0.64  fof(f826,plain,(
% 1.99/0.64    k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK1 = sK2),
% 1.99/0.64    inference(superposition,[],[f108,f284])).
% 1.99/0.64  fof(f284,plain,(
% 1.99/0.64    ( ! [X2,X1] : (k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) = k5_xboole_0(k1_tarski(X2),k1_tarski(X1)) | X1 = X2) )),
% 1.99/0.64    inference(superposition,[],[f221,f79])).
% 1.99/0.64  fof(f79,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.99/0.64    inference(resolution,[],[f53,f50])).
% 1.99/0.64  fof(f50,plain,(
% 1.99/0.64    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.99/0.64    inference(cnf_transformation,[],[f25])).
% 1.99/0.64  fof(f25,plain,(
% 1.99/0.64    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.99/0.64    inference(ennf_transformation,[],[f17])).
% 1.99/0.64  fof(f17,axiom,(
% 1.99/0.64    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.99/0.64  fof(f53,plain,(
% 1.99/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.99/0.64    inference(cnf_transformation,[],[f28])).
% 1.99/0.64  fof(f28,plain,(
% 1.99/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.99/0.64    inference(ennf_transformation,[],[f23])).
% 1.99/0.64  fof(f23,plain,(
% 1.99/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.99/0.64    inference(unused_predicate_definition_removal,[],[f4])).
% 1.99/0.64  fof(f4,axiom,(
% 1.99/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.99/0.64  fof(f108,plain,(
% 1.99/0.64    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.99/0.64    inference(superposition,[],[f40,f45])).
% 1.99/0.64  fof(f45,plain,(
% 1.99/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.99/0.64    inference(cnf_transformation,[],[f16])).
% 1.99/0.64  fof(f16,axiom,(
% 1.99/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.99/0.64  fof(f40,plain,(
% 1.99/0.64    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.99/0.64    inference(cnf_transformation,[],[f33])).
% 1.99/0.64  fof(f33,plain,(
% 1.99/0.64    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.99/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f32])).
% 1.99/0.64  fof(f32,plain,(
% 1.99/0.64    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.99/0.64    introduced(choice_axiom,[])).
% 1.99/0.64  fof(f24,plain,(
% 1.99/0.64    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.64    inference(ennf_transformation,[],[f22])).
% 1.99/0.64  fof(f22,negated_conjecture,(
% 1.99/0.64    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.64    inference(negated_conjecture,[],[f21])).
% 1.99/0.64  fof(f21,conjecture,(
% 1.99/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 1.99/0.64  % SZS output end Proof for theBenchmark
% 1.99/0.64  % (9590)------------------------------
% 1.99/0.64  % (9590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.64  % (9590)Termination reason: Refutation
% 1.99/0.64  
% 1.99/0.64  % (9590)Memory used [KB]: 7419
% 1.99/0.64  % (9590)Time elapsed: 0.156 s
% 1.99/0.64  % (9590)------------------------------
% 1.99/0.64  % (9590)------------------------------
% 1.99/0.65  % (9582)Success in time 0.278 s
%------------------------------------------------------------------------------
