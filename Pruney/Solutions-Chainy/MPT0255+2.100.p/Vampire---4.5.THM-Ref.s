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
% DateTime   : Thu Dec  3 12:39:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  76 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   43 (  93 expanded)
%              Number of equality atoms :   36 (  74 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f154,f84])).

fof(f84,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f67,f82])).

fof(f82,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f80,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f80,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f52,f71])).

fof(f71,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f69,f41])).

fof(f69,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f68,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f67,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f154,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f141,f71])).

fof(f141,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(sK0,X2)) ),
    inference(forward_demodulation,[],[f136,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f136,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_tarski(sK0,X2)) ),
    inference(superposition,[],[f53,f87])).

fof(f87,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK0,X6)) ),
    inference(superposition,[],[f52,f82])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (10151)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (10157)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.49  % (10175)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.50  % (10151)Refutation not found, incomplete strategy% (10151)------------------------------
% 0.19/0.50  % (10151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10159)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (10151)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10151)Memory used [KB]: 10746
% 0.19/0.50  % (10151)Time elapsed: 0.094 s
% 0.19/0.50  % (10151)------------------------------
% 0.19/0.50  % (10151)------------------------------
% 0.19/0.50  % (10173)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.50  % (10175)Refutation not found, incomplete strategy% (10175)------------------------------
% 0.19/0.50  % (10175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10175)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10175)Memory used [KB]: 10746
% 0.19/0.50  % (10175)Time elapsed: 0.109 s
% 0.19/0.50  % (10175)------------------------------
% 0.19/0.50  % (10175)------------------------------
% 0.19/0.50  % (10171)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (10159)Refutation not found, incomplete strategy% (10159)------------------------------
% 0.19/0.50  % (10159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10159)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10159)Memory used [KB]: 10618
% 0.19/0.50  % (10159)Time elapsed: 0.108 s
% 0.19/0.50  % (10159)------------------------------
% 0.19/0.50  % (10159)------------------------------
% 0.19/0.50  % (10171)Refutation not found, incomplete strategy% (10171)------------------------------
% 0.19/0.50  % (10171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10171)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (10171)Memory used [KB]: 10746
% 0.19/0.50  % (10171)Time elapsed: 0.076 s
% 0.19/0.50  % (10171)------------------------------
% 0.19/0.50  % (10171)------------------------------
% 0.19/0.50  % (10161)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (10165)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (10157)Refutation not found, incomplete strategy% (10157)------------------------------
% 0.19/0.51  % (10157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (10157)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (10157)Memory used [KB]: 10746
% 0.19/0.51  % (10157)Time elapsed: 0.101 s
% 0.19/0.51  % (10157)------------------------------
% 0.19/0.51  % (10157)------------------------------
% 0.19/0.51  % (10162)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (10177)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (10158)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (10158)Refutation not found, incomplete strategy% (10158)------------------------------
% 0.19/0.52  % (10158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10158)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10158)Memory used [KB]: 10618
% 0.19/0.52  % (10158)Time elapsed: 0.118 s
% 0.19/0.52  % (10158)------------------------------
% 0.19/0.52  % (10158)------------------------------
% 0.19/0.52  % (10152)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (10174)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (10150)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (10174)Refutation not found, incomplete strategy% (10174)------------------------------
% 0.19/0.52  % (10174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10174)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10174)Memory used [KB]: 6268
% 0.19/0.52  % (10174)Time elapsed: 0.129 s
% 0.19/0.52  % (10174)------------------------------
% 0.19/0.52  % (10174)------------------------------
% 0.19/0.52  % (10160)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (10149)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (10166)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (10149)Refutation not found, incomplete strategy% (10149)------------------------------
% 0.19/0.52  % (10149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10149)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10149)Memory used [KB]: 1663
% 0.19/0.52  % (10149)Time elapsed: 0.126 s
% 0.19/0.52  % (10149)------------------------------
% 0.19/0.52  % (10149)------------------------------
% 0.19/0.52  % (10169)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (10160)Refutation not found, incomplete strategy% (10160)------------------------------
% 0.19/0.52  % (10160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10160)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10160)Memory used [KB]: 10618
% 0.19/0.52  % (10160)Time elapsed: 0.126 s
% 0.19/0.52  % (10160)------------------------------
% 0.19/0.52  % (10160)------------------------------
% 0.19/0.52  % (10166)Refutation not found, incomplete strategy% (10166)------------------------------
% 0.19/0.52  % (10166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10166)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10166)Memory used [KB]: 10618
% 0.19/0.52  % (10166)Time elapsed: 0.128 s
% 0.19/0.52  % (10166)------------------------------
% 0.19/0.52  % (10166)------------------------------
% 0.19/0.52  % (10163)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (10153)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (10172)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (10154)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (10153)Refutation not found, incomplete strategy% (10153)------------------------------
% 0.19/0.53  % (10153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (10153)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (10153)Memory used [KB]: 6140
% 0.19/0.53  % (10153)Time elapsed: 0.129 s
% 0.19/0.53  % (10153)------------------------------
% 0.19/0.53  % (10153)------------------------------
% 0.19/0.53  % (10172)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f158,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(subsumption_resolution,[],[f154,f84])).
% 0.19/0.53  fof(f84,plain,(
% 0.19/0.53    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.53    inference(superposition,[],[f67,f82])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    k1_xboole_0 = k1_tarski(sK0)),
% 0.19/0.53    inference(forward_demodulation,[],[f80,f41])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.53  fof(f80,plain,(
% 0.19/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.19/0.53    inference(superposition,[],[f52,f71])).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.19/0.53    inference(forward_demodulation,[],[f69,f41])).
% 0.19/0.53  fof(f69,plain,(
% 0.19/0.53    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 0.19/0.53    inference(resolution,[],[f68,f57])).
% 0.19/0.53  fof(f57,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f32])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 0.19/0.53    inference(superposition,[],[f47,f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f34])).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.19/0.53    inference(ennf_transformation,[],[f26])).
% 0.19/0.53  fof(f26,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.19/0.53    inference(negated_conjecture,[],[f25])).
% 0.19/0.53  fof(f25,conjecture,(
% 0.19/0.53    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,axiom,(
% 0.19/0.53    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.19/0.53    inference(equality_resolution,[],[f58])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.53    inference(nnf_transformation,[],[f24])).
% 0.19/0.53  fof(f24,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.53  fof(f154,plain,(
% 0.19/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.53    inference(superposition,[],[f141,f71])).
% 0.19/0.53  fof(f141,plain,(
% 0.19/0.53    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(sK0,X2))) )),
% 0.19/0.53    inference(forward_demodulation,[],[f136,f42])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,axiom,(
% 0.19/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.53  fof(f136,plain,(
% 0.19/0.53    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_tarski(sK0,X2))) )),
% 0.19/0.53    inference(superposition,[],[f53,f87])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK0,X6))) )),
% 0.19/0.53    inference(superposition,[],[f52,f82])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (10172)------------------------------
% 0.19/0.53  % (10172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (10172)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (10172)Memory used [KB]: 1791
% 0.19/0.53  % (10172)Time elapsed: 0.130 s
% 0.19/0.53  % (10172)------------------------------
% 0.19/0.53  % (10172)------------------------------
% 0.19/0.53  % (10148)Success in time 0.173 s
%------------------------------------------------------------------------------
