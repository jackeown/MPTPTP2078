%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  62 expanded)
%              Number of equality atoms :   40 (  54 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(subsumption_resolution,[],[f874,f52])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f874,plain,(
    k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f872,f92])).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f91,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f91,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f58,f52])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f872,plain,(
    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f177,f871])).

fof(f871,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f868,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f868,plain,
    ( k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK1 = sK2 ),
    inference(superposition,[],[f177,f678])).

fof(f678,plain,(
    ! [X6,X5] :
      ( k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5))
      | X5 = X6 ) ),
    inference(superposition,[],[f60,f101])).

fof(f101,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) = k4_xboole_0(k1_tarski(X2),k1_tarski(X3))
      | X2 = X3 ) ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f177,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f50,f58])).

fof(f50,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f37])).

fof(f37,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (18913)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.49  % (18937)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.49  % (18929)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.49  % (18921)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (18929)Refutation not found, incomplete strategy% (18929)------------------------------
% 0.22/0.50  % (18929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18921)Refutation not found, incomplete strategy% (18921)------------------------------
% 0.22/0.50  % (18921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18929)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18929)Memory used [KB]: 10618
% 0.22/0.50  % (18929)Time elapsed: 0.116 s
% 0.22/0.50  % (18929)------------------------------
% 0.22/0.50  % (18929)------------------------------
% 0.22/0.51  % (18921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18921)Memory used [KB]: 10618
% 0.22/0.51  % (18921)Time elapsed: 0.116 s
% 0.22/0.51  % (18921)------------------------------
% 0.22/0.51  % (18921)------------------------------
% 0.22/0.51  % (18912)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (18916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (18928)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (18919)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (18912)Refutation not found, incomplete strategy% (18912)------------------------------
% 0.22/0.52  % (18912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18912)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18912)Memory used [KB]: 1663
% 0.22/0.52  % (18912)Time elapsed: 0.110 s
% 0.22/0.52  % (18912)------------------------------
% 0.22/0.52  % (18912)------------------------------
% 0.22/0.53  % (18940)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (18927)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (18920)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (18932)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (18927)Refutation not found, incomplete strategy% (18927)------------------------------
% 0.22/0.53  % (18927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18934)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (18927)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18927)Memory used [KB]: 6268
% 0.22/0.53  % (18927)Time elapsed: 0.122 s
% 0.22/0.53  % (18927)------------------------------
% 0.22/0.53  % (18927)------------------------------
% 0.22/0.53  % (18920)Refutation not found, incomplete strategy% (18920)------------------------------
% 0.22/0.53  % (18920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18920)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18920)Memory used [KB]: 10746
% 0.22/0.54  % (18920)Time elapsed: 0.126 s
% 0.22/0.54  % (18920)------------------------------
% 0.22/0.54  % (18920)------------------------------
% 0.22/0.54  % (18916)Refutation not found, incomplete strategy% (18916)------------------------------
% 0.22/0.54  % (18916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18914)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18936)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (18915)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (18914)Refutation not found, incomplete strategy% (18914)------------------------------
% 0.22/0.54  % (18914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18914)Memory used [KB]: 10746
% 0.22/0.54  % (18914)Time elapsed: 0.125 s
% 0.22/0.54  % (18914)------------------------------
% 0.22/0.54  % (18914)------------------------------
% 0.22/0.54  % (18932)Refutation not found, incomplete strategy% (18932)------------------------------
% 0.22/0.54  % (18932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18926)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18917)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (18932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18924)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18932)Memory used [KB]: 10746
% 0.22/0.54  % (18932)Time elapsed: 0.131 s
% 0.22/0.54  % (18932)------------------------------
% 0.22/0.54  % (18932)------------------------------
% 0.22/0.54  % (18916)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18916)Memory used [KB]: 6396
% 0.22/0.54  % (18916)Time elapsed: 0.127 s
% 0.22/0.54  % (18916)------------------------------
% 0.22/0.54  % (18916)------------------------------
% 0.22/0.55  % (18939)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18918)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (18938)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (18930)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18941)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (18931)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18922)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (18933)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (18922)Refutation not found, incomplete strategy% (18922)------------------------------
% 0.22/0.56  % (18922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18922)Memory used [KB]: 10618
% 0.22/0.56  % (18922)Time elapsed: 0.149 s
% 0.22/0.56  % (18922)------------------------------
% 0.22/0.56  % (18922)------------------------------
% 0.22/0.56  % (18935)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (18933)Refutation not found, incomplete strategy% (18933)------------------------------
% 0.22/0.56  % (18933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18933)Memory used [KB]: 1791
% 0.22/0.56  % (18933)Time elapsed: 0.150 s
% 0.22/0.56  % (18933)------------------------------
% 0.22/0.56  % (18933)------------------------------
% 0.22/0.56  % (18935)Refutation not found, incomplete strategy% (18935)------------------------------
% 0.22/0.56  % (18935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18935)Memory used [KB]: 1663
% 0.22/0.56  % (18935)Time elapsed: 0.124 s
% 0.22/0.56  % (18935)------------------------------
% 0.22/0.56  % (18935)------------------------------
% 0.22/0.56  % (18925)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (18923)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (18923)Refutation not found, incomplete strategy% (18923)------------------------------
% 0.22/0.56  % (18923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18923)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18923)Memory used [KB]: 10618
% 0.22/0.56  % (18923)Time elapsed: 0.158 s
% 0.22/0.56  % (18923)------------------------------
% 0.22/0.56  % (18923)------------------------------
% 0.22/0.58  % (18919)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f875,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f874,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.58  fof(f874,plain,(
% 0.22/0.58    k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 0.22/0.58    inference(forward_demodulation,[],[f872,f92])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.58    inference(forward_demodulation,[],[f91,f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,axiom,(
% 0.22/0.58    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(superposition,[],[f58,f52])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.58  fof(f872,plain,(
% 0.22/0.58    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.22/0.58    inference(backward_demodulation,[],[f177,f871])).
% 0.22/0.58  fof(f871,plain,(
% 0.22/0.58    sK1 = sK2),
% 0.22/0.58    inference(subsumption_resolution,[],[f868,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.22/0.58  fof(f868,plain,(
% 0.22/0.58    k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK1 = sK2),
% 0.22/0.58    inference(superposition,[],[f177,f678])).
% 0.22/0.58  fof(f678,plain,(
% 0.22/0.58    ( ! [X6,X5] : (k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5)) | X5 = X6) )),
% 0.22/0.58    inference(superposition,[],[f60,f101])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    ( ! [X2,X3] : (k1_tarski(X2) = k4_xboole_0(k1_tarski(X2),k1_tarski(X3)) | X2 = X3) )),
% 0.22/0.58    inference(resolution,[],[f68,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.58    inference(superposition,[],[f50,f58])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.58    inference(negated_conjecture,[],[f23])).
% 0.22/0.58  fof(f23,conjecture,(
% 0.22/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (18919)------------------------------
% 0.22/0.58  % (18919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (18919)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (18919)Memory used [KB]: 6780
% 0.22/0.58  % (18919)Time elapsed: 0.146 s
% 0.22/0.58  % (18919)------------------------------
% 0.22/0.58  % (18919)------------------------------
% 0.22/0.58  % (18910)Success in time 0.214 s
%------------------------------------------------------------------------------
