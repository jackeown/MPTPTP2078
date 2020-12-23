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
% DateTime   : Thu Dec  3 12:37:31 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 109 expanded)
%              Number of equality atoms :   50 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1635,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1634,f52])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1634,plain,(
    k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f1632,f161])).

fof(f161,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f158,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f158,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f58,f154])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f147,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f147,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f108])).

fof(f108,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1632,plain,(
    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f168,f1631])).

fof(f1631,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f1627,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f1627,plain,
    ( k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK1 = sK2 ),
    inference(superposition,[],[f168,f456])).

fof(f456,plain,(
    ! [X6,X7] :
      ( k2_xboole_0(k1_tarski(X7),k1_tarski(X6)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X6))
      | X6 = X7 ) ),
    inference(superposition,[],[f58,f109])).

fof(f109,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),k1_tarski(X2))
      | X1 = X2 ) ),
    inference(resolution,[],[f66,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f168,plain,(
    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f49,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f36])).

fof(f36,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (32324)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (32316)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (32307)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (32324)Refutation not found, incomplete strategy% (32324)------------------------------
% 0.22/0.52  % (32324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32324)Memory used [KB]: 1663
% 0.22/0.52  % (32324)Time elapsed: 0.063 s
% 0.22/0.52  % (32324)------------------------------
% 0.22/0.52  % (32324)------------------------------
% 0.22/0.53  % (32316)Refutation not found, incomplete strategy% (32316)------------------------------
% 0.22/0.53  % (32316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32316)Memory used [KB]: 6268
% 0.22/0.53  % (32316)Time elapsed: 0.065 s
% 0.22/0.53  % (32316)------------------------------
% 0.22/0.53  % (32316)------------------------------
% 0.22/0.53  % (32308)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (32321)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (32306)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (32304)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (32326)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (32312)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32302)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (32323)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (32327)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (32325)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (32329)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (32312)Refutation not found, incomplete strategy% (32312)------------------------------
% 0.22/0.55  % (32312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32312)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32312)Memory used [KB]: 10618
% 0.22/0.55  % (32312)Time elapsed: 0.104 s
% 0.22/0.55  % (32312)------------------------------
% 0.22/0.55  % (32312)------------------------------
% 0.22/0.55  % (32305)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (32309)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (32309)Refutation not found, incomplete strategy% (32309)------------------------------
% 0.22/0.55  % (32309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32309)Memory used [KB]: 10746
% 0.22/0.55  % (32309)Time elapsed: 0.134 s
% 0.22/0.55  % (32309)------------------------------
% 0.22/0.55  % (32309)------------------------------
% 0.22/0.55  % (32318)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (32303)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (32328)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (32318)Refutation not found, incomplete strategy% (32318)------------------------------
% 0.22/0.55  % (32318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32318)Memory used [KB]: 10618
% 0.22/0.55  % (32318)Time elapsed: 0.135 s
% 0.22/0.55  % (32318)------------------------------
% 0.22/0.55  % (32318)------------------------------
% 0.22/0.55  % (32303)Refutation not found, incomplete strategy% (32303)------------------------------
% 0.22/0.55  % (32303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32303)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32303)Memory used [KB]: 10746
% 0.22/0.55  % (32303)Time elapsed: 0.132 s
% 0.22/0.55  % (32303)------------------------------
% 0.22/0.55  % (32303)------------------------------
% 0.22/0.55  % (32301)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.55  % (32301)Refutation not found, incomplete strategy% (32301)------------------------------
% 1.48/0.55  % (32301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (32301)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (32301)Memory used [KB]: 1663
% 1.48/0.55  % (32301)Time elapsed: 0.133 s
% 1.48/0.55  % (32301)------------------------------
% 1.48/0.55  % (32301)------------------------------
% 1.48/0.55  % (32321)Refutation not found, incomplete strategy% (32321)------------------------------
% 1.48/0.55  % (32321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (32321)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (32321)Memory used [KB]: 10746
% 1.48/0.55  % (32321)Time elapsed: 0.142 s
% 1.48/0.55  % (32321)------------------------------
% 1.48/0.55  % (32321)------------------------------
% 1.48/0.55  % (32314)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.55  % (32315)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.55  % (32310)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  % (32310)Refutation not found, incomplete strategy% (32310)------------------------------
% 1.48/0.56  % (32310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (32310)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (32310)Memory used [KB]: 10618
% 1.48/0.56  % (32310)Time elapsed: 0.137 s
% 1.48/0.56  % (32310)------------------------------
% 1.48/0.56  % (32310)------------------------------
% 1.48/0.56  % (32330)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.56  % (32319)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.56  % (32322)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.56  % (32320)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (32313)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.57  % (32317)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.57  % (32311)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.57  % (32311)Refutation not found, incomplete strategy% (32311)------------------------------
% 1.48/0.57  % (32311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (32311)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (32311)Memory used [KB]: 10618
% 1.48/0.57  % (32311)Time elapsed: 0.155 s
% 1.48/0.57  % (32311)------------------------------
% 1.48/0.57  % (32311)------------------------------
% 1.66/0.58  % (32322)Refutation not found, incomplete strategy% (32322)------------------------------
% 1.66/0.58  % (32322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (32322)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (32322)Memory used [KB]: 1791
% 1.66/0.58  % (32322)Time elapsed: 0.168 s
% 1.66/0.58  % (32322)------------------------------
% 1.66/0.58  % (32322)------------------------------
% 1.66/0.62  % (32308)Refutation found. Thanks to Tanya!
% 1.66/0.62  % SZS status Theorem for theBenchmark
% 1.66/0.62  % SZS output start Proof for theBenchmark
% 1.66/0.62  fof(f1635,plain,(
% 1.66/0.62    $false),
% 1.66/0.62    inference(subsumption_resolution,[],[f1634,f52])).
% 1.66/0.62  fof(f52,plain,(
% 1.66/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f12])).
% 1.66/0.62  fof(f12,axiom,(
% 1.66/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.62  fof(f1634,plain,(
% 1.66/0.62    k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 1.66/0.62    inference(forward_demodulation,[],[f1632,f161])).
% 1.66/0.62  fof(f161,plain,(
% 1.66/0.62    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 1.66/0.62    inference(forward_demodulation,[],[f158,f51])).
% 1.66/0.62  fof(f51,plain,(
% 1.66/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f7])).
% 1.66/0.62  fof(f7,axiom,(
% 1.66/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.66/0.62  fof(f158,plain,(
% 1.66/0.62    ( ! [X1] : (k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.66/0.62    inference(superposition,[],[f58,f154])).
% 1.66/0.62  fof(f154,plain,(
% 1.66/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.66/0.62    inference(forward_demodulation,[],[f147,f92])).
% 1.66/0.62  fof(f92,plain,(
% 1.66/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.62    inference(resolution,[],[f91,f53])).
% 1.66/0.62  fof(f53,plain,(
% 1.66/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f39])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f28,plain,(
% 1.66/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.66/0.62    inference(ennf_transformation,[],[f4])).
% 1.66/0.62  fof(f4,axiom,(
% 1.66/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.66/0.62  fof(f91,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.66/0.62    inference(resolution,[],[f62,f50])).
% 1.66/0.62  fof(f50,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.66/0.62  fof(f62,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f41])).
% 1.66/0.62  fof(f41,plain,(
% 1.66/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f40])).
% 1.66/0.62  fof(f40,plain,(
% 1.66/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f29,plain,(
% 1.66/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f26])).
% 1.66/0.62  fof(f26,plain,(
% 1.66/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(rectify,[],[f3])).
% 1.66/0.62  fof(f3,axiom,(
% 1.66/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.66/0.62  fof(f147,plain,(
% 1.66/0.62    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.66/0.62    inference(superposition,[],[f60,f108])).
% 1.66/0.62  fof(f108,plain,(
% 1.66/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.62    inference(resolution,[],[f66,f50])).
% 1.66/0.62  fof(f66,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f42])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(nnf_transformation,[],[f9])).
% 1.66/0.62  fof(f9,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f6])).
% 1.66/0.62  fof(f6,axiom,(
% 1.66/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.62  fof(f58,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f10])).
% 1.66/0.62  fof(f10,axiom,(
% 1.66/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.66/0.62  fof(f1632,plain,(
% 1.66/0.62    k2_tarski(sK1,sK1) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.66/0.62    inference(backward_demodulation,[],[f168,f1631])).
% 1.66/0.62  fof(f1631,plain,(
% 1.66/0.62    sK1 = sK2),
% 1.66/0.62    inference(subsumption_resolution,[],[f1627,f64])).
% 1.66/0.62  fof(f64,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f31])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.66/0.62    inference(ennf_transformation,[],[f22])).
% 1.66/0.62  fof(f22,axiom,(
% 1.66/0.62    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.66/0.62  fof(f1627,plain,(
% 1.66/0.62    k2_tarski(sK1,sK2) != k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK1 = sK2),
% 1.66/0.62    inference(superposition,[],[f168,f456])).
% 1.66/0.62  fof(f456,plain,(
% 1.66/0.62    ( ! [X6,X7] : (k2_xboole_0(k1_tarski(X7),k1_tarski(X6)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X6)) | X6 = X7) )),
% 1.66/0.62    inference(superposition,[],[f58,f109])).
% 1.66/0.62  fof(f109,plain,(
% 1.66/0.62    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) | X1 = X2) )),
% 1.66/0.62    inference(resolution,[],[f66,f63])).
% 1.66/0.62  fof(f63,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f30])).
% 1.66/0.62  fof(f30,plain,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.66/0.62    inference(ennf_transformation,[],[f21])).
% 1.66/0.62  fof(f21,axiom,(
% 1.66/0.62    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.66/0.62  fof(f168,plain,(
% 1.66/0.62    k2_tarski(sK1,sK2) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.66/0.62    inference(superposition,[],[f49,f56])).
% 1.66/0.62  fof(f56,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f20])).
% 1.66/0.62  fof(f20,axiom,(
% 1.66/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.66/0.62  fof(f49,plain,(
% 1.66/0.62    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.66/0.62    inference(cnf_transformation,[],[f37])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f36])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK1,sK2) != k3_tarski(k2_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f24])).
% 1.66/0.62  fof(f24,negated_conjecture,(
% 1.66/0.62    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.66/0.62    inference(negated_conjecture,[],[f23])).
% 1.66/0.62  fof(f23,conjecture,(
% 1.66/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (32308)------------------------------
% 1.66/0.62  % (32308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (32308)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (32308)Memory used [KB]: 7164
% 1.66/0.62  % (32308)Time elapsed: 0.164 s
% 1.66/0.62  % (32308)------------------------------
% 1.66/0.62  % (32308)------------------------------
% 1.66/0.62  % (32300)Success in time 0.244 s
%------------------------------------------------------------------------------
