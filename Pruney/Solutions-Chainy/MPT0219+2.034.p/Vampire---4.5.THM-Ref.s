%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:24 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 ( 104 expanded)
%              Number of equality atoms :   49 (  71 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2905,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f26,f2396,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f2396,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f2384])).

fof(f2384,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f40,f2236])).

fof(f2236,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f2170,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2170,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k3_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f1023,f25])).

fof(f25,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1023,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f31,f313])).

fof(f313,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f312,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f312,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f302,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f302,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f33,f98])).

fof(f98,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f68,plain,(
    ! [X6,X7] : r1_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X7,k4_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.50  % (14292)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.50  % (14284)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14281)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (14289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (14300)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (14283)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (14278)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (14290)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (14290)Refutation not found, incomplete strategy% (14290)------------------------------
% 0.22/0.53  % (14290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14290)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14290)Memory used [KB]: 10618
% 0.22/0.53  % (14290)Time elapsed: 0.110 s
% 0.22/0.53  % (14290)------------------------------
% 0.22/0.53  % (14290)------------------------------
% 0.22/0.53  % (14297)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (14306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.53  % (14291)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.54  % (14307)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.54  % (14299)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.54  % (14298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.54  % (14280)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.54  % (14282)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.54  % (14294)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.55  % (14288)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.55  % (14302)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.55  % (14302)Refutation not found, incomplete strategy% (14302)------------------------------
% 1.23/0.55  % (14302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (14286)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.55  % (14302)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (14302)Memory used [KB]: 10618
% 1.43/0.55  % (14302)Time elapsed: 0.131 s
% 1.43/0.55  % (14302)------------------------------
% 1.43/0.55  % (14302)------------------------------
% 1.43/0.55  % (14295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.55  % (14294)Refutation not found, incomplete strategy% (14294)------------------------------
% 1.43/0.55  % (14294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (14294)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (14294)Memory used [KB]: 10618
% 1.43/0.55  % (14294)Time elapsed: 0.131 s
% 1.43/0.55  % (14294)------------------------------
% 1.43/0.55  % (14294)------------------------------
% 1.43/0.56  % (14279)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.56  % (14307)Refutation not found, incomplete strategy% (14307)------------------------------
% 1.43/0.56  % (14307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (14307)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (14307)Memory used [KB]: 1663
% 1.43/0.56  % (14307)Time elapsed: 0.003 s
% 1.43/0.56  % (14307)------------------------------
% 1.43/0.56  % (14307)------------------------------
% 1.43/0.56  % (14306)Refutation not found, incomplete strategy% (14306)------------------------------
% 1.43/0.56  % (14306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (14306)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (14306)Memory used [KB]: 10746
% 1.43/0.56  % (14306)Time elapsed: 0.144 s
% 1.43/0.56  % (14306)------------------------------
% 1.43/0.56  % (14306)------------------------------
% 1.43/0.56  % (14296)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.57  % (14305)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.57  % (14305)Refutation not found, incomplete strategy% (14305)------------------------------
% 1.43/0.57  % (14305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (14305)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (14305)Memory used [KB]: 6140
% 1.43/0.57  % (14305)Time elapsed: 0.152 s
% 1.43/0.57  % (14305)------------------------------
% 1.43/0.57  % (14305)------------------------------
% 1.43/0.57  % (14304)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.57  % (14301)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.57  % (14288)Refutation not found, incomplete strategy% (14288)------------------------------
% 1.43/0.57  % (14288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (14288)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (14288)Memory used [KB]: 10746
% 1.43/0.57  % (14288)Time elapsed: 0.136 s
% 1.43/0.57  % (14288)------------------------------
% 1.43/0.57  % (14288)------------------------------
% 1.43/0.57  % (14287)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.57  % (14279)Refutation not found, incomplete strategy% (14279)------------------------------
% 1.43/0.57  % (14279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (14279)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (14279)Memory used [KB]: 1663
% 1.43/0.57  % (14279)Time elapsed: 0.142 s
% 1.43/0.57  % (14279)------------------------------
% 1.43/0.57  % (14279)------------------------------
% 1.43/0.57  % (14303)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.57  % (14293)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.58  % (14295)Refutation not found, incomplete strategy% (14295)------------------------------
% 1.43/0.58  % (14295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (14295)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.58  
% 1.43/0.58  % (14295)Memory used [KB]: 1663
% 1.43/0.58  % (14295)Time elapsed: 0.162 s
% 1.43/0.58  % (14295)------------------------------
% 1.43/0.58  % (14295)------------------------------
% 1.43/0.59  % (14285)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.99/0.66  % (14281)Refutation not found, incomplete strategy% (14281)------------------------------
% 1.99/0.66  % (14281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.66  % (14281)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.66  
% 1.99/0.66  % (14281)Memory used [KB]: 6140
% 1.99/0.66  % (14281)Time elapsed: 0.237 s
% 1.99/0.66  % (14281)------------------------------
% 1.99/0.66  % (14281)------------------------------
% 1.99/0.67  % (14329)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.23/0.69  % (14335)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.23/0.69  % (14333)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.23/0.70  % (14330)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.23/0.70  % (14333)Refutation not found, incomplete strategy% (14333)------------------------------
% 2.23/0.70  % (14333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.70  % (14333)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.70  
% 2.23/0.70  % (14333)Memory used [KB]: 10618
% 2.23/0.70  % (14333)Time elapsed: 0.107 s
% 2.23/0.70  % (14333)------------------------------
% 2.23/0.70  % (14333)------------------------------
% 2.23/0.70  % (14331)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.23/0.70  % (14334)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.23/0.70  % (14331)Refutation not found, incomplete strategy% (14331)------------------------------
% 2.23/0.70  % (14331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.70  % (14331)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.70  
% 2.23/0.70  % (14331)Memory used [KB]: 6140
% 2.23/0.70  % (14331)Time elapsed: 0.100 s
% 2.23/0.70  % (14331)------------------------------
% 2.23/0.70  % (14331)------------------------------
% 2.23/0.70  % (14334)Refutation not found, incomplete strategy% (14334)------------------------------
% 2.23/0.70  % (14334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.70  % (14334)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.70  
% 2.23/0.70  % (14334)Memory used [KB]: 1663
% 2.23/0.70  % (14334)Time elapsed: 0.084 s
% 2.23/0.70  % (14334)------------------------------
% 2.23/0.70  % (14334)------------------------------
% 2.23/0.71  % (14332)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.23/0.73  % (14337)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.23/0.74  % (14336)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.67/0.76  % (14285)Refutation found. Thanks to Tanya!
% 2.67/0.76  % SZS status Theorem for theBenchmark
% 2.67/0.76  % SZS output start Proof for theBenchmark
% 2.67/0.76  fof(f2905,plain,(
% 2.67/0.76    $false),
% 2.67/0.76    inference(unit_resulting_resolution,[],[f26,f2396,f35])).
% 2.67/0.76  fof(f35,plain,(
% 2.67/0.76    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.67/0.76    inference(cnf_transformation,[],[f19])).
% 2.67/0.76  fof(f19,plain,(
% 2.67/0.76    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.67/0.76    inference(ennf_transformation,[],[f14])).
% 2.67/0.76  fof(f14,axiom,(
% 2.67/0.76    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.67/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.67/0.76  fof(f2396,plain,(
% 2.67/0.76    r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 2.67/0.76    inference(trivial_inequality_removal,[],[f2384])).
% 2.67/0.76  fof(f2384,plain,(
% 2.67/0.76    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 2.67/0.76    inference(superposition,[],[f40,f2236])).
% 2.67/0.76  fof(f2236,plain,(
% 2.67/0.76    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 2.67/0.76    inference(forward_demodulation,[],[f2170,f45])).
% 2.67/0.76  fof(f45,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.67/0.76    inference(resolution,[],[f38,f28])).
% 2.67/0.76  fof(f28,plain,(
% 2.67/0.76    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.67/0.76    inference(cnf_transformation,[],[f7])).
% 2.67/0.76  fof(f7,axiom,(
% 2.67/0.76    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.67/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.67/0.76  fof(f38,plain,(
% 2.67/0.76    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.67/0.76    inference(cnf_transformation,[],[f24])).
% 2.78/0.76  fof(f24,plain,(
% 2.78/0.76    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.78/0.76    inference(nnf_transformation,[],[f3])).
% 2.78/0.76  fof(f3,axiom,(
% 2.78/0.76    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.78/0.76  fof(f2170,plain,(
% 2.78/0.76    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k3_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_tarski(sK0))),
% 2.78/0.76    inference(superposition,[],[f1023,f25])).
% 2.78/0.76  fof(f25,plain,(
% 2.78/0.76    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.78/0.76    inference(cnf_transformation,[],[f22])).
% 2.78/0.76  fof(f22,plain,(
% 2.78/0.76    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.78/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).
% 2.78/0.76  fof(f21,plain,(
% 2.78/0.76    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.78/0.76    introduced(choice_axiom,[])).
% 2.78/0.76  fof(f18,plain,(
% 2.78/0.76    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.78/0.76    inference(ennf_transformation,[],[f16])).
% 2.78/0.76  fof(f16,negated_conjecture,(
% 2.78/0.76    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.78/0.76    inference(negated_conjecture,[],[f15])).
% 2.78/0.76  fof(f15,conjecture,(
% 2.78/0.76    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.78/0.76  fof(f1023,plain,(
% 2.78/0.76    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 2.78/0.76    inference(superposition,[],[f31,f313])).
% 2.78/0.76  fof(f313,plain,(
% 2.78/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 2.78/0.76    inference(forward_demodulation,[],[f312,f33])).
% 2.78/0.76  fof(f33,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.78/0.76    inference(cnf_transformation,[],[f9])).
% 2.78/0.76  fof(f9,axiom,(
% 2.78/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.78/0.76  fof(f312,plain,(
% 2.78/0.76    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 2.78/0.76    inference(forward_demodulation,[],[f302,f29])).
% 2.78/0.76  fof(f29,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.78/0.76    inference(cnf_transformation,[],[f2])).
% 2.78/0.76  fof(f2,axiom,(
% 2.78/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.78/0.76  fof(f302,plain,(
% 2.78/0.76    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 2.78/0.76    inference(superposition,[],[f33,f98])).
% 2.78/0.76  fof(f98,plain,(
% 2.78/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 2.78/0.76    inference(resolution,[],[f68,f36])).
% 2.78/0.76  fof(f36,plain,(
% 2.78/0.76    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.78/0.76    inference(cnf_transformation,[],[f23])).
% 2.78/0.76  fof(f23,plain,(
% 2.78/0.76    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.78/0.76    inference(nnf_transformation,[],[f8])).
% 2.78/0.76  fof(f8,axiom,(
% 2.78/0.76    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.78/0.76  fof(f68,plain,(
% 2.78/0.76    ( ! [X6,X7] : (r1_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 2.78/0.76    inference(trivial_inequality_removal,[],[f67])).
% 2.78/0.76  fof(f67,plain,(
% 2.78/0.76    ( ! [X6,X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 2.78/0.76    inference(superposition,[],[f46,f45])).
% 2.78/0.76  fof(f46,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.78/0.76    inference(superposition,[],[f39,f30])).
% 2.78/0.76  fof(f30,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.78/0.76    inference(cnf_transformation,[],[f1])).
% 2.78/0.76  fof(f1,axiom,(
% 2.78/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.78/0.76  fof(f39,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.78/0.76    inference(cnf_transformation,[],[f24])).
% 2.78/0.76  fof(f31,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.78/0.76    inference(cnf_transformation,[],[f6])).
% 2.78/0.76  fof(f6,axiom,(
% 2.78/0.76    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.78/0.76  fof(f40,plain,(
% 2.78/0.76    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 2.78/0.76    inference(cnf_transformation,[],[f20])).
% 2.78/0.76  fof(f20,plain,(
% 2.78/0.76    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 2.78/0.76    inference(ennf_transformation,[],[f17])).
% 2.78/0.76  fof(f17,plain,(
% 2.78/0.76    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 2.78/0.76    inference(unused_predicate_definition_removal,[],[f4])).
% 2.78/0.76  fof(f4,axiom,(
% 2.78/0.76    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.78/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.78/0.76  fof(f26,plain,(
% 2.78/0.76    sK0 != sK1),
% 2.78/0.76    inference(cnf_transformation,[],[f22])).
% 2.78/0.76  % SZS output end Proof for theBenchmark
% 2.78/0.76  % (14285)------------------------------
% 2.78/0.76  % (14285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.76  % (14285)Termination reason: Refutation
% 2.78/0.76  
% 2.78/0.76  % (14285)Memory used [KB]: 2942
% 2.78/0.76  % (14285)Time elapsed: 0.265 s
% 2.78/0.76  % (14285)------------------------------
% 2.78/0.76  % (14285)------------------------------
% 2.78/0.76  % (14277)Success in time 0.384 s
%------------------------------------------------------------------------------
