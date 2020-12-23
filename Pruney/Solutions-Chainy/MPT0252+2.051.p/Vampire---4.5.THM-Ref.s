%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:58 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 206 expanded)
%              Number of leaves         :    7 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 583 expanded)
%              Number of equality atoms :   20 ( 123 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f483,plain,(
    $false ),
    inference(resolution,[],[f260,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f260,plain,(
    r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f168,f226])).

fof(f226,plain,(
    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) ),
    inference(resolution,[],[f166,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f166,plain,(
    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2) ),
    inference(superposition,[],[f58,f132])).

fof(f132,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(resolution,[],[f129,f73])).

fof(f73,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X2,X1))
      | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ) ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f61,f67])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X1,X1,X0))
      | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
      | ~ r2_hidden(X0,k1_enumset1(X1,X1,X0)) ) ),
    inference(resolution,[],[f117,f73])).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_enumset1(X3,X3,X4))
      | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3)
      | ~ r2_hidden(X4,k1_enumset1(X5,X5,X3))
      | ~ r2_hidden(X3,k1_enumset1(X5,X5,X3)) ) ),
    inference(resolution,[],[f102,f75])).

fof(f102,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(X10,k1_enumset1(X8,X8,X9))
      | k1_enumset1(X8,X8,X9) = k1_enumset1(X7,X7,X10)
      | ~ r2_hidden(X7,k1_enumset1(X8,X8,X9))
      | ~ r2_hidden(X9,k1_enumset1(X7,X7,X10))
      | ~ r2_hidden(X8,k1_enumset1(X7,X7,X10)) ) ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,k1_enumset1(X8,X8,X6))
      | ~ r2_hidden(X8,X7)
      | k1_enumset1(X8,X8,X6) = X7
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f59,f41])).

fof(f58,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f34,f53,f50])).

fof(f34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,(
    ! [X255,X253,X254] : r2_hidden(X253,k3_tarski(k1_enumset1(X255,X255,k1_enumset1(X253,X253,X254)))) ),
    inference(superposition,[],[f76,f132])).

fof(f76,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4))) ),
    inference(resolution,[],[f61,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (27245)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (27254)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (27254)Refutation not found, incomplete strategy% (27254)------------------------------
% 0.22/0.55  % (27254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (27247)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.56  % (27254)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (27254)Memory used [KB]: 10618
% 1.49/0.56  % (27254)Time elapsed: 0.121 s
% 1.49/0.56  % (27254)------------------------------
% 1.49/0.56  % (27254)------------------------------
% 1.49/0.56  % (27269)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.49/0.57  % (27246)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.49/0.57  % (27253)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.49/0.57  % (27262)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.57  % (27269)Refutation not found, incomplete strategy% (27269)------------------------------
% 1.49/0.57  % (27269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (27253)Refutation not found, incomplete strategy% (27253)------------------------------
% 1.49/0.57  % (27253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (27269)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (27269)Memory used [KB]: 6268
% 1.49/0.57  % (27269)Time elapsed: 0.143 s
% 1.49/0.57  % (27269)------------------------------
% 1.49/0.57  % (27269)------------------------------
% 1.49/0.57  % (27253)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (27253)Memory used [KB]: 6396
% 1.49/0.57  % (27253)Time elapsed: 0.144 s
% 1.49/0.57  % (27253)------------------------------
% 1.49/0.57  % (27253)------------------------------
% 1.49/0.57  % (27244)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.58  % (27248)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.58  % (27242)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.59  % (27265)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.59  % (27257)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.60  % (27250)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.60  % (27271)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.60  % (27271)Refutation not found, incomplete strategy% (27271)------------------------------
% 1.66/0.60  % (27271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (27271)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (27271)Memory used [KB]: 1663
% 1.66/0.60  % (27271)Time elapsed: 0.170 s
% 1.66/0.60  % (27271)------------------------------
% 1.66/0.60  % (27271)------------------------------
% 1.66/0.60  % (27266)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.60  % (27249)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.60  % (27268)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.66/0.61  % (27266)Refutation not found, incomplete strategy% (27266)------------------------------
% 1.66/0.61  % (27266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (27266)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (27266)Memory used [KB]: 10746
% 1.66/0.61  % (27266)Time elapsed: 0.182 s
% 1.66/0.61  % (27266)------------------------------
% 1.66/0.61  % (27266)------------------------------
% 1.66/0.61  % (27264)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.61  % (27260)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.61  % (27267)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.61  % (27260)Refutation not found, incomplete strategy% (27260)------------------------------
% 1.66/0.61  % (27260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (27260)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (27260)Memory used [KB]: 1663
% 1.66/0.61  % (27260)Time elapsed: 0.181 s
% 1.66/0.61  % (27260)------------------------------
% 1.66/0.61  % (27260)------------------------------
% 1.66/0.61  % (27243)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.61  % (27263)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.66/0.61  % (27243)Refutation not found, incomplete strategy% (27243)------------------------------
% 1.66/0.61  % (27243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (27243)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (27243)Memory used [KB]: 1663
% 1.66/0.61  % (27243)Time elapsed: 0.181 s
% 1.66/0.61  % (27243)------------------------------
% 1.66/0.61  % (27243)------------------------------
% 1.66/0.61  % (27256)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.61  % (27256)Refutation not found, incomplete strategy% (27256)------------------------------
% 1.66/0.61  % (27256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (27256)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (27256)Memory used [KB]: 1663
% 1.66/0.61  % (27256)Time elapsed: 0.195 s
% 1.66/0.61  % (27256)------------------------------
% 1.66/0.61  % (27256)------------------------------
% 1.66/0.61  % (27258)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.62  % (27255)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.62  % (27258)Refutation not found, incomplete strategy% (27258)------------------------------
% 1.66/0.62  % (27258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (27258)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.62  
% 1.66/0.62  % (27258)Memory used [KB]: 10618
% 1.66/0.62  % (27258)Time elapsed: 0.191 s
% 1.66/0.62  % (27258)------------------------------
% 1.66/0.62  % (27258)------------------------------
% 1.66/0.62  % (27270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.62  % (27252)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.66/0.62  % (27252)Refutation not found, incomplete strategy% (27252)------------------------------
% 1.66/0.62  % (27252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (27251)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.66/0.63  % (27268)Refutation not found, incomplete strategy% (27268)------------------------------
% 1.66/0.63  % (27268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (27261)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.63  % (27268)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (27268)Memory used [KB]: 6268
% 1.66/0.63  % (27268)Time elapsed: 0.201 s
% 1.66/0.63  % (27268)------------------------------
% 1.66/0.63  % (27268)------------------------------
% 1.66/0.63  % (27270)Refutation not found, incomplete strategy% (27270)------------------------------
% 1.66/0.63  % (27270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (27270)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (27270)Memory used [KB]: 10874
% 1.66/0.63  % (27270)Time elapsed: 0.204 s
% 1.66/0.63  % (27270)------------------------------
% 1.66/0.63  % (27270)------------------------------
% 1.66/0.63  % (27267)Refutation not found, incomplete strategy% (27267)------------------------------
% 1.66/0.63  % (27267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (27267)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (27267)Memory used [KB]: 6268
% 1.66/0.63  % (27267)Time elapsed: 0.176 s
% 1.66/0.63  % (27267)------------------------------
% 1.66/0.63  % (27267)------------------------------
% 1.66/0.64  % (27252)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.64  
% 1.66/0.64  % (27252)Memory used [KB]: 10874
% 1.66/0.64  % (27252)Time elapsed: 0.192 s
% 1.66/0.64  % (27252)------------------------------
% 1.66/0.64  % (27252)------------------------------
% 1.66/0.64  % (27259)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.66/0.65  % (27259)Refutation not found, incomplete strategy% (27259)------------------------------
% 1.66/0.65  % (27259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (27259)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (27259)Memory used [KB]: 1918
% 2.19/0.66  % (27259)Time elapsed: 0.221 s
% 2.19/0.66  % (27259)------------------------------
% 2.19/0.66  % (27259)------------------------------
% 2.31/0.72  % (27245)Refutation not found, incomplete strategy% (27245)------------------------------
% 2.31/0.72  % (27245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.73  % (27245)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.73  
% 2.50/0.73  % (27245)Memory used [KB]: 6140
% 2.50/0.73  % (27245)Time elapsed: 0.282 s
% 2.50/0.73  % (27245)------------------------------
% 2.50/0.73  % (27245)------------------------------
% 2.64/0.75  % (27309)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.64/0.75  % (27310)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.64/0.76  % (27310)Refutation not found, incomplete strategy% (27310)------------------------------
% 2.64/0.76  % (27310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.76  % (27310)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.76  
% 2.64/0.76  % (27310)Memory used [KB]: 6268
% 2.64/0.76  % (27310)Time elapsed: 0.106 s
% 2.64/0.76  % (27310)------------------------------
% 2.64/0.76  % (27310)------------------------------
% 2.64/0.77  % (27308)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.64/0.77  % (27317)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.64/0.78  % (27257)Refutation not found, incomplete strategy% (27257)------------------------------
% 2.64/0.78  % (27257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.78  % (27257)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.78  
% 2.64/0.78  % (27257)Memory used [KB]: 6140
% 2.64/0.78  % (27257)Time elapsed: 0.309 s
% 2.64/0.78  % (27257)------------------------------
% 2.64/0.78  % (27257)------------------------------
% 2.64/0.78  % (27242)Refutation not found, incomplete strategy% (27242)------------------------------
% 2.64/0.78  % (27242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.78  % (27242)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.78  
% 2.64/0.78  % (27242)Memory used [KB]: 1791
% 2.64/0.78  % (27242)Time elapsed: 0.353 s
% 2.64/0.78  % (27242)------------------------------
% 2.64/0.78  % (27242)------------------------------
% 2.64/0.79  % (27244)Refutation not found, incomplete strategy% (27244)------------------------------
% 2.64/0.79  % (27244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.79  % (27250)Refutation not found, incomplete strategy% (27250)------------------------------
% 2.64/0.79  % (27250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.79  % (27250)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.79  
% 2.64/0.79  % (27250)Memory used [KB]: 6268
% 2.64/0.79  % (27250)Time elapsed: 0.364 s
% 2.64/0.79  % (27250)------------------------------
% 2.64/0.79  % (27250)------------------------------
% 2.64/0.79  % (27311)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.64/0.80  % (27312)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.64/0.80  % (27244)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.80  
% 2.64/0.80  % (27244)Memory used [KB]: 6396
% 2.64/0.80  % (27244)Time elapsed: 0.363 s
% 2.64/0.80  % (27244)------------------------------
% 2.64/0.80  % (27244)------------------------------
% 2.64/0.80  % (27317)Refutation not found, incomplete strategy% (27317)------------------------------
% 2.64/0.80  % (27317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.80  % (27317)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.80  
% 2.64/0.80  % (27317)Memory used [KB]: 10746
% 2.64/0.80  % (27317)Time elapsed: 0.099 s
% 2.64/0.80  % (27317)------------------------------
% 2.64/0.80  % (27317)------------------------------
% 2.64/0.80  % (27312)Refutation not found, incomplete strategy% (27312)------------------------------
% 2.64/0.80  % (27312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.80  % (27312)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.80  
% 2.64/0.80  % (27312)Memory used [KB]: 10746
% 2.64/0.80  % (27312)Time elapsed: 0.147 s
% 2.64/0.80  % (27312)------------------------------
% 2.64/0.80  % (27312)------------------------------
% 2.64/0.80  % (27319)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.64/0.81  % (27315)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.64/0.81  % (27319)Refutation not found, incomplete strategy% (27319)------------------------------
% 2.64/0.81  % (27319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.81  % (27319)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.81  
% 2.64/0.81  % (27319)Memory used [KB]: 10746
% 2.64/0.81  % (27319)Time elapsed: 0.142 s
% 2.64/0.81  % (27319)------------------------------
% 2.64/0.81  % (27319)------------------------------
% 2.64/0.81  % (27314)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.64/0.81  % (27314)Refutation not found, incomplete strategy% (27314)------------------------------
% 2.64/0.81  % (27314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.81  % (27314)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.81  
% 2.64/0.81  % (27314)Memory used [KB]: 10746
% 2.64/0.81  % (27314)Time elapsed: 0.153 s
% 2.64/0.81  % (27314)------------------------------
% 2.64/0.81  % (27314)------------------------------
% 2.64/0.81  % (27320)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.64/0.81  % (27313)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.64/0.81  % (27316)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.64/0.81  % (27313)Refutation not found, incomplete strategy% (27313)------------------------------
% 2.64/0.81  % (27313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.81  % (27313)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.81  
% 2.64/0.81  % (27313)Memory used [KB]: 1918
% 2.64/0.81  % (27313)Time elapsed: 0.154 s
% 2.64/0.81  % (27313)------------------------------
% 2.64/0.81  % (27313)------------------------------
% 2.64/0.81  % (27311)Refutation not found, incomplete strategy% (27311)------------------------------
% 2.64/0.81  % (27311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.81  % (27311)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.81  
% 2.64/0.81  % (27311)Memory used [KB]: 10618
% 2.64/0.81  % (27311)Time elapsed: 0.174 s
% 2.64/0.81  % (27311)------------------------------
% 2.64/0.81  % (27311)------------------------------
% 2.64/0.82  % (27321)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.30/0.83  % (27318)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.30/0.84  % (27322)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.30/0.84  % (27321)Refutation not found, incomplete strategy% (27321)------------------------------
% 3.30/0.84  % (27321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.30/0.84  % (27321)Termination reason: Refutation not found, incomplete strategy
% 3.30/0.84  
% 3.30/0.84  % (27321)Memory used [KB]: 10746
% 3.30/0.84  % (27321)Time elapsed: 0.149 s
% 3.30/0.84  % (27321)------------------------------
% 3.30/0.84  % (27321)------------------------------
% 3.30/0.86  % (27320)Refutation found. Thanks to Tanya!
% 3.30/0.86  % SZS status Theorem for theBenchmark
% 3.30/0.86  % SZS output start Proof for theBenchmark
% 3.30/0.86  fof(f483,plain,(
% 3.30/0.86    $false),
% 3.30/0.86    inference(resolution,[],[f260,f35])).
% 3.30/0.86  fof(f35,plain,(
% 3.30/0.86    ~r2_hidden(sK0,sK2)),
% 3.30/0.86    inference(cnf_transformation,[],[f29])).
% 3.30/0.86  fof(f29,plain,(
% 3.30/0.86    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.30/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 3.30/0.86  fof(f28,plain,(
% 3.30/0.86    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.30/0.86    introduced(choice_axiom,[])).
% 3.30/0.86  fof(f27,plain,(
% 3.30/0.86    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.30/0.86    inference(ennf_transformation,[],[f25])).
% 3.30/0.86  fof(f25,negated_conjecture,(
% 3.30/0.86    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.30/0.86    inference(negated_conjecture,[],[f24])).
% 3.30/0.86  fof(f24,conjecture,(
% 3.30/0.86    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 3.30/0.86  fof(f260,plain,(
% 3.30/0.86    r2_hidden(sK0,sK2)),
% 3.30/0.86    inference(superposition,[],[f168,f226])).
% 3.30/0.86  fof(f226,plain,(
% 3.30/0.86    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1)))),
% 3.30/0.86    inference(resolution,[],[f166,f71])).
% 3.30/0.86  fof(f71,plain,(
% 3.30/0.86    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = X1) )),
% 3.30/0.86    inference(resolution,[],[f41,f63])).
% 3.30/0.86  fof(f63,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.30/0.86    inference(definition_unfolding,[],[f43,f53])).
% 3.30/0.86  fof(f53,plain,(
% 3.30/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.30/0.86    inference(definition_unfolding,[],[f51,f50])).
% 3.30/0.86  fof(f50,plain,(
% 3.30/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f16])).
% 3.30/0.86  fof(f16,axiom,(
% 3.30/0.86    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.30/0.86  fof(f51,plain,(
% 3.30/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.30/0.86    inference(cnf_transformation,[],[f22])).
% 3.30/0.86  fof(f22,axiom,(
% 3.30/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.30/0.86  fof(f43,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.30/0.86    inference(cnf_transformation,[],[f6])).
% 3.30/0.86  fof(f6,axiom,(
% 3.30/0.86    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.30/0.86  fof(f41,plain,(
% 3.30/0.86    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f33])).
% 3.30/0.86  fof(f33,plain,(
% 3.30/0.86    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/0.86    inference(flattening,[],[f32])).
% 3.30/0.86  fof(f32,plain,(
% 3.30/0.86    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/0.86    inference(nnf_transformation,[],[f4])).
% 3.30/0.86  fof(f4,axiom,(
% 3.30/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.30/0.86  fof(f166,plain,(
% 3.30/0.86    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2)),
% 3.30/0.86    inference(superposition,[],[f58,f132])).
% 3.30/0.86  fof(f132,plain,(
% 3.30/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.30/0.86    inference(resolution,[],[f129,f73])).
% 3.30/0.86  fof(f73,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 3.30/0.86    inference(resolution,[],[f60,f67])).
% 3.30/0.86  fof(f67,plain,(
% 3.30/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.30/0.86    inference(equality_resolution,[],[f40])).
% 3.30/0.86  fof(f40,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.30/0.86    inference(cnf_transformation,[],[f33])).
% 3.30/0.86  fof(f60,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 3.30/0.86    inference(definition_unfolding,[],[f37,f50])).
% 3.30/0.86  fof(f37,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f31])).
% 3.30/0.86  fof(f31,plain,(
% 3.30/0.86    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.30/0.86    inference(flattening,[],[f30])).
% 3.30/0.86  fof(f30,plain,(
% 3.30/0.86    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.30/0.86    inference(nnf_transformation,[],[f23])).
% 3.30/0.86  fof(f23,axiom,(
% 3.30/0.86    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.30/0.86  fof(f129,plain,(
% 3.30/0.86    ( ! [X2,X1] : (~r2_hidden(X1,k1_enumset1(X2,X2,X1)) | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1)) )),
% 3.30/0.86    inference(resolution,[],[f122,f75])).
% 3.30/0.86  fof(f75,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 3.30/0.86    inference(resolution,[],[f61,f67])).
% 3.30/0.86  fof(f61,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 3.30/0.86    inference(definition_unfolding,[],[f36,f50])).
% 3.30/0.86  fof(f36,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f31])).
% 3.30/0.86  fof(f122,plain,(
% 3.30/0.86    ( ! [X0,X1] : (~r2_hidden(X1,k1_enumset1(X1,X1,X0)) | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) | ~r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 3.30/0.86    inference(resolution,[],[f117,f73])).
% 3.30/0.86  fof(f117,plain,(
% 3.30/0.86    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_enumset1(X3,X3,X4)) | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3) | ~r2_hidden(X4,k1_enumset1(X5,X5,X3)) | ~r2_hidden(X3,k1_enumset1(X5,X5,X3))) )),
% 3.30/0.86    inference(resolution,[],[f102,f75])).
% 3.30/0.86  fof(f102,plain,(
% 3.30/0.86    ( ! [X10,X8,X7,X9] : (~r2_hidden(X10,k1_enumset1(X8,X8,X9)) | k1_enumset1(X8,X8,X9) = k1_enumset1(X7,X7,X10) | ~r2_hidden(X7,k1_enumset1(X8,X8,X9)) | ~r2_hidden(X9,k1_enumset1(X7,X7,X10)) | ~r2_hidden(X8,k1_enumset1(X7,X7,X10))) )),
% 3.30/0.86    inference(resolution,[],[f81,f59])).
% 3.30/0.86  fof(f59,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.30/0.86    inference(definition_unfolding,[],[f38,f50])).
% 3.30/0.86  fof(f38,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f31])).
% 3.30/0.86  fof(f81,plain,(
% 3.30/0.86    ( ! [X6,X8,X7] : (~r1_tarski(X7,k1_enumset1(X8,X8,X6)) | ~r2_hidden(X8,X7) | k1_enumset1(X8,X8,X6) = X7 | ~r2_hidden(X6,X7)) )),
% 3.30/0.86    inference(resolution,[],[f59,f41])).
% 3.30/0.86  fof(f58,plain,(
% 3.30/0.86    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 3.30/0.86    inference(definition_unfolding,[],[f34,f53,f50])).
% 3.30/0.86  fof(f34,plain,(
% 3.30/0.86    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.30/0.86    inference(cnf_transformation,[],[f29])).
% 3.30/0.86  fof(f168,plain,(
% 3.30/0.86    ( ! [X255,X253,X254] : (r2_hidden(X253,k3_tarski(k1_enumset1(X255,X255,k1_enumset1(X253,X253,X254))))) )),
% 3.30/0.86    inference(superposition,[],[f76,f132])).
% 3.30/0.86  fof(f76,plain,(
% 3.30/0.86    ( ! [X4,X2,X3] : (r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4)))) )),
% 3.30/0.86    inference(resolution,[],[f61,f63])).
% 3.30/0.86  % SZS output end Proof for theBenchmark
% 3.30/0.86  % (27320)------------------------------
% 3.30/0.86  % (27320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.30/0.86  % (27320)Termination reason: Refutation
% 3.30/0.86  
% 3.30/0.86  % (27320)Memory used [KB]: 2174
% 3.30/0.86  % (27320)Time elapsed: 0.172 s
% 3.30/0.86  % (27320)------------------------------
% 3.30/0.86  % (27320)------------------------------
% 3.30/0.86  % (27241)Success in time 0.502 s
%------------------------------------------------------------------------------
