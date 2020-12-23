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
% DateTime   : Thu Dec  3 12:38:57 EST 2020

% Result     : Theorem 3.49s
% Output     : Refutation 3.49s
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
fof(f708,plain,(
    $false ),
    inference(resolution,[],[f563,f37])).

fof(f37,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f563,plain,(
    r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f184,f244])).

fof(f244,plain,(
    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) ),
    inference(resolution,[],[f182,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f43,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2) ),
    inference(superposition,[],[f61,f146])).

fof(f146,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(resolution,[],[f141,f78])).

fof(f78,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X2,X1))
      | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ) ),
    inference(resolution,[],[f136,f80])).

fof(f80,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f64,f71])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X1,X1,X0))
      | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
      | ~ r2_hidden(X0,k1_enumset1(X1,X1,X0)) ) ),
    inference(resolution,[],[f130,f78])).

fof(f130,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_enumset1(X3,X3,X4))
      | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3)
      | ~ r2_hidden(X4,k1_enumset1(X5,X5,X3))
      | ~ r2_hidden(X3,k1_enumset1(X5,X5,X3)) ) ),
    inference(resolution,[],[f112,f80])).

fof(f112,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r2_hidden(X12,k1_enumset1(X10,X10,X11))
      | k1_enumset1(X10,X10,X11) = k1_enumset1(X9,X9,X12)
      | ~ r2_hidden(X9,k1_enumset1(X10,X10,X11))
      | ~ r2_hidden(X11,k1_enumset1(X9,X9,X12))
      | ~ r2_hidden(X10,k1_enumset1(X9,X9,X12)) ) ),
    inference(resolution,[],[f87,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,k1_enumset1(X8,X8,X6))
      | ~ r2_hidden(X8,X7)
      | k1_enumset1(X8,X8,X6) = X7
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f62,f43])).

fof(f61,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f36,f56,f53])).

fof(f36,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f184,plain,(
    ! [X257,X256,X258] : r2_hidden(X256,k3_tarski(k1_enumset1(X258,X258,k1_enumset1(X256,X256,X257)))) ),
    inference(superposition,[],[f81,f146])).

fof(f81,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4))) ),
    inference(resolution,[],[f64,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (6446)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (6436)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (6443)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (6454)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (6455)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.56  % (6443)Refutation not found, incomplete strategy% (6443)------------------------------
% 0.20/0.56  % (6443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6433)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (6459)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (6443)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6443)Memory used [KB]: 10874
% 0.20/0.56  % (6443)Time elapsed: 0.153 s
% 0.20/0.56  % (6443)------------------------------
% 0.20/0.56  % (6443)------------------------------
% 0.20/0.56  % (6459)Refutation not found, incomplete strategy% (6459)------------------------------
% 0.20/0.56  % (6459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6459)Memory used [KB]: 6268
% 0.20/0.56  % (6459)Time elapsed: 0.147 s
% 0.20/0.56  % (6459)------------------------------
% 0.20/0.56  % (6459)------------------------------
% 0.20/0.56  % (6438)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.57  % (6441)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (6456)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.64/0.57  % (6447)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.64/0.57  % (6447)Refutation not found, incomplete strategy% (6447)------------------------------
% 1.64/0.57  % (6447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (6447)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (6447)Memory used [KB]: 1663
% 1.64/0.57  % (6447)Time elapsed: 0.101 s
% 1.64/0.57  % (6447)------------------------------
% 1.64/0.57  % (6447)------------------------------
% 1.64/0.57  % (6434)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.64/0.57  % (6448)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.64/0.58  % (6462)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.64/0.58  % (6462)Refutation not found, incomplete strategy% (6462)------------------------------
% 1.64/0.58  % (6462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (6462)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (6462)Memory used [KB]: 1663
% 1.64/0.58  % (6462)Time elapsed: 0.168 s
% 1.64/0.58  % (6462)------------------------------
% 1.64/0.58  % (6462)------------------------------
% 1.64/0.58  % (6449)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.64/0.58  % (6440)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.64/0.58  % (6434)Refutation not found, incomplete strategy% (6434)------------------------------
% 1.64/0.58  % (6434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (6434)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (6434)Memory used [KB]: 1663
% 1.64/0.58  % (6434)Time elapsed: 0.159 s
% 1.64/0.58  % (6434)------------------------------
% 1.64/0.58  % (6434)------------------------------
% 1.64/0.58  % (6451)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.64/0.59  % (6451)Refutation not found, incomplete strategy% (6451)------------------------------
% 1.64/0.59  % (6451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (6451)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (6451)Memory used [KB]: 1791
% 1.64/0.59  % (6451)Time elapsed: 0.162 s
% 1.64/0.59  % (6451)------------------------------
% 1.64/0.59  % (6451)------------------------------
% 1.83/0.59  % (6439)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.83/0.59  % (6435)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.83/0.59  % (6449)Refutation not found, incomplete strategy% (6449)------------------------------
% 1.83/0.59  % (6449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.59  % (6442)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.83/0.59  % (6449)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.59  
% 1.83/0.59  % (6449)Memory used [KB]: 10618
% 1.83/0.59  % (6449)Time elapsed: 0.173 s
% 1.83/0.59  % (6449)------------------------------
% 1.83/0.59  % (6449)------------------------------
% 1.83/0.59  % (6437)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.83/0.60  % (6461)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.83/0.60  % (6445)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.83/0.61  % (6453)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.83/0.61  % (6458)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.83/0.61  % (6450)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.83/0.61  % (6444)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.83/0.61  % (6445)Refutation not found, incomplete strategy% (6445)------------------------------
% 1.83/0.61  % (6445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (6460)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.83/0.62  % (6445)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (6445)Memory used [KB]: 10618
% 1.83/0.62  % (6445)Time elapsed: 0.191 s
% 1.83/0.62  % (6445)------------------------------
% 1.83/0.62  % (6445)------------------------------
% 1.83/0.62  % (6460)Refutation not found, incomplete strategy% (6460)------------------------------
% 1.83/0.62  % (6460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (6460)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (6460)Memory used [KB]: 6268
% 1.83/0.62  % (6460)Time elapsed: 0.198 s
% 1.83/0.62  % (6460)------------------------------
% 1.83/0.62  % (6460)------------------------------
% 1.83/0.62  % (6461)Refutation not found, incomplete strategy% (6461)------------------------------
% 1.83/0.62  % (6461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (6461)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (6461)Memory used [KB]: 10874
% 1.83/0.62  % (6461)Time elapsed: 0.202 s
% 1.83/0.62  % (6461)------------------------------
% 1.83/0.62  % (6461)------------------------------
% 2.07/0.63  % (6457)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.07/0.63  % (6452)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.07/0.63  % (6457)Refutation not found, incomplete strategy% (6457)------------------------------
% 2.07/0.63  % (6457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (6457)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (6457)Memory used [KB]: 10746
% 2.07/0.63  % (6457)Time elapsed: 0.212 s
% 2.07/0.63  % (6457)------------------------------
% 2.07/0.63  % (6457)------------------------------
% 2.07/0.63  % (6444)Refutation not found, incomplete strategy% (6444)------------------------------
% 2.07/0.63  % (6444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (6450)Refutation not found, incomplete strategy% (6450)------------------------------
% 2.07/0.63  % (6450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (6450)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (6450)Memory used [KB]: 1918
% 2.07/0.63  % (6450)Time elapsed: 0.194 s
% 2.07/0.63  % (6450)------------------------------
% 2.07/0.63  % (6450)------------------------------
% 2.07/0.63  % (6444)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (6444)Memory used [KB]: 6396
% 2.07/0.63  % (6444)Time elapsed: 0.193 s
% 2.07/0.63  % (6444)------------------------------
% 2.07/0.63  % (6444)------------------------------
% 2.07/0.63  % (6458)Refutation not found, incomplete strategy% (6458)------------------------------
% 2.07/0.63  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (6458)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (6458)Memory used [KB]: 6268
% 2.07/0.63  % (6458)Time elapsed: 0.208 s
% 2.07/0.63  % (6458)------------------------------
% 2.07/0.63  % (6458)------------------------------
% 2.13/0.69  % (6436)Refutation not found, incomplete strategy% (6436)------------------------------
% 2.13/0.69  % (6436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.69  % (6436)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.69  
% 2.13/0.69  % (6436)Memory used [KB]: 6140
% 2.13/0.69  % (6436)Time elapsed: 0.248 s
% 2.13/0.69  % (6436)------------------------------
% 2.13/0.69  % (6436)------------------------------
% 2.13/0.69  % (6490)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.13/0.70  % (6489)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.50/0.74  % (6491)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.50/0.74  % (6494)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.50/0.74  % (6491)Refutation not found, incomplete strategy% (6491)------------------------------
% 2.50/0.74  % (6491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.74  % (6491)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.74  
% 2.50/0.74  % (6491)Memory used [KB]: 6268
% 2.50/0.74  % (6491)Time elapsed: 0.144 s
% 2.50/0.74  % (6491)------------------------------
% 2.50/0.74  % (6491)------------------------------
% 2.50/0.75  % (6435)Refutation not found, incomplete strategy% (6435)------------------------------
% 2.50/0.75  % (6435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.75  % (6500)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.50/0.75  % (6494)Refutation not found, incomplete strategy% (6494)------------------------------
% 2.50/0.75  % (6494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.76  % (6494)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.76  
% 2.50/0.76  % (6494)Memory used [KB]: 1918
% 2.50/0.76  % (6494)Time elapsed: 0.129 s
% 2.50/0.76  % (6494)------------------------------
% 2.50/0.76  % (6494)------------------------------
% 2.50/0.76  % (6435)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.76  
% 2.50/0.76  % (6435)Memory used [KB]: 6396
% 2.50/0.76  % (6435)Time elapsed: 0.329 s
% 2.50/0.76  % (6435)------------------------------
% 2.50/0.76  % (6435)------------------------------
% 2.83/0.77  % (6500)Refutation not found, incomplete strategy% (6500)------------------------------
% 2.83/0.77  % (6500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.77  % (6500)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.77  
% 2.83/0.77  % (6500)Memory used [KB]: 10746
% 2.83/0.77  % (6500)Time elapsed: 0.109 s
% 2.83/0.77  % (6500)------------------------------
% 2.83/0.77  % (6500)------------------------------
% 2.83/0.78  % (6496)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.83/0.79  % (6441)Refutation not found, incomplete strategy% (6441)------------------------------
% 2.83/0.79  % (6441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.79  % (6441)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.79  
% 2.83/0.79  % (6441)Memory used [KB]: 6268
% 2.83/0.79  % (6441)Time elapsed: 0.372 s
% 2.83/0.79  % (6441)------------------------------
% 2.83/0.79  % (6441)------------------------------
% 2.83/0.79  % (6498)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.83/0.79  % (6498)Refutation not found, incomplete strategy% (6498)------------------------------
% 2.83/0.79  % (6498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.79  % (6498)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.79  
% 2.83/0.79  % (6498)Memory used [KB]: 10746
% 2.83/0.79  % (6498)Time elapsed: 0.140 s
% 2.83/0.79  % (6498)------------------------------
% 2.83/0.79  % (6498)------------------------------
% 2.83/0.80  % (6497)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.83/0.80  % (6492)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.83/0.80  % (6495)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.83/0.80  % (6433)Refutation not found, incomplete strategy% (6433)------------------------------
% 2.83/0.80  % (6433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.80  % (6493)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.83/0.80  % (6499)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.83/0.80  % (6493)Refutation not found, incomplete strategy% (6493)------------------------------
% 2.83/0.80  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.80  % (6493)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.80  
% 2.83/0.80  % (6493)Memory used [KB]: 10874
% 2.83/0.80  % (6493)Time elapsed: 0.163 s
% 2.83/0.80  % (6493)------------------------------
% 2.83/0.80  % (6493)------------------------------
% 2.83/0.81  % (6501)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.83/0.81  % (6495)Refutation not found, incomplete strategy% (6495)------------------------------
% 2.83/0.81  % (6495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.81  % (6495)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.81  
% 2.83/0.81  % (6495)Memory used [KB]: 10618
% 2.83/0.81  % (6495)Time elapsed: 0.168 s
% 2.83/0.81  % (6495)------------------------------
% 2.83/0.81  % (6495)------------------------------
% 2.83/0.81  % (6448)Refutation not found, incomplete strategy% (6448)------------------------------
% 2.83/0.81  % (6448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.81  % (6448)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.81  
% 2.83/0.81  % (6448)Memory used [KB]: 6140
% 2.83/0.81  % (6448)Time elapsed: 0.386 s
% 2.83/0.81  % (6448)------------------------------
% 2.83/0.81  % (6448)------------------------------
% 2.83/0.81  % (6433)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.81  
% 2.83/0.81  % (6433)Memory used [KB]: 1791
% 2.83/0.81  % (6433)Time elapsed: 0.370 s
% 2.83/0.81  % (6433)------------------------------
% 2.83/0.81  % (6433)------------------------------
% 2.83/0.82  % (6502)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.83/0.82  % (6492)Refutation not found, incomplete strategy% (6492)------------------------------
% 2.83/0.82  % (6492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.82  % (6492)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.82  
% 2.83/0.82  % (6492)Memory used [KB]: 10618
% 2.83/0.82  % (6492)Time elapsed: 0.199 s
% 2.83/0.82  % (6492)------------------------------
% 2.83/0.82  % (6492)------------------------------
% 2.83/0.82  % (6502)Refutation not found, incomplete strategy% (6502)------------------------------
% 2.83/0.82  % (6502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.82  % (6502)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.82  
% 2.83/0.82  % (6502)Memory used [KB]: 10746
% 2.83/0.82  % (6502)Time elapsed: 0.143 s
% 2.83/0.82  % (6502)------------------------------
% 2.83/0.82  % (6502)------------------------------
% 2.83/0.82  % (6503)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.49/0.86  % (6509)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.49/0.86  % (6507)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.49/0.88  % (6510)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.49/0.88  % (6501)Refutation found. Thanks to Tanya!
% 3.49/0.88  % SZS status Theorem for theBenchmark
% 3.49/0.88  % SZS output start Proof for theBenchmark
% 3.49/0.88  fof(f708,plain,(
% 3.49/0.88    $false),
% 3.49/0.88    inference(resolution,[],[f563,f37])).
% 3.49/0.88  fof(f37,plain,(
% 3.49/0.88    ~r2_hidden(sK0,sK2)),
% 3.49/0.88    inference(cnf_transformation,[],[f31])).
% 3.49/0.88  fof(f31,plain,(
% 3.49/0.88    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.49/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 3.49/0.88  fof(f30,plain,(
% 3.49/0.88    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.49/0.88    introduced(choice_axiom,[])).
% 3.49/0.88  fof(f29,plain,(
% 3.49/0.88    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.49/0.88    inference(ennf_transformation,[],[f27])).
% 3.49/0.88  fof(f27,negated_conjecture,(
% 3.49/0.88    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.49/0.88    inference(negated_conjecture,[],[f26])).
% 3.49/0.88  fof(f26,conjecture,(
% 3.49/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 3.49/0.88  fof(f563,plain,(
% 3.49/0.88    r2_hidden(sK0,sK2)),
% 3.49/0.88    inference(superposition,[],[f184,f244])).
% 3.49/0.88  fof(f244,plain,(
% 3.49/0.88    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1)))),
% 3.49/0.88    inference(resolution,[],[f182,f76])).
% 3.49/0.88  fof(f76,plain,(
% 3.49/0.88    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = X1) )),
% 3.49/0.88    inference(resolution,[],[f43,f66])).
% 3.49/0.88  fof(f66,plain,(
% 3.49/0.88    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.49/0.88    inference(definition_unfolding,[],[f45,f56])).
% 3.49/0.88  fof(f56,plain,(
% 3.49/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.49/0.88    inference(definition_unfolding,[],[f54,f53])).
% 3.49/0.88  fof(f53,plain,(
% 3.49/0.88    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.49/0.88    inference(cnf_transformation,[],[f18])).
% 3.49/0.88  fof(f18,axiom,(
% 3.49/0.88    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.49/0.88  fof(f54,plain,(
% 3.49/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.49/0.88    inference(cnf_transformation,[],[f24])).
% 3.49/0.88  fof(f24,axiom,(
% 3.49/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.49/0.88  fof(f45,plain,(
% 3.49/0.88    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.49/0.88    inference(cnf_transformation,[],[f9])).
% 3.49/0.88  fof(f9,axiom,(
% 3.49/0.88    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.49/0.88  fof(f43,plain,(
% 3.49/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.49/0.88    inference(cnf_transformation,[],[f35])).
% 3.49/0.88  fof(f35,plain,(
% 3.49/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.88    inference(flattening,[],[f34])).
% 3.49/0.88  fof(f34,plain,(
% 3.49/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.88    inference(nnf_transformation,[],[f4])).
% 3.49/0.88  fof(f4,axiom,(
% 3.49/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.49/0.88  fof(f182,plain,(
% 3.49/0.88    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2)),
% 3.49/0.88    inference(superposition,[],[f61,f146])).
% 3.49/0.88  fof(f146,plain,(
% 3.49/0.88    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.49/0.88    inference(resolution,[],[f141,f78])).
% 3.49/0.88  fof(f78,plain,(
% 3.49/0.88    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 3.49/0.88    inference(resolution,[],[f63,f71])).
% 3.49/0.88  fof(f71,plain,(
% 3.49/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.49/0.88    inference(equality_resolution,[],[f42])).
% 3.49/0.88  fof(f42,plain,(
% 3.49/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.49/0.88    inference(cnf_transformation,[],[f35])).
% 3.49/0.88  fof(f63,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 3.49/0.88    inference(definition_unfolding,[],[f39,f53])).
% 3.49/0.88  fof(f39,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.49/0.88    inference(cnf_transformation,[],[f33])).
% 3.49/0.88  fof(f33,plain,(
% 3.49/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.49/0.88    inference(flattening,[],[f32])).
% 3.49/0.88  fof(f32,plain,(
% 3.49/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.49/0.88    inference(nnf_transformation,[],[f25])).
% 3.49/0.88  fof(f25,axiom,(
% 3.49/0.88    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.49/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.49/0.88  fof(f141,plain,(
% 3.49/0.88    ( ! [X2,X1] : (~r2_hidden(X1,k1_enumset1(X2,X2,X1)) | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1)) )),
% 3.49/0.88    inference(resolution,[],[f136,f80])).
% 3.49/0.88  fof(f80,plain,(
% 3.49/0.88    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 3.49/0.88    inference(resolution,[],[f64,f71])).
% 3.49/0.88  fof(f64,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 3.49/0.88    inference(definition_unfolding,[],[f38,f53])).
% 3.49/0.88  fof(f38,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.49/0.88    inference(cnf_transformation,[],[f33])).
% 3.49/0.88  fof(f136,plain,(
% 3.49/0.88    ( ! [X0,X1] : (~r2_hidden(X1,k1_enumset1(X1,X1,X0)) | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) | ~r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 3.49/0.88    inference(resolution,[],[f130,f78])).
% 3.49/0.88  fof(f130,plain,(
% 3.49/0.88    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_enumset1(X3,X3,X4)) | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3) | ~r2_hidden(X4,k1_enumset1(X5,X5,X3)) | ~r2_hidden(X3,k1_enumset1(X5,X5,X3))) )),
% 3.49/0.88    inference(resolution,[],[f112,f80])).
% 3.49/0.88  fof(f112,plain,(
% 3.49/0.88    ( ! [X12,X10,X11,X9] : (~r2_hidden(X12,k1_enumset1(X10,X10,X11)) | k1_enumset1(X10,X10,X11) = k1_enumset1(X9,X9,X12) | ~r2_hidden(X9,k1_enumset1(X10,X10,X11)) | ~r2_hidden(X11,k1_enumset1(X9,X9,X12)) | ~r2_hidden(X10,k1_enumset1(X9,X9,X12))) )),
% 3.49/0.88    inference(resolution,[],[f87,f62])).
% 3.49/0.88  fof(f62,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.49/0.88    inference(definition_unfolding,[],[f40,f53])).
% 3.49/0.88  fof(f40,plain,(
% 3.49/0.88    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.49/0.88    inference(cnf_transformation,[],[f33])).
% 3.49/0.88  fof(f87,plain,(
% 3.49/0.88    ( ! [X6,X8,X7] : (~r1_tarski(X7,k1_enumset1(X8,X8,X6)) | ~r2_hidden(X8,X7) | k1_enumset1(X8,X8,X6) = X7 | ~r2_hidden(X6,X7)) )),
% 3.49/0.88    inference(resolution,[],[f62,f43])).
% 3.49/0.88  fof(f61,plain,(
% 3.49/0.88    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 3.49/0.88    inference(definition_unfolding,[],[f36,f56,f53])).
% 3.49/0.88  fof(f36,plain,(
% 3.49/0.88    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.49/0.88    inference(cnf_transformation,[],[f31])).
% 3.49/0.88  fof(f184,plain,(
% 3.49/0.88    ( ! [X257,X256,X258] : (r2_hidden(X256,k3_tarski(k1_enumset1(X258,X258,k1_enumset1(X256,X256,X257))))) )),
% 3.49/0.88    inference(superposition,[],[f81,f146])).
% 3.49/0.88  fof(f81,plain,(
% 3.49/0.88    ( ! [X4,X2,X3] : (r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4)))) )),
% 3.49/0.88    inference(resolution,[],[f64,f66])).
% 3.49/0.88  % SZS output end Proof for theBenchmark
% 3.49/0.88  % (6501)------------------------------
% 3.49/0.88  % (6501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.88  % (6501)Termination reason: Refutation
% 3.49/0.88  
% 3.49/0.88  % (6501)Memory used [KB]: 2302
% 3.49/0.88  % (6501)Time elapsed: 0.226 s
% 3.49/0.88  % (6501)------------------------------
% 3.49/0.88  % (6501)------------------------------
% 3.49/0.89  % (6432)Success in time 0.535 s
%------------------------------------------------------------------------------
