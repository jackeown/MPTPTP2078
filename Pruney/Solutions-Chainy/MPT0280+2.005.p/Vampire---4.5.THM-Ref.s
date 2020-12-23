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
% DateTime   : Thu Dec  3 12:41:35 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 112 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f303,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f303,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f291,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f291,plain,(
    ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f289,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f289,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f271,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f271,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f269,f41])).

fof(f269,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f217,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(subsumption_resolution,[],[f132,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(k3_xboole_0(X4,X3),X5),X3) ),
    inference(superposition,[],[f66,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f66,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(k3_xboole_0(X2,X3),X4),X2) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f217,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f133,f32])).

fof(f32,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_xboole_0(X3,X4),X5)
      | ~ r1_tarski(k4_xboole_0(X4,X3),X5)
      | ~ r1_tarski(X3,X5) ) ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.59/0.58  % (30077)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.58  % (30075)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.59  % (30085)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.59  % (30076)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.59/0.59  % (30086)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.59  % (30094)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.60  % (30084)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.60  % (30092)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.59/0.60  % (30086)Refutation not found, incomplete strategy% (30086)------------------------------
% 1.59/0.60  % (30086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (30086)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (30086)Memory used [KB]: 10618
% 1.59/0.60  % (30086)Time elapsed: 0.166 s
% 1.59/0.60  % (30086)------------------------------
% 1.59/0.60  % (30086)------------------------------
% 1.59/0.61  % (30084)Refutation not found, incomplete strategy% (30084)------------------------------
% 1.59/0.61  % (30084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (30084)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (30084)Memory used [KB]: 1663
% 1.59/0.61  % (30084)Time elapsed: 0.164 s
% 1.59/0.61  % (30084)------------------------------
% 1.59/0.61  % (30084)------------------------------
% 1.59/0.61  % (30093)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.63  % (30070)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.59/0.63  % (30070)Refutation not found, incomplete strategy% (30070)------------------------------
% 1.59/0.63  % (30070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  % (30070)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.63  
% 1.59/0.63  % (30070)Memory used [KB]: 1663
% 1.59/0.63  % (30070)Time elapsed: 0.186 s
% 1.59/0.63  % (30070)------------------------------
% 1.59/0.63  % (30070)------------------------------
% 1.59/0.63  % (30080)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.59/0.64  % (30095)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.64  % (30097)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.64  % (30072)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.64  % (30078)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.13/0.65  % (30087)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.13/0.65  % (30088)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.13/0.65  % (30089)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.13/0.65  % (30087)Refutation not found, incomplete strategy% (30087)------------------------------
% 2.13/0.65  % (30087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (30087)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.65  
% 2.13/0.65  % (30087)Memory used [KB]: 1663
% 2.13/0.65  % (30087)Time elapsed: 0.208 s
% 2.13/0.65  % (30087)------------------------------
% 2.13/0.65  % (30087)------------------------------
% 2.13/0.65  % (30071)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.13/0.65  % (30098)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.13/0.66  % (30098)Refutation not found, incomplete strategy% (30098)------------------------------
% 2.13/0.66  % (30098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (30098)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (30098)Memory used [KB]: 10746
% 2.13/0.66  % (30098)Time elapsed: 0.220 s
% 2.13/0.66  % (30098)------------------------------
% 2.13/0.66  % (30098)------------------------------
% 2.13/0.66  % (30096)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.13/0.66  % (30073)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 2.13/0.66  % (30096)Refutation not found, incomplete strategy% (30096)------------------------------
% 2.13/0.66  % (30096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (30096)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (30096)Memory used [KB]: 6140
% 2.13/0.66  % (30096)Time elapsed: 0.226 s
% 2.13/0.66  % (30096)------------------------------
% 2.13/0.66  % (30096)------------------------------
% 2.13/0.66  % (30079)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.13/0.66  % (30079)Refutation not found, incomplete strategy% (30079)------------------------------
% 2.13/0.66  % (30079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (30079)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (30079)Memory used [KB]: 10746
% 2.13/0.66  % (30079)Time elapsed: 0.229 s
% 2.13/0.66  % (30079)------------------------------
% 2.13/0.66  % (30079)------------------------------
% 2.13/0.67  % (30081)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.38/0.68  % (30090)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.38/0.68  % (30081)Refutation not found, incomplete strategy% (30081)------------------------------
% 2.38/0.68  % (30081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.68  % (30081)Termination reason: Refutation not found, incomplete strategy
% 2.38/0.68  
% 2.38/0.68  % (30081)Memory used [KB]: 10618
% 2.38/0.68  % (30081)Time elapsed: 0.238 s
% 2.38/0.68  % (30081)------------------------------
% 2.38/0.68  % (30081)------------------------------
% 2.38/0.70  % (30078)Refutation found. Thanks to Tanya!
% 2.38/0.70  % SZS status Theorem for theBenchmark
% 2.38/0.70  % SZS output start Proof for theBenchmark
% 2.38/0.70  fof(f305,plain,(
% 2.38/0.70    $false),
% 2.38/0.70    inference(subsumption_resolution,[],[f303,f53])).
% 2.38/0.70  fof(f53,plain,(
% 2.38/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.38/0.70    inference(equality_resolution,[],[f43])).
% 2.38/0.70  fof(f43,plain,(
% 2.38/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.38/0.70    inference(cnf_transformation,[],[f31])).
% 2.38/0.70  fof(f31,plain,(
% 2.38/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.70    inference(flattening,[],[f30])).
% 2.38/0.70  fof(f30,plain,(
% 2.38/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.70    inference(nnf_transformation,[],[f2])).
% 2.38/0.70  fof(f2,axiom,(
% 2.38/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.38/0.70  fof(f303,plain,(
% 2.38/0.70    ~r1_tarski(sK1,sK1)),
% 2.38/0.70    inference(resolution,[],[f291,f46])).
% 2.38/0.70  fof(f46,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f24])).
% 2.38/0.70  fof(f24,plain,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.38/0.70    inference(ennf_transformation,[],[f4])).
% 2.38/0.70  fof(f4,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.38/0.70  fof(f291,plain,(
% 2.38/0.70    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1))),
% 2.38/0.70    inference(subsumption_resolution,[],[f289,f33])).
% 2.38/0.70  fof(f33,plain,(
% 2.38/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f9])).
% 2.38/0.70  fof(f9,axiom,(
% 2.38/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.38/0.70  fof(f289,plain,(
% 2.38/0.70    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | ~r1_tarski(sK0,k2_xboole_0(sK0,sK1))),
% 2.38/0.70    inference(resolution,[],[f271,f41])).
% 2.38/0.70  fof(f41,plain,(
% 2.38/0.70    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f23])).
% 2.38/0.70  fof(f23,plain,(
% 2.38/0.70    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.38/0.70    inference(ennf_transformation,[],[f18])).
% 2.38/0.70  fof(f18,axiom,(
% 2.38/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 2.38/0.70  fof(f271,plain,(
% 2.38/0.70    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~r1_tarski(sK1,k2_xboole_0(sK0,sK1))),
% 2.38/0.70    inference(resolution,[],[f269,f41])).
% 2.38/0.70  fof(f269,plain,(
% 2.38/0.70    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 2.38/0.70    inference(resolution,[],[f217,f134])).
% 2.38/0.70  fof(f134,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,X2)) )),
% 2.38/0.70    inference(subsumption_resolution,[],[f132,f89])).
% 2.38/0.70  fof(f89,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(superposition,[],[f73,f40])).
% 2.38/0.70  fof(f40,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f22])).
% 2.38/0.70  fof(f22,plain,(
% 2.38/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.38/0.70    inference(ennf_transformation,[],[f8])).
% 2.38/0.70  fof(f8,axiom,(
% 2.38/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.38/0.70  fof(f73,plain,(
% 2.38/0.70    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(k3_xboole_0(X4,X3),X5),X3)) )),
% 2.38/0.70    inference(superposition,[],[f66,f35])).
% 2.38/0.70  fof(f35,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f1])).
% 2.38/0.70  fof(f1,axiom,(
% 2.38/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.38/0.70  fof(f66,plain,(
% 2.38/0.70    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(k3_xboole_0(X2,X3),X4),X2)) )),
% 2.38/0.70    inference(resolution,[],[f47,f34])).
% 2.38/0.70  fof(f34,plain,(
% 2.38/0.70    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f6])).
% 2.38/0.70  fof(f6,axiom,(
% 2.38/0.70    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.38/0.70  fof(f47,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f25])).
% 2.38/0.70  fof(f25,plain,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.38/0.70    inference(ennf_transformation,[],[f7])).
% 2.38/0.70  fof(f7,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.38/0.70  fof(f132,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_tarski(X0,X2)) )),
% 2.38/0.70    inference(superposition,[],[f48,f38])).
% 2.38/0.70  fof(f38,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f3])).
% 2.38/0.70  fof(f3,axiom,(
% 2.38/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.38/0.70  fof(f48,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f27])).
% 2.38/0.70  fof(f27,plain,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.38/0.70    inference(flattening,[],[f26])).
% 2.38/0.70  fof(f26,plain,(
% 2.38/0.70    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.38/0.70    inference(ennf_transformation,[],[f5])).
% 2.38/0.70  fof(f5,axiom,(
% 2.38/0.70    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 2.38/0.70  fof(f217,plain,(
% 2.38/0.70    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 2.38/0.70    inference(resolution,[],[f133,f32])).
% 2.38/0.70  fof(f32,plain,(
% 2.38/0.70    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 2.38/0.70    inference(cnf_transformation,[],[f29])).
% 2.38/0.70  fof(f29,plain,(
% 2.38/0.70    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 2.38/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f28])).
% 2.38/0.70  fof(f28,plain,(
% 2.38/0.70    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 2.38/0.70    introduced(choice_axiom,[])).
% 2.38/0.70  fof(f21,plain,(
% 2.38/0.70    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 2.38/0.70    inference(ennf_transformation,[],[f20])).
% 2.38/0.70  fof(f20,negated_conjecture,(
% 2.38/0.70    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 2.38/0.70    inference(negated_conjecture,[],[f19])).
% 2.38/0.70  fof(f19,conjecture,(
% 2.38/0.70    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 2.38/0.70  fof(f133,plain,(
% 2.38/0.70    ( ! [X4,X5,X3] : (r1_tarski(k2_xboole_0(X3,X4),X5) | ~r1_tarski(k4_xboole_0(X4,X3),X5) | ~r1_tarski(X3,X5)) )),
% 2.38/0.70    inference(superposition,[],[f48,f39])).
% 2.38/0.70  fof(f39,plain,(
% 2.38/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.38/0.70    inference(cnf_transformation,[],[f10])).
% 2.38/0.70  fof(f10,axiom,(
% 2.38/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.38/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.38/0.70  % SZS output end Proof for theBenchmark
% 2.38/0.70  % (30078)------------------------------
% 2.38/0.70  % (30078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.70  % (30078)Termination reason: Refutation
% 2.38/0.70  
% 2.38/0.70  % (30078)Memory used [KB]: 1918
% 2.38/0.70  % (30078)Time elapsed: 0.268 s
% 2.38/0.70  % (30078)------------------------------
% 2.38/0.70  % (30078)------------------------------
% 2.38/0.70  % (30068)Success in time 0.338 s
%------------------------------------------------------------------------------
