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
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 235 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(subsumption_resolution,[],[f515,f30])).

fof(f30,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

% (2529)Refutation not found, incomplete strategy% (2529)------------------------------
% (2529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2529)Termination reason: Refutation not found, incomplete strategy

% (2529)Memory used [KB]: 10746
% (2529)Time elapsed: 0.178 s
% (2529)------------------------------
% (2529)------------------------------
fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f515,plain,(
    ~ r1_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f508,f402])).

fof(f402,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f391,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f391,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f37,f130])).

fof(f130,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK2,sK1) ),
    inference(backward_demodulation,[],[f71,f83])).

fof(f83,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f80,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f80,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f36,f48])).

fof(f48,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f71,plain,(
    r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f33,f28])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f508,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f337,f78])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k4_xboole_0(X4,X5),X3)
      | k1_xboole_0 = k4_xboole_0(X4,X5)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f337,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[],[f152,f32])).

fof(f152,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,X3),sK2),sK3) ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK3) ) ),
    inference(superposition,[],[f43,f28])).

fof(f55,plain,(
    ! [X4,X5,X3] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X5,X3)) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (2524)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (2519)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (2520)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (2525)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2535)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (2536)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (2548)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2548)Refutation not found, incomplete strategy% (2548)------------------------------
% 0.21/0.53  % (2548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2548)Memory used [KB]: 1663
% 0.21/0.53  % (2548)Time elapsed: 0.131 s
% 0.21/0.53  % (2548)------------------------------
% 0.21/0.53  % (2548)------------------------------
% 0.21/0.53  % (2534)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (2537)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (2535)Refutation not found, incomplete strategy% (2535)------------------------------
% 0.21/0.53  % (2535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2535)Memory used [KB]: 10618
% 0.21/0.53  % (2535)Time elapsed: 0.093 s
% 0.21/0.53  % (2535)------------------------------
% 0.21/0.53  % (2535)------------------------------
% 0.21/0.54  % (2527)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (2544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (2521)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (2523)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (2522)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (2540)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (2531)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (2526)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (2530)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (2528)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (2529)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (2542)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (2533)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (2547)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (2546)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (2545)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (2541)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (2547)Refutation not found, incomplete strategy% (2547)------------------------------
% 0.21/0.55  % (2547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2547)Memory used [KB]: 10746
% 0.21/0.55  % (2547)Time elapsed: 0.152 s
% 0.21/0.55  % (2547)------------------------------
% 0.21/0.55  % (2547)------------------------------
% 0.21/0.55  % (2543)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (2538)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (2532)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (2539)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (2526)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f516,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f515,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    r1_xboole_0(sK3,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.60/0.57    inference(flattening,[],[f15])).
% 1.60/0.59  % (2529)Refutation not found, incomplete strategy% (2529)------------------------------
% 1.60/0.59  % (2529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (2529)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (2529)Memory used [KB]: 10746
% 1.60/0.59  % (2529)Time elapsed: 0.178 s
% 1.60/0.59  % (2529)------------------------------
% 1.60/0.59  % (2529)------------------------------
% 1.81/0.59  fof(f15,plain,(
% 1.81/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.81/0.59    inference(ennf_transformation,[],[f14])).
% 1.81/0.60  fof(f14,negated_conjecture,(
% 1.81/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.81/0.60    inference(negated_conjecture,[],[f13])).
% 1.81/0.60  fof(f13,conjecture,(
% 1.81/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.81/0.60  fof(f515,plain,(
% 1.81/0.60    ~r1_xboole_0(sK3,sK1)),
% 1.81/0.60    inference(subsumption_resolution,[],[f508,f402])).
% 1.81/0.60  fof(f402,plain,(
% 1.81/0.60    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.81/0.60    inference(subsumption_resolution,[],[f391,f31])).
% 1.81/0.60  fof(f31,plain,(
% 1.81/0.60    sK1 != sK2),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f391,plain,(
% 1.81/0.60    k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK1 = sK2),
% 1.81/0.60    inference(superposition,[],[f37,f130])).
% 1.81/0.60  fof(f130,plain,(
% 1.81/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.81/0.60    inference(resolution,[],[f84,f41])).
% 1.81/0.60  fof(f41,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f27])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.81/0.60    inference(nnf_transformation,[],[f5])).
% 1.81/0.60  fof(f5,axiom,(
% 1.81/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.81/0.60  fof(f84,plain,(
% 1.81/0.60    r1_tarski(sK2,sK1)),
% 1.81/0.60    inference(backward_demodulation,[],[f71,f83])).
% 1.81/0.60  fof(f83,plain,(
% 1.81/0.60    sK2 = k4_xboole_0(sK2,sK0)),
% 1.81/0.60    inference(forward_demodulation,[],[f80,f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f6])).
% 1.81/0.60  fof(f6,axiom,(
% 1.81/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.81/0.60  fof(f80,plain,(
% 1.81/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.81/0.60    inference(superposition,[],[f36,f48])).
% 1.81/0.60  fof(f48,plain,(
% 1.81/0.60    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 1.81/0.60    inference(resolution,[],[f38,f29])).
% 1.81/0.60  fof(f29,plain,(
% 1.81/0.60    r1_xboole_0(sK2,sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f38,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f26])).
% 1.81/0.60  fof(f26,plain,(
% 1.81/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.81/0.60    inference(nnf_transformation,[],[f1])).
% 1.81/0.60  fof(f1,axiom,(
% 1.81/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.81/0.60  fof(f36,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f8])).
% 1.81/0.60  fof(f8,axiom,(
% 1.81/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.81/0.60  fof(f71,plain,(
% 1.81/0.60    r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 1.81/0.60    inference(resolution,[],[f43,f46])).
% 1.81/0.60  fof(f46,plain,(
% 1.81/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.81/0.60    inference(superposition,[],[f33,f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f11])).
% 1.81/0.60  fof(f11,axiom,(
% 1.81/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.81/0.60  fof(f43,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f19])).
% 1.81/0.60  fof(f19,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.81/0.60    inference(ennf_transformation,[],[f7])).
% 1.81/0.60  fof(f7,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.81/0.60  fof(f37,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 1.81/0.60    inference(cnf_transformation,[],[f17])).
% 1.81/0.60  fof(f17,plain,(
% 1.81/0.60    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f3])).
% 1.81/0.60  fof(f3,axiom,(
% 1.81/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.81/0.60  fof(f508,plain,(
% 1.81/0.60    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~r1_xboole_0(sK3,sK1)),
% 1.81/0.60    inference(resolution,[],[f337,f78])).
% 1.81/0.60  fof(f78,plain,(
% 1.81/0.60    ( ! [X4,X5,X3] : (~r1_tarski(k4_xboole_0(X4,X5),X3) | k1_xboole_0 = k4_xboole_0(X4,X5) | ~r1_xboole_0(X3,X4)) )),
% 1.81/0.60    inference(resolution,[],[f44,f34])).
% 1.81/0.60  fof(f34,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f4])).
% 1.81/0.60  fof(f4,axiom,(
% 1.81/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.81/0.60  fof(f44,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f21])).
% 1.81/0.60  fof(f21,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.81/0.60    inference(flattening,[],[f20])).
% 1.81/0.60  fof(f20,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.81/0.60    inference(ennf_transformation,[],[f10])).
% 1.81/0.60  fof(f10,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.81/0.60  fof(f337,plain,(
% 1.81/0.60    r1_tarski(k4_xboole_0(sK1,sK2),sK3)),
% 1.81/0.60    inference(superposition,[],[f152,f32])).
% 1.81/0.60  fof(f152,plain,(
% 1.81/0.60    ( ! [X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,X3),sK2),sK3)) )),
% 1.81/0.60    inference(resolution,[],[f55,f72])).
% 1.81/0.60  fof(f72,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK3)) )),
% 1.81/0.60    inference(superposition,[],[f43,f28])).
% 1.81/0.60  fof(f55,plain,(
% 1.81/0.60    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X5,X3))) )),
% 1.81/0.60    inference(resolution,[],[f42,f34])).
% 1.81/0.60  fof(f42,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f18])).
% 1.81/0.60  fof(f18,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f2])).
% 1.81/0.60  fof(f2,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.81/0.60  % SZS output end Proof for theBenchmark
% 1.81/0.60  % (2526)------------------------------
% 1.81/0.60  % (2526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (2526)Termination reason: Refutation
% 1.81/0.60  
% 1.81/0.60  % (2526)Memory used [KB]: 2174
% 1.81/0.60  % (2526)Time elapsed: 0.139 s
% 1.81/0.60  % (2526)------------------------------
% 1.81/0.60  % (2526)------------------------------
% 1.81/0.60  % (2518)Success in time 0.233 s
%------------------------------------------------------------------------------
