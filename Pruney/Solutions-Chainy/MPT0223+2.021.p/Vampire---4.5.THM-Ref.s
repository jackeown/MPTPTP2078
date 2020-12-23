%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:53 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 201 expanded)
%              Number of equality atoms :   64 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f923,plain,(
    $false ),
    inference(subsumption_resolution,[],[f922,f43])).

fof(f43,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f922,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f867,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f867,plain,(
    r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f865,f78])).

fof(f78,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f865,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f795,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f795,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(resolution,[],[f724,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f724,plain,(
    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f716,f44])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f716,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_xboole_0)
    | r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(superposition,[],[f104,f676])).

fof(f676,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f669,f125])).

fof(f125,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f122,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f122,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f669,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(superposition,[],[f152,f540])).

fof(f540,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f115,f42])).

fof(f42,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f52,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f152,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),X0)) = k4_xboole_0(k1_tarski(sK0),X0) ),
    inference(superposition,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,k3_xboole_0(X1,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.60/0.57  % (17940)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.60/0.59  % (17958)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.60/0.59  % (17948)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.60/0.59  % (17937)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.60/0.59  % (17937)Refutation not found, incomplete strategy% (17937)------------------------------
% 1.60/0.59  % (17937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (17937)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (17937)Memory used [KB]: 1663
% 1.60/0.59  % (17937)Time elapsed: 0.153 s
% 1.60/0.59  % (17937)------------------------------
% 1.60/0.59  % (17937)------------------------------
% 1.60/0.59  % (17941)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.59  % (17951)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.59  % (17953)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.60/0.59  % (17942)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.60  % (17945)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.60/0.60  % (17947)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.60/0.60  % (17946)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.60/0.60  % (17936)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.60/0.61  % (17959)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.62  % (17938)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.60/0.62  % (17939)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.60/0.62  % (17943)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.60/0.62  % (17964)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.60/0.63  % (17956)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.60/0.63  % (17965)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.60/0.63  % (17965)Refutation not found, incomplete strategy% (17965)------------------------------
% 1.60/0.63  % (17965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (17965)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (17965)Memory used [KB]: 1663
% 1.60/0.63  % (17965)Time elapsed: 0.195 s
% 1.60/0.63  % (17965)------------------------------
% 1.60/0.63  % (17965)------------------------------
% 1.60/0.63  % (17957)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.60/0.63  % (17944)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.60/0.63  % (17955)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.60/0.64  % (17952)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.64  % (17962)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.64  % (17949)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.60/0.64  % (17952)Refutation not found, incomplete strategy% (17952)------------------------------
% 1.60/0.64  % (17952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.64  % (17952)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.64  
% 1.60/0.64  % (17952)Memory used [KB]: 10618
% 1.60/0.64  % (17952)Time elapsed: 0.202 s
% 1.60/0.64  % (17952)------------------------------
% 1.60/0.64  % (17952)------------------------------
% 1.60/0.64  % (17950)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.60/0.64  % (17963)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.60/0.64  % (17960)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.64  % (17961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.24/0.65  % (17954)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.24/0.67  % (17945)Refutation found. Thanks to Tanya!
% 2.24/0.67  % SZS status Theorem for theBenchmark
% 2.24/0.67  % SZS output start Proof for theBenchmark
% 2.24/0.67  fof(f923,plain,(
% 2.24/0.67    $false),
% 2.24/0.67    inference(subsumption_resolution,[],[f922,f43])).
% 2.24/0.67  fof(f43,plain,(
% 2.24/0.67    sK0 != sK1),
% 2.24/0.67    inference(cnf_transformation,[],[f31])).
% 2.24/0.67  fof(f31,plain,(
% 2.24/0.67    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.24/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).
% 2.24/0.67  fof(f30,plain,(
% 2.24/0.67    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.24/0.67    introduced(choice_axiom,[])).
% 2.24/0.67  fof(f24,plain,(
% 2.24/0.67    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.24/0.67    inference(ennf_transformation,[],[f22])).
% 2.24/0.67  fof(f22,negated_conjecture,(
% 2.24/0.67    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.24/0.67    inference(negated_conjecture,[],[f21])).
% 2.24/0.67  fof(f21,conjecture,(
% 2.24/0.67    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 2.24/0.67  fof(f922,plain,(
% 2.24/0.67    sK0 = sK1),
% 2.24/0.67    inference(resolution,[],[f867,f79])).
% 2.24/0.67  fof(f79,plain,(
% 2.24/0.67    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.24/0.67    inference(equality_resolution,[],[f56])).
% 2.24/0.67  fof(f56,plain,(
% 2.24/0.67    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.24/0.67    inference(cnf_transformation,[],[f35])).
% 2.24/0.67  fof(f35,plain,(
% 2.24/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.24/0.67  fof(f34,plain,(
% 2.24/0.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.24/0.67    introduced(choice_axiom,[])).
% 2.24/0.67  fof(f33,plain,(
% 2.24/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.67    inference(rectify,[],[f32])).
% 2.24/0.67  fof(f32,plain,(
% 2.24/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.24/0.67    inference(nnf_transformation,[],[f15])).
% 2.24/0.67  fof(f15,axiom,(
% 2.24/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.24/0.67  fof(f867,plain,(
% 2.24/0.67    r2_hidden(sK0,k1_tarski(sK1))),
% 2.24/0.67    inference(subsumption_resolution,[],[f865,f78])).
% 2.24/0.67  fof(f78,plain,(
% 2.24/0.67    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.24/0.67    inference(equality_resolution,[],[f77])).
% 2.24/0.67  fof(f77,plain,(
% 2.24/0.67    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.24/0.67    inference(equality_resolution,[],[f57])).
% 2.24/0.67  fof(f57,plain,(
% 2.24/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.24/0.67    inference(cnf_transformation,[],[f35])).
% 2.24/0.67  fof(f865,plain,(
% 2.24/0.67    r2_hidden(sK0,k1_tarski(sK1)) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 2.24/0.67    inference(resolution,[],[f795,f67])).
% 2.24/0.67  fof(f67,plain,(
% 2.24/0.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f36])).
% 2.24/0.67  fof(f36,plain,(
% 2.24/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.24/0.67    inference(nnf_transformation,[],[f28])).
% 2.24/0.67  fof(f28,plain,(
% 2.24/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.24/0.67    inference(ennf_transformation,[],[f4])).
% 2.24/0.67  fof(f4,axiom,(
% 2.24/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.24/0.67  fof(f795,plain,(
% 2.24/0.67    ~r2_hidden(sK0,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 2.24/0.67    inference(resolution,[],[f724,f61])).
% 2.24/0.67  fof(f61,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f27])).
% 2.24/0.67  fof(f27,plain,(
% 2.24/0.67    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f20])).
% 2.24/0.67  fof(f20,axiom,(
% 2.24/0.67    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 2.24/0.67  fof(f724,plain,(
% 2.24/0.67    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 2.24/0.67    inference(subsumption_resolution,[],[f716,f44])).
% 2.24/0.67  fof(f44,plain,(
% 2.24/0.67    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f12])).
% 2.24/0.67  fof(f12,axiom,(
% 2.24/0.67    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.24/0.67  fof(f716,plain,(
% 2.24/0.67    ~r1_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k1_xboole_0) | r1_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 2.24/0.67    inference(superposition,[],[f104,f676])).
% 2.24/0.67  fof(f676,plain,(
% 2.24/0.67    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 2.24/0.67    inference(forward_demodulation,[],[f669,f125])).
% 2.24/0.67  fof(f125,plain,(
% 2.24/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.24/0.67    inference(forward_demodulation,[],[f122,f45])).
% 2.24/0.67  fof(f45,plain,(
% 2.24/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f7])).
% 2.24/0.67  fof(f7,axiom,(
% 2.24/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.24/0.67  fof(f122,plain,(
% 2.24/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.24/0.67    inference(superposition,[],[f53,f46])).
% 2.24/0.67  fof(f46,plain,(
% 2.24/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.24/0.67    inference(cnf_transformation,[],[f8])).
% 2.24/0.67  fof(f8,axiom,(
% 2.24/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.24/0.67  fof(f53,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.24/0.67    inference(cnf_transformation,[],[f9])).
% 2.24/0.67  fof(f9,axiom,(
% 2.24/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.24/0.67  fof(f669,plain,(
% 2.24/0.67    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 2.24/0.67    inference(superposition,[],[f152,f540])).
% 2.24/0.67  fof(f540,plain,(
% 2.24/0.67    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 2.24/0.67    inference(superposition,[],[f115,f42])).
% 2.24/0.67  fof(f42,plain,(
% 2.24/0.67    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.24/0.67    inference(cnf_transformation,[],[f31])).
% 2.24/0.67  fof(f115,plain,(
% 2.24/0.67    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.24/0.67    inference(superposition,[],[f52,f49])).
% 2.24/0.67  fof(f49,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f1])).
% 2.24/0.67  fof(f1,axiom,(
% 2.24/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.24/0.67  fof(f52,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.24/0.67    inference(cnf_transformation,[],[f5])).
% 2.24/0.67  fof(f5,axiom,(
% 2.24/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.24/0.67  fof(f152,plain,(
% 2.24/0.67    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),X0)) = k4_xboole_0(k1_tarski(sK0),X0)) )),
% 2.24/0.67    inference(superposition,[],[f63,f42])).
% 2.24/0.67  fof(f63,plain,(
% 2.24/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f10])).
% 2.24/0.67  fof(f10,axiom,(
% 2.24/0.67    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.24/0.67  fof(f104,plain,(
% 2.24/0.67    ( ! [X2,X1] : (~r1_xboole_0(X2,k3_xboole_0(X1,X2)) | r1_xboole_0(X1,X2)) )),
% 2.24/0.67    inference(resolution,[],[f60,f55])).
% 2.24/0.67  fof(f55,plain,(
% 2.24/0.67    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f25])).
% 2.24/0.67  fof(f25,plain,(
% 2.24/0.67    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f3])).
% 2.24/0.67  fof(f3,axiom,(
% 2.24/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.24/0.67  fof(f60,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f26])).
% 2.24/0.67  fof(f26,plain,(
% 2.24/0.67    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f13])).
% 2.24/0.67  fof(f13,axiom,(
% 2.24/0.67    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 2.24/0.67  % SZS output end Proof for theBenchmark
% 2.24/0.67  % (17945)------------------------------
% 2.24/0.67  % (17945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.67  % (17945)Termination reason: Refutation
% 2.24/0.67  
% 2.24/0.67  % (17945)Memory used [KB]: 2430
% 2.24/0.67  % (17945)Time elapsed: 0.229 s
% 2.24/0.67  % (17945)------------------------------
% 2.24/0.67  % (17945)------------------------------
% 2.24/0.68  % (17935)Success in time 0.315 s
%------------------------------------------------------------------------------
