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
% DateTime   : Thu Dec  3 12:49:00 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 147 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 676 expanded)
%              Number of equality atoms :   30 ( 152 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f143,f146,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f146,plain,(
    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f127,f38,f127,f71])).

fof(f71,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),X7)
      | r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),k4_xboole_0(X7,X8))
      | k8_relat_1(X7,k8_relat_1(X8,sK2)) = k8_relat_1(X9,sK2)
      | ~ r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),X9) ) ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2) ),
    inference(unit_resulting_resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(f38,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,(
    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,k4_xboole_0(X0,X1),X0),X0)
      | k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2) ) ),
    inference(factoring,[],[f69])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(X1,k4_xboole_0(X1,X2),X3),X1)
      | r2_hidden(sK4(X1,k4_xboole_0(X1,X2),X3),X3)
      | k8_relat_1(X1,k8_relat_1(X2,sK2)) = k8_relat_1(X3,sK2) ) ),
    inference(superposition,[],[f63,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f143,plain,(
    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f37,f127,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (25019)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.21/0.54  % (25019)Refutation not found, incomplete strategy% (25019)------------------------------
% 0.21/0.54  % (25019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25019)Memory used [KB]: 6268
% 0.21/0.54  % (25019)Time elapsed: 0.101 s
% 0.21/0.54  % (25019)------------------------------
% 0.21/0.54  % (25019)------------------------------
% 0.21/0.55  % (25013)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.28/0.55  % (25011)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.55/0.57  % (25035)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.55/0.58  % (25024)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.55/0.58  % (25021)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.55/0.58  % (25029)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.55/0.58  % (25012)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.55/0.58  % (25012)Refutation not found, incomplete strategy% (25012)------------------------------
% 1.55/0.58  % (25012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (25012)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (25012)Memory used [KB]: 6140
% 1.55/0.58  % (25012)Time elapsed: 0.151 s
% 1.55/0.58  % (25012)------------------------------
% 1.55/0.58  % (25012)------------------------------
% 1.55/0.59  % (25009)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 1.55/0.59  % (25015)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 1.55/0.59  % (25015)Refutation not found, incomplete strategy% (25015)------------------------------
% 1.55/0.59  % (25015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (25015)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (25015)Memory used [KB]: 10618
% 1.55/0.59  % (25015)Time elapsed: 0.153 s
% 1.55/0.59  % (25015)------------------------------
% 1.55/0.59  % (25015)------------------------------
% 1.55/0.59  % (25014)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 1.55/0.59  % (25032)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.59  % (25018)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.55/0.60  % (25031)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.55/0.60  % (25026)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 1.55/0.60  % (25010)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.55/0.61  % (25033)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.61  % (25023)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 1.55/0.61  % (25033)Refutation not found, incomplete strategy% (25033)------------------------------
% 1.55/0.61  % (25033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (25033)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (25033)Memory used [KB]: 10618
% 1.55/0.61  % (25033)Time elapsed: 0.170 s
% 1.55/0.61  % (25033)------------------------------
% 1.55/0.61  % (25033)------------------------------
% 1.55/0.61  % (25016)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.55/0.61  % (25023)Refutation not found, incomplete strategy% (25023)------------------------------
% 1.55/0.61  % (25023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (25023)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (25023)Memory used [KB]: 6140
% 1.55/0.61  % (25023)Time elapsed: 0.181 s
% 1.55/0.61  % (25023)------------------------------
% 1.55/0.61  % (25023)------------------------------
% 1.55/0.62  % (25028)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.55/0.62  % (25027)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.62  % (25022)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.55/0.62  % (25030)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.55/0.62  % (25038)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.55/0.63  % (25025)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.55/0.63  % (25037)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.55/0.63  % (25017)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.55/0.63  % (25017)Refutation not found, incomplete strategy% (25017)------------------------------
% 1.55/0.63  % (25017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (25017)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (25017)Memory used [KB]: 6140
% 1.55/0.63  % (25017)Time elapsed: 0.200 s
% 1.55/0.63  % (25017)------------------------------
% 1.55/0.63  % (25017)------------------------------
% 1.55/0.63  % (25020)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.55/0.64  % (25036)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.55/0.65  % (25034)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 2.19/0.68  % (25018)Refutation found. Thanks to Tanya!
% 2.19/0.68  % SZS status Theorem for theBenchmark
% 2.40/0.69  % (25075)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.40/0.70  % SZS output start Proof for theBenchmark
% 2.40/0.70  fof(f431,plain,(
% 2.40/0.70    $false),
% 2.40/0.70    inference(unit_resulting_resolution,[],[f143,f146,f61])).
% 2.40/0.70  fof(f61,plain,(
% 2.40/0.70    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(equality_resolution,[],[f49])).
% 2.40/0.71  fof(f49,plain,(
% 2.40/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.40/0.71    inference(cnf_transformation,[],[f32])).
% 2.40/0.71  fof(f32,plain,(
% 2.40/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 2.40/0.71  fof(f31,plain,(
% 2.40/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.40/0.71    introduced(choice_axiom,[])).
% 2.40/0.71  fof(f30,plain,(
% 2.40/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.71    inference(rectify,[],[f29])).
% 2.40/0.71  fof(f29,plain,(
% 2.40/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.71    inference(flattening,[],[f28])).
% 2.40/0.71  fof(f28,plain,(
% 2.40/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.71    inference(nnf_transformation,[],[f2])).
% 2.40/0.71  fof(f2,axiom,(
% 2.40/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.40/0.71  fof(f146,plain,(
% 2.40/0.71    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1))),
% 2.40/0.71    inference(unit_resulting_resolution,[],[f127,f38,f127,f71])).
% 2.40/0.71  fof(f71,plain,(
% 2.40/0.71    ( ! [X8,X7,X9] : (~r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),X7) | r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),k4_xboole_0(X7,X8)) | k8_relat_1(X7,k8_relat_1(X8,sK2)) = k8_relat_1(X9,sK2) | ~r2_hidden(sK4(X7,k4_xboole_0(X7,X8),X9),X9)) )),
% 2.40/0.71    inference(superposition,[],[f63,f53])).
% 2.40/0.71  fof(f53,plain,(
% 2.40/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.40/0.71    inference(cnf_transformation,[],[f32])).
% 2.40/0.71  fof(f63,plain,(
% 2.40/0.71    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2)) )),
% 2.40/0.71    inference(unit_resulting_resolution,[],[f36,f56])).
% 2.40/0.71  fof(f56,plain,(
% 2.40/0.71    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 2.40/0.71    inference(definition_unfolding,[],[f39,f46])).
% 2.40/0.71  fof(f46,plain,(
% 2.40/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.40/0.71    inference(cnf_transformation,[],[f7])).
% 2.40/0.71  fof(f7,axiom,(
% 2.40/0.71    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.40/0.71  fof(f39,plain,(
% 2.40/0.71    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.40/0.71    inference(cnf_transformation,[],[f17])).
% 2.40/0.71  fof(f17,plain,(
% 2.40/0.71    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.40/0.71    inference(ennf_transformation,[],[f11])).
% 2.40/0.71  fof(f11,axiom,(
% 2.40/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 2.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 2.40/0.71  fof(f36,plain,(
% 2.40/0.71    v1_relat_1(sK2)),
% 2.40/0.71    inference(cnf_transformation,[],[f21])).
% 2.40/0.71  fof(f21,plain,(
% 2.40/0.71    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 2.40/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 2.40/0.71  fof(f20,plain,(
% 2.40/0.71    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 2.40/0.71    introduced(choice_axiom,[])).
% 2.40/0.71  fof(f16,plain,(
% 2.40/0.71    ? [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.40/0.71    inference(flattening,[],[f15])).
% 2.40/0.71  fof(f15,plain,(
% 2.40/0.71    ? [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(X0,X2) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.40/0.71    inference(ennf_transformation,[],[f13])).
% 2.40/0.71  fof(f13,negated_conjecture,(
% 2.40/0.71    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 2.40/0.71    inference(negated_conjecture,[],[f12])).
% 2.40/0.71  fof(f12,conjecture,(
% 2.40/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 2.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).
% 2.40/0.71  fof(f38,plain,(
% 2.40/0.71    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)),
% 2.40/0.71    inference(cnf_transformation,[],[f21])).
% 2.40/0.71  fof(f127,plain,(
% 2.40/0.71    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),sK0)),
% 2.40/0.71    inference(unit_resulting_resolution,[],[f38,f87])).
% 2.40/0.71  fof(f87,plain,(
% 2.40/0.71    ( ! [X0,X1] : (r2_hidden(sK4(X0,k4_xboole_0(X0,X1),X0),X0) | k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2)) )),
% 2.40/0.71    inference(factoring,[],[f69])).
% 2.40/0.71  fof(f69,plain,(
% 2.40/0.71    ( ! [X2,X3,X1] : (r2_hidden(sK4(X1,k4_xboole_0(X1,X2),X3),X1) | r2_hidden(sK4(X1,k4_xboole_0(X1,X2),X3),X3) | k8_relat_1(X1,k8_relat_1(X2,sK2)) = k8_relat_1(X3,sK2)) )),
% 2.40/0.71    inference(superposition,[],[f63,f51])).
% 2.40/0.71  fof(f51,plain,(
% 2.40/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.40/0.71    inference(cnf_transformation,[],[f32])).
% 2.40/0.71  fof(f143,plain,(
% 2.40/0.71    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),sK0),sK1)),
% 2.40/0.71    inference(unit_resulting_resolution,[],[f37,f127,f40])).
% 2.40/0.71  fof(f40,plain,(
% 2.40/0.71    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.71    inference(cnf_transformation,[],[f25])).
% 2.40/0.71  fof(f25,plain,(
% 2.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 2.40/0.71  fof(f24,plain,(
% 2.40/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.40/0.71    introduced(choice_axiom,[])).
% 2.40/0.71  fof(f23,plain,(
% 2.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.71    inference(rectify,[],[f22])).
% 2.40/0.71  fof(f22,plain,(
% 2.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.71    inference(nnf_transformation,[],[f18])).
% 2.40/0.71  fof(f18,plain,(
% 2.40/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.71    inference(ennf_transformation,[],[f1])).
% 2.40/0.71  fof(f1,axiom,(
% 2.40/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.71  fof(f37,plain,(
% 2.40/0.71    r1_tarski(sK0,sK1)),
% 2.40/0.71    inference(cnf_transformation,[],[f21])).
% 2.40/0.71  % SZS output end Proof for theBenchmark
% 2.40/0.71  % (25018)------------------------------
% 2.40/0.71  % (25018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.71  % (25018)Termination reason: Refutation
% 2.40/0.71  
% 2.40/0.71  % (25018)Memory used [KB]: 6652
% 2.40/0.71  % (25018)Time elapsed: 0.251 s
% 2.40/0.71  % (25018)------------------------------
% 2.40/0.71  % (25018)------------------------------
% 2.40/0.71  % (25008)Success in time 0.336 s
%------------------------------------------------------------------------------
