%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 180 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   25
%              Number of atoms          :  255 ( 748 expanded)
%              Number of equality atoms :  122 ( 333 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(resolution,[],[f335,f145])).

fof(f145,plain,(
    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f140,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f140,plain,(
    r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f58,f137])).

fof(f137,plain,(
    k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f135,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f135,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f46,f132])).

fof(f132,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

% (23615)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (23597)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (23612)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (23611)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (23610)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (23606)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (23604)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (23609)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (23607)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,X0),sK2) ) ),
    inference(resolution,[],[f81,f57])).

fof(f81,plain,(
    ! [X0] :
      ( r1_xboole_0(k2_tarski(sK0,X0),sK2)
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f335,plain,(
    ! [X0] : ~ r1_xboole_0(sK2,k2_tarski(sK0,X0)) ),
    inference(superposition,[],[f326,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f326,plain,(
    ! [X0] : ~ r1_xboole_0(sK2,k2_tarski(X0,sK0)) ),
    inference(superposition,[],[f304,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f304,plain,(
    ! [X4,X5] : ~ r1_xboole_0(sK2,k1_enumset1(X4,X5,sK0)) ),
    inference(resolution,[],[f299,f75])).

fof(f75,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f299,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f292,f55])).

% (23618)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f292,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f287,f145])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,k2_tarski(X0,sK1))
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f165,f50])).

fof(f165,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(sK2,k1_enumset1(X4,X5,sK1))
      | r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f150,f75])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ r1_xboole_0(sK2,X0)
      | r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f143,f55])).

fof(f143,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f43,f141])).

fof(f141,plain,(
    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f139,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f139,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k5_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f51,f137])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:46:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (23616)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (23608)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (23600)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (23595)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23598)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (23596)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (23599)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (23593)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (23616)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(resolution,[],[f335,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    r1_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f140,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(superposition,[],[f58,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(superposition,[],[f46,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,sK1),sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f85,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 0.21/0.53  % (23615)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (23597)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (23612)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (23611)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (23610)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (23606)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (23604)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23609)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (23607)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.38/0.54    inference(flattening,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.38/0.54    inference(nnf_transformation,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.38/0.54    inference(ennf_transformation,[],[f22])).
% 1.38/0.54  fof(f22,negated_conjecture,(
% 1.38/0.54    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.38/0.54    inference(negated_conjecture,[],[f21])).
% 1.38/0.54  fof(f21,conjecture,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.38/0.54  fof(f85,plain,(
% 1.38/0.54    ( ! [X0] : (r2_hidden(X0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k3_xboole_0(k2_tarski(sK0,X0),sK2)) )),
% 1.38/0.54    inference(resolution,[],[f81,f57])).
% 1.38/0.54  fof(f81,plain,(
% 1.38/0.54    ( ! [X0] : (r1_xboole_0(k2_tarski(sK0,X0),sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(X0,sK2)) )),
% 1.38/0.54    inference(resolution,[],[f41,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f32])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f335,plain,(
% 1.38/0.54    ( ! [X0] : (~r1_xboole_0(sK2,k2_tarski(sK0,X0))) )),
% 1.38/0.54    inference(superposition,[],[f326,f47])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.38/0.54  fof(f326,plain,(
% 1.38/0.54    ( ! [X0] : (~r1_xboole_0(sK2,k2_tarski(X0,sK0))) )),
% 1.38/0.54    inference(superposition,[],[f304,f50])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.54  fof(f304,plain,(
% 1.38/0.54    ( ! [X4,X5] : (~r1_xboole_0(sK2,k1_enumset1(X4,X5,sK0))) )),
% 1.38/0.54    inference(resolution,[],[f299,f75])).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.38/0.54    inference(equality_resolution,[],[f74])).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.38/0.54    inference(equality_resolution,[],[f66])).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(rectify,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(flattening,[],[f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(nnf_transformation,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.38/0.54  fof(f299,plain,(
% 1.38/0.54    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(sK2,X0)) )),
% 1.38/0.54    inference(resolution,[],[f292,f55])).
% 1.38/0.54  % (23618)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(rectify,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.38/0.54  fof(f292,plain,(
% 1.38/0.54    r2_hidden(sK0,sK2)),
% 1.38/0.54    inference(resolution,[],[f287,f145])).
% 1.38/0.54  fof(f287,plain,(
% 1.38/0.54    ( ! [X0] : (~r1_xboole_0(sK2,k2_tarski(X0,sK1)) | r2_hidden(sK0,sK2)) )),
% 1.38/0.54    inference(superposition,[],[f165,f50])).
% 1.38/0.54  fof(f165,plain,(
% 1.38/0.54    ( ! [X4,X5] : (~r1_xboole_0(sK2,k1_enumset1(X4,X5,sK1)) | r2_hidden(sK0,sK2)) )),
% 1.38/0.54    inference(resolution,[],[f150,f75])).
% 1.38/0.54  fof(f150,plain,(
% 1.38/0.54    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(sK2,X0) | r2_hidden(sK0,sK2)) )),
% 1.38/0.54    inference(resolution,[],[f143,f55])).
% 1.38/0.54  fof(f143,plain,(
% 1.38/0.54    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f142])).
% 1.38/0.54  fof(f142,plain,(
% 1.38/0.54    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.38/0.54    inference(backward_demodulation,[],[f43,f141])).
% 1.38/0.54  fof(f141,plain,(
% 1.38/0.54    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.54    inference(forward_demodulation,[],[f139,f45])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.38/0.54  fof(f139,plain,(
% 1.38/0.54    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k5_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 1.38/0.54    inference(superposition,[],[f51,f137])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f32])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (23616)------------------------------
% 1.38/0.54  % (23616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (23616)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (23616)Memory used [KB]: 1918
% 1.38/0.54  % (23616)Time elapsed: 0.062 s
% 1.38/0.54  % (23616)------------------------------
% 1.38/0.54  % (23616)------------------------------
% 1.38/0.54  % (23603)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (23622)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (23617)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (23592)Success in time 0.177 s
%------------------------------------------------------------------------------
