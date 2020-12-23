%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:01 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 220 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 ( 517 expanded)
%              Number of equality atoms :   91 ( 258 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f232,f256])).

fof(f256,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl9_1 ),
    inference(resolution,[],[f250,f88])).

fof(f88,plain,(
    ! [X2,X3,X1] : sP2(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f40])).

% (31594)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f40,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f250,plain,
    ( ! [X0] : ~ sP2(X0,sK5,sK4,sK4)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f248,f140])).

fof(f140,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f137,plain,(
    ! [X4,X3] :
      ( sP0(X4,X3,k1_xboole_0)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f55,f107])).

fof(f107,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(superposition,[],[f87,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f100,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f18,f17])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

% (31595)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK5,sK4,sK4)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl9_1 ),
    inference(resolution,[],[f245,f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X4,X2,X1,X0) )
            & ( sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f245,plain,
    ( sP3(sK4,sK4,sK5,k1_xboole_0)
    | ~ spl9_1 ),
    inference(superposition,[],[f91,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl9_1
  <=> k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f91,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f16,f21,f20])).

% (31592)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f232,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f231,f167])).

fof(f231,plain,(
    k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(resolution,[],[f224,f91])).

fof(f224,plain,(
    ! [X0] :
      ( ~ sP3(sK4,sK4,sK5,X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f217,f185])).

fof(f185,plain,(
    ! [X0] :
      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != X0
      | ~ sP3(sK4,sK4,sK5,X0) ) ),
    inference(resolution,[],[f175,f91])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ sP3(sK6,sK6,sK6,X1)
      | X0 != X1
      | ~ sP3(sK4,sK4,sK5,X0) ) ),
    inference(superposition,[],[f157,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_enumset1(X0,X0,X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f157,plain,(
    ! [X2] :
      ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X2
      | ~ sP3(sK6,sK6,sK6,X2) ) ),
    inference(superposition,[],[f78,f83])).

fof(f78,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK5) != k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f44,f76,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    k2_tarski(sK4,sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_tarski(sK4,sK5) != k1_tarski(sK6)
    & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK4,sK5) != k1_tarski(sK6)
      & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

% (31592)Refutation not found, incomplete strategy% (31592)------------------------------
% (31592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31592)Termination reason: Refutation not found, incomplete strategy

% (31592)Memory used [KB]: 10618
% (31592)Time elapsed: 0.169 s
% (31592)------------------------------
% (31592)------------------------------
fof(f217,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = X0
      | ~ sP3(sK4,sK4,sK5,X0) ) ),
    inference(resolution,[],[f82,f159])).

fof(f159,plain,(
    ! [X4] :
      ( r1_tarski(X4,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
      | ~ sP3(sK4,sK4,sK5,X4) ) ),
    inference(superposition,[],[f79,f83])).

fof(f79,plain,(
    r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f43,f76,f77])).

fof(f43,plain,(
    r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f77,f77])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:11:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.56  % (31583)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (31585)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (31584)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (31593)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (31603)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (31609)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (31593)Refutation not found, incomplete strategy% (31593)------------------------------
% 0.22/0.58  % (31593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31593)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31593)Memory used [KB]: 10618
% 0.22/0.58  % (31593)Time elapsed: 0.147 s
% 0.22/0.58  % (31593)------------------------------
% 0.22/0.58  % (31593)------------------------------
% 1.65/0.59  % (31597)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.65/0.59  % (31582)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.65/0.59  % (31582)Refutation not found, incomplete strategy% (31582)------------------------------
% 1.65/0.59  % (31582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (31582)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (31582)Memory used [KB]: 1663
% 1.65/0.59  % (31582)Time elapsed: 0.157 s
% 1.65/0.59  % (31582)------------------------------
% 1.65/0.59  % (31582)------------------------------
% 1.65/0.60  % (31586)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.65/0.60  % (31609)Refutation found. Thanks to Tanya!
% 1.65/0.60  % SZS status Theorem for theBenchmark
% 1.65/0.60  % SZS output start Proof for theBenchmark
% 1.65/0.60  fof(f257,plain,(
% 1.65/0.60    $false),
% 1.65/0.60    inference(avatar_sat_refutation,[],[f232,f256])).
% 1.65/0.60  fof(f256,plain,(
% 1.65/0.60    ~spl9_1),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f251])).
% 1.65/0.60  fof(f251,plain,(
% 1.65/0.60    $false | ~spl9_1),
% 1.65/0.60    inference(resolution,[],[f250,f88])).
% 1.65/0.60  fof(f88,plain,(
% 1.65/0.60    ( ! [X2,X3,X1] : (sP2(X1,X1,X2,X3)) )),
% 1.65/0.60    inference(equality_resolution,[],[f72])).
% 1.65/0.60  fof(f72,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X1) )),
% 1.65/0.60    inference(cnf_transformation,[],[f41])).
% 1.65/0.60  fof(f41,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 1.65/0.60    inference(rectify,[],[f40])).
% 1.65/0.60  % (31594)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.65/0.60  fof(f40,plain,(
% 1.65/0.60    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 1.65/0.60    inference(flattening,[],[f39])).
% 1.65/0.60  fof(f39,plain,(
% 1.65/0.60    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 1.65/0.60    inference(nnf_transformation,[],[f20])).
% 1.65/0.60  fof(f20,plain,(
% 1.65/0.60    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.65/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.65/0.60  fof(f250,plain,(
% 1.65/0.60    ( ! [X0] : (~sP2(X0,sK5,sK4,sK4)) ) | ~spl9_1),
% 1.65/0.60    inference(subsumption_resolution,[],[f248,f140])).
% 1.65/0.60  fof(f140,plain,(
% 1.65/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.65/0.60    inference(condensation,[],[f138])).
% 1.65/0.60  fof(f138,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.65/0.60    inference(resolution,[],[f137,f60])).
% 1.65/0.60  fof(f60,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f33])).
% 1.65/0.60  fof(f33,plain,(
% 1.65/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.65/0.60    inference(rectify,[],[f32])).
% 1.65/0.60  fof(f32,plain,(
% 1.65/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.65/0.60    inference(flattening,[],[f31])).
% 1.65/0.60  fof(f31,plain,(
% 1.65/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.65/0.60    inference(nnf_transformation,[],[f17])).
% 1.65/0.60  fof(f17,plain,(
% 1.65/0.60    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.65/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.65/0.60  fof(f137,plain,(
% 1.65/0.60    ( ! [X4,X3] : (sP0(X4,X3,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0)) )),
% 1.65/0.60    inference(resolution,[],[f55,f107])).
% 1.65/0.60  fof(f107,plain,(
% 1.65/0.60    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.65/0.60    inference(superposition,[],[f87,f106])).
% 1.65/0.60  fof(f106,plain,(
% 1.65/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.65/0.60    inference(resolution,[],[f100,f47])).
% 1.65/0.60  fof(f47,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f5])).
% 1.65/0.60  fof(f5,axiom,(
% 1.65/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.65/0.60  fof(f100,plain,(
% 1.65/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.65/0.60    inference(superposition,[],[f50,f45])).
% 1.65/0.60  fof(f45,plain,(
% 1.65/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/0.60    inference(cnf_transformation,[],[f4])).
% 1.65/0.60  fof(f4,axiom,(
% 1.65/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.65/0.60  fof(f50,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f15])).
% 1.65/0.60  fof(f15,plain,(
% 1.65/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.65/0.60    inference(ennf_transformation,[],[f3])).
% 1.65/0.60  fof(f3,axiom,(
% 1.65/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.65/0.60  fof(f87,plain,(
% 1.65/0.60    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(equality_resolution,[],[f62])).
% 1.65/0.60  fof(f62,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.65/0.60    inference(cnf_transformation,[],[f34])).
% 1.65/0.60  fof(f34,plain,(
% 1.65/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.65/0.60    inference(nnf_transformation,[],[f19])).
% 1.65/0.60  fof(f19,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.65/0.60    inference(definition_folding,[],[f2,f18,f17])).
% 1.65/0.60  fof(f18,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.65/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.65/0.60  fof(f2,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.65/0.60  fof(f55,plain,(
% 1.65/0.60    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f30])).
% 1.65/0.60  fof(f30,plain,(
% 1.65/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.65/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 1.65/0.60  fof(f29,plain,(
% 1.65/0.60    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.65/0.60    introduced(choice_axiom,[])).
% 1.65/0.60  fof(f28,plain,(
% 1.65/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.65/0.60    inference(rectify,[],[f27])).
% 1.65/0.60  % (31595)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.65/0.60  fof(f27,plain,(
% 1.65/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.65/0.60    inference(nnf_transformation,[],[f18])).
% 1.65/0.60  fof(f248,plain,(
% 1.65/0.60    ( ! [X0] : (~sP2(X0,sK5,sK4,sK4) | r2_hidden(X0,k1_xboole_0)) ) | ~spl9_1),
% 1.65/0.60    inference(resolution,[],[f245,f66])).
% 1.65/0.60  fof(f66,plain,(
% 1.65/0.60    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f38])).
% 1.65/0.60  fof(f38,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.65/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).
% 1.65/0.60  fof(f37,plain,(
% 1.65/0.60    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 1.65/0.60    introduced(choice_axiom,[])).
% 1.65/0.60  fof(f36,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.65/0.60    inference(rectify,[],[f35])).
% 1.65/0.60  fof(f35,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.65/0.60    inference(nnf_transformation,[],[f21])).
% 1.65/0.60  fof(f21,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 1.65/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.65/0.60  fof(f245,plain,(
% 1.65/0.60    sP3(sK4,sK4,sK5,k1_xboole_0) | ~spl9_1),
% 1.65/0.60    inference(superposition,[],[f91,f169])).
% 1.65/0.60  fof(f169,plain,(
% 1.65/0.60    k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5) | ~spl9_1),
% 1.65/0.60    inference(avatar_component_clause,[],[f167])).
% 1.65/0.60  fof(f167,plain,(
% 1.65/0.60    spl9_1 <=> k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5)),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.65/0.60  fof(f91,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.65/0.60    inference(equality_resolution,[],[f84])).
% 1.65/0.60  fof(f84,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.65/0.60    inference(definition_unfolding,[],[f73,f75])).
% 1.65/0.60  fof(f75,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f54,f64])).
% 1.65/0.60  fof(f64,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f10])).
% 1.65/0.60  fof(f10,axiom,(
% 1.65/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.65/0.60  fof(f54,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f9])).
% 1.65/0.60  fof(f9,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.65/0.60  fof(f73,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.65/0.60    inference(cnf_transformation,[],[f42])).
% 1.65/0.60  fof(f42,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.65/0.60    inference(nnf_transformation,[],[f22])).
% 1.65/0.60  fof(f22,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 1.65/0.60    inference(definition_folding,[],[f16,f21,f20])).
% 1.65/0.60  % (31592)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.60  fof(f16,plain,(
% 1.65/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.65/0.60    inference(ennf_transformation,[],[f6])).
% 1.65/0.60  fof(f6,axiom,(
% 1.65/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.65/0.60  fof(f232,plain,(
% 1.65/0.60    spl9_1),
% 1.65/0.60    inference(avatar_split_clause,[],[f231,f167])).
% 1.65/0.60  fof(f231,plain,(
% 1.65/0.60    k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK5)),
% 1.65/0.60    inference(resolution,[],[f224,f91])).
% 1.65/0.60  fof(f224,plain,(
% 1.65/0.60    ( ! [X0] : (~sP3(sK4,sK4,sK5,X0) | k1_xboole_0 = X0) )),
% 1.65/0.60    inference(subsumption_resolution,[],[f217,f185])).
% 1.65/0.60  fof(f185,plain,(
% 1.65/0.60    ( ! [X0] : (k3_enumset1(sK6,sK6,sK6,sK6,sK6) != X0 | ~sP3(sK4,sK4,sK5,X0)) )),
% 1.65/0.60    inference(resolution,[],[f175,f91])).
% 1.65/0.60  fof(f175,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~sP3(sK6,sK6,sK6,X1) | X0 != X1 | ~sP3(sK4,sK4,sK5,X0)) )),
% 1.65/0.60    inference(superposition,[],[f157,f83])).
% 1.65/0.60  fof(f83,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f74,f75])).
% 1.65/0.60  fof(f74,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f42])).
% 1.65/0.60  fof(f157,plain,(
% 1.65/0.60    ( ! [X2] : (k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X2 | ~sP3(sK6,sK6,sK6,X2)) )),
% 1.65/0.60    inference(superposition,[],[f78,f83])).
% 1.65/0.60  fof(f78,plain,(
% 1.65/0.60    k3_enumset1(sK4,sK4,sK4,sK4,sK5) != k3_enumset1(sK6,sK6,sK6,sK6,sK6)),
% 1.65/0.60    inference(definition_unfolding,[],[f44,f76,f77])).
% 1.65/0.60  fof(f77,plain,(
% 1.65/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f46,f76])).
% 1.65/0.60  fof(f46,plain,(
% 1.65/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f7])).
% 1.65/0.60  fof(f7,axiom,(
% 1.65/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.65/0.60  fof(f76,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f49,f75])).
% 1.65/0.60  fof(f49,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f8])).
% 1.65/0.60  fof(f8,axiom,(
% 1.65/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.60  fof(f44,plain,(
% 1.65/0.60    k2_tarski(sK4,sK5) != k1_tarski(sK6)),
% 1.65/0.60    inference(cnf_transformation,[],[f24])).
% 1.65/0.60  fof(f24,plain,(
% 1.65/0.60    k2_tarski(sK4,sK5) != k1_tarski(sK6) & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6))),
% 1.65/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f23])).
% 1.65/0.60  fof(f23,plain,(
% 1.65/0.60    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK4,sK5) != k1_tarski(sK6) & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)))),
% 1.65/0.60    introduced(choice_axiom,[])).
% 1.65/0.60  fof(f14,plain,(
% 1.65/0.60    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.65/0.60    inference(ennf_transformation,[],[f13])).
% 1.65/0.60  fof(f13,negated_conjecture,(
% 1.65/0.60    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.65/0.60    inference(negated_conjecture,[],[f12])).
% 1.65/0.60  fof(f12,conjecture,(
% 1.65/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 1.88/0.60  % (31592)Refutation not found, incomplete strategy% (31592)------------------------------
% 1.88/0.60  % (31592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.60  % (31592)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.60  
% 1.88/0.60  % (31592)Memory used [KB]: 10618
% 1.88/0.60  % (31592)Time elapsed: 0.169 s
% 1.88/0.60  % (31592)------------------------------
% 1.88/0.60  % (31592)------------------------------
% 1.88/0.60  fof(f217,plain,(
% 1.88/0.60    ( ! [X0] : (k1_xboole_0 = X0 | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = X0 | ~sP3(sK4,sK4,sK5,X0)) )),
% 1.88/0.60    inference(resolution,[],[f82,f159])).
% 1.88/0.60  fof(f159,plain,(
% 1.88/0.60    ( ! [X4] : (r1_tarski(X4,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) | ~sP3(sK4,sK4,sK5,X4)) )),
% 1.88/0.60    inference(superposition,[],[f79,f83])).
% 1.88/0.60  fof(f79,plain,(
% 1.88/0.60    r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k3_enumset1(sK6,sK6,sK6,sK6,sK6))),
% 1.88/0.60    inference(definition_unfolding,[],[f43,f76,f77])).
% 1.88/0.60  fof(f43,plain,(
% 1.88/0.60    r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6))),
% 1.88/0.60    inference(cnf_transformation,[],[f24])).
% 1.88/0.60  fof(f82,plain,(
% 1.88/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.88/0.60    inference(definition_unfolding,[],[f51,f77,f77])).
% 1.88/0.60  fof(f51,plain,(
% 1.88/0.60    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.88/0.60    inference(cnf_transformation,[],[f26])).
% 1.88/0.60  fof(f26,plain,(
% 1.88/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.88/0.60    inference(flattening,[],[f25])).
% 1.88/0.60  fof(f25,plain,(
% 1.88/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.88/0.60    inference(nnf_transformation,[],[f11])).
% 1.88/0.60  fof(f11,axiom,(
% 1.88/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.88/0.60  % SZS output end Proof for theBenchmark
% 1.88/0.60  % (31609)------------------------------
% 1.88/0.60  % (31609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.60  % (31609)Termination reason: Refutation
% 1.88/0.60  
% 1.88/0.60  % (31609)Memory used [KB]: 6268
% 1.88/0.60  % (31609)Time elapsed: 0.158 s
% 1.88/0.60  % (31609)------------------------------
% 1.88/0.60  % (31609)------------------------------
% 1.88/0.60  % (31611)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.88/0.61  % (31581)Success in time 0.239 s
%------------------------------------------------------------------------------
