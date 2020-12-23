%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:09 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 234 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  326 ( 628 expanded)
%              Number of equality atoms :  177 ( 370 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f94,f378,f409])).

fof(f409,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f396,f74])).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

% (6449)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f396,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f390,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X2,X3))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f102,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f102,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(resolution,[],[f79,f78])).

fof(f78,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f28])).

% (6462)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f79,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f15,f16])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f390,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_3 ),
    inference(superposition,[],[f65,f93])).

fof(f93,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_3
  <=> k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f378,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f376,f83])).

fof(f83,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_1
  <=> k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f376,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | spl6_1
    | spl6_2 ),
    inference(resolution,[],[f337,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f337,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f327,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(extensionality_resolution,[],[f75,f86])).

fof(f86,plain,
    ( sK1 != sK2
    | spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f327,plain,
    ( r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl6_1 ),
    inference(superposition,[],[f39,f325])).

fof(f325,plain,
    ( sK2 = sK3(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 = sK3(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl6_1 ),
    inference(superposition,[],[f83,f175])).

% (6458)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f175,plain,(
    ! [X10,X11] :
      ( k5_xboole_0(X10,k3_xboole_0(X10,k3_enumset1(X11,X11,X11,X11,X11))) = X10
      | sK3(X10,k3_enumset1(X11,X11,X11,X11,X11)) = X11 ) ),
    inference(resolution,[],[f112,f66])).

fof(f112,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))
      | sK3(X3,k3_enumset1(X2,X2,X2,X2,X2)) = X2 ) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f89,f85,f91])).

fof(f89,plain,
    ( sK1 != sK2
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( sK1 != sK2
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f34,f62,f38,f62,f62])).

fof(f34,plain,
    ( sK1 != sK2
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK1 = sK2
      | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) )
    & ( sK1 != sK2
      | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK1 = sK2
        | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) )
      & ( sK1 != sK2
        | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f88,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f63,f85,f81])).

fof(f63,plain,
    ( sK1 = sK2
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f35,f62,f38,f62,f62])).

fof(f35,plain,
    ( sK1 = sK2
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (6455)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (6455)Refutation not found, incomplete strategy% (6455)------------------------------
% 0.21/0.56  % (6455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6447)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (6455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6455)Memory used [KB]: 1663
% 0.21/0.57  % (6455)Time elapsed: 0.134 s
% 0.21/0.57  % (6455)------------------------------
% 0.21/0.57  % (6455)------------------------------
% 0.21/0.57  % (6463)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.59  % (6451)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.59  % (6467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.59  % (6459)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (6442)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.59  % (6442)Refutation not found, incomplete strategy% (6442)------------------------------
% 0.21/0.59  % (6442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (6442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (6442)Memory used [KB]: 1663
% 0.21/0.59  % (6442)Time elapsed: 0.147 s
% 0.21/0.59  % (6442)------------------------------
% 0.21/0.59  % (6442)------------------------------
% 0.21/0.59  % (6459)Refutation not found, incomplete strategy% (6459)------------------------------
% 0.21/0.59  % (6459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (6467)Refutation not found, incomplete strategy% (6467)------------------------------
% 0.21/0.59  % (6467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (6446)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.60  % (6467)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (6467)Memory used [KB]: 6140
% 0.21/0.60  % (6467)Time elapsed: 0.155 s
% 0.21/0.60  % (6467)------------------------------
% 0.21/0.60  % (6467)------------------------------
% 0.21/0.60  % (6459)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (6459)Memory used [KB]: 1663
% 0.21/0.60  % (6459)Time elapsed: 0.155 s
% 0.21/0.60  % (6459)------------------------------
% 0.21/0.60  % (6459)------------------------------
% 0.21/0.60  % (6444)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.60  % (6445)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.60  % (6464)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.60  % (6441)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.60  % (6443)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.60  % (6456)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.87/0.61  % (6447)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % (6470)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.87/0.61  % (6470)Refutation not found, incomplete strategy% (6470)------------------------------
% 1.87/0.61  % (6470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (6470)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (6470)Memory used [KB]: 1663
% 1.87/0.61  % (6470)Time elapsed: 0.001 s
% 1.87/0.61  % (6470)------------------------------
% 1.87/0.61  % (6470)------------------------------
% 1.87/0.61  % (6469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f410,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(avatar_sat_refutation,[],[f88,f94,f378,f409])).
% 1.87/0.61  fof(f409,plain,(
% 1.87/0.61    ~spl6_3),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f408])).
% 1.87/0.61  fof(f408,plain,(
% 1.87/0.61    $false | ~spl6_3),
% 1.87/0.61    inference(subsumption_resolution,[],[f396,f74])).
% 1.87/0.61  fof(f74,plain,(
% 1.87/0.61    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.87/0.61    inference(equality_resolution,[],[f73])).
% 1.87/0.61  fof(f73,plain,(
% 1.87/0.61    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.87/0.61    inference(equality_resolution,[],[f69])).
% 1.87/0.61  fof(f69,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.87/0.61    inference(definition_unfolding,[],[f45,f62])).
% 1.87/0.61  fof(f62,plain,(
% 1.87/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.87/0.61    inference(definition_unfolding,[],[f36,f61])).
% 1.87/0.61  fof(f61,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.87/0.61    inference(definition_unfolding,[],[f37,f60])).
% 1.87/0.61  fof(f60,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.87/0.61    inference(definition_unfolding,[],[f48,f49])).
% 1.87/0.61  fof(f49,plain,(
% 1.87/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.87/0.61  % (6449)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.87/0.61  fof(f37,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.87/0.61  fof(f36,plain,(
% 1.87/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.87/0.61    inference(rectify,[],[f24])).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.87/0.61    inference(nnf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.87/0.61  fof(f396,plain,(
% 1.87/0.61    ~r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_3),
% 1.87/0.61    inference(resolution,[],[f390,f105])).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X2,X3)) | ~r2_hidden(X1,X0)) )),
% 1.87/0.61    inference(resolution,[],[f102,f41])).
% 1.87/0.61  fof(f41,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f22])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f14,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(ennf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,plain,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(rectify,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.87/0.61  fof(f102,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.87/0.61    inference(resolution,[],[f79,f78])).
% 1.87/0.61  fof(f78,plain,(
% 1.87/0.61    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.87/0.61    inference(equality_resolution,[],[f51])).
% 1.87/0.61  fof(f51,plain,(
% 1.87/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f32])).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.87/0.61    inference(rectify,[],[f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.87/0.61    inference(flattening,[],[f28])).
% 1.87/0.61  % (6462)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.87/0.61    inference(nnf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,plain,(
% 1.87/0.61    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.87/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.87/0.61    inference(equality_resolution,[],[f72])).
% 1.87/0.61  fof(f72,plain,(
% 1.87/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.87/0.61    inference(definition_unfolding,[],[f58,f60])).
% 1.87/0.61  fof(f58,plain,(
% 1.87/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.87/0.61    inference(cnf_transformation,[],[f33])).
% 1.87/0.61  fof(f33,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.87/0.61    inference(nnf_transformation,[],[f17])).
% 1.87/0.61  fof(f17,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.87/0.61    inference(definition_folding,[],[f15,f16])).
% 1.87/0.61  fof(f15,plain,(
% 1.87/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.87/0.61    inference(ennf_transformation,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.87/0.61  fof(f390,plain,(
% 1.87/0.61    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_3),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f389])).
% 1.87/0.61  fof(f389,plain,(
% 1.87/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_3),
% 1.87/0.61    inference(superposition,[],[f65,f93])).
% 1.87/0.61  fof(f93,plain,(
% 1.87/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl6_3),
% 1.87/0.61    inference(avatar_component_clause,[],[f91])).
% 1.87/0.61  fof(f91,plain,(
% 1.87/0.61    spl6_3 <=> k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.87/0.61  fof(f65,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(definition_unfolding,[],[f43,f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f23])).
% 1.87/0.61  fof(f23,plain,(
% 1.87/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(nnf_transformation,[],[f3])).
% 1.87/0.61  fof(f3,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.87/0.61  fof(f378,plain,(
% 1.87/0.61    spl6_1 | spl6_2),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f377])).
% 1.87/0.61  fof(f377,plain,(
% 1.87/0.61    $false | (spl6_1 | spl6_2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f376,f83])).
% 1.87/0.61  fof(f83,plain,(
% 1.87/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | spl6_1),
% 1.87/0.61    inference(avatar_component_clause,[],[f81])).
% 1.87/0.61  fof(f81,plain,(
% 1.87/0.61    spl6_1 <=> k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.87/0.61  fof(f376,plain,(
% 1.87/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | (spl6_1 | spl6_2)),
% 1.87/0.61    inference(resolution,[],[f337,f66])).
% 1.87/0.61  fof(f66,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.87/0.61    inference(definition_unfolding,[],[f42,f38])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f23])).
% 1.87/0.61  fof(f337,plain,(
% 1.87/0.61    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | (spl6_1 | spl6_2)),
% 1.87/0.61    inference(subsumption_resolution,[],[f327,f107])).
% 1.87/0.61  fof(f107,plain,(
% 1.87/0.61    ~r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl6_2),
% 1.87/0.61    inference(extensionality_resolution,[],[f75,f86])).
% 1.87/0.61  fof(f86,plain,(
% 1.87/0.61    sK1 != sK2 | spl6_2),
% 1.87/0.61    inference(avatar_component_clause,[],[f85])).
% 1.87/0.61  fof(f85,plain,(
% 1.87/0.61    spl6_2 <=> sK1 = sK2),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.87/0.61  fof(f75,plain,(
% 1.87/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.87/0.61    inference(equality_resolution,[],[f70])).
% 1.87/0.61  fof(f70,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.87/0.61    inference(definition_unfolding,[],[f44,f62])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f327,plain,(
% 1.87/0.61    r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl6_1),
% 1.87/0.61    inference(superposition,[],[f39,f325])).
% 1.87/0.61  fof(f325,plain,(
% 1.87/0.61    sK2 = sK3(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl6_1),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f324])).
% 1.87/0.61  fof(f324,plain,(
% 1.87/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 = sK3(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl6_1),
% 1.87/0.61    inference(superposition,[],[f83,f175])).
% 1.87/0.61  % (6458)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.87/0.61  fof(f175,plain,(
% 1.87/0.61    ( ! [X10,X11] : (k5_xboole_0(X10,k3_xboole_0(X10,k3_enumset1(X11,X11,X11,X11,X11))) = X10 | sK3(X10,k3_enumset1(X11,X11,X11,X11,X11)) = X11) )),
% 1.87/0.61    inference(resolution,[],[f112,f66])).
% 1.87/0.61  fof(f112,plain,(
% 1.87/0.61    ( ! [X2,X3] : (r1_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)) | sK3(X3,k3_enumset1(X2,X2,X2,X2,X2)) = X2) )),
% 1.87/0.61    inference(resolution,[],[f75,f40])).
% 1.87/0.61  fof(f40,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f22])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f22])).
% 1.87/0.61  fof(f94,plain,(
% 1.87/0.61    spl6_3 | ~spl6_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f89,f85,f91])).
% 1.87/0.61  fof(f89,plain,(
% 1.87/0.61    sK1 != sK2 | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.87/0.61    inference(inner_rewriting,[],[f64])).
% 1.87/0.61  fof(f64,plain,(
% 1.87/0.61    sK1 != sK2 | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.87/0.61    inference(definition_unfolding,[],[f34,f62,f38,f62,f62])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.87/0.61    inference(cnf_transformation,[],[f20])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    (sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) & (sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) & (sK1 != sK2 | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f18,plain,(
% 1.87/0.61    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.87/0.61    inference(nnf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,plain,(
% 1.87/0.61    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.87/0.61    inference(negated_conjecture,[],[f10])).
% 1.87/0.61  fof(f10,conjecture,(
% 1.87/0.61    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.87/0.61  fof(f88,plain,(
% 1.87/0.61    ~spl6_1 | spl6_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f63,f85,f81])).
% 1.87/0.61  fof(f63,plain,(
% 1.87/0.61    sK1 = sK2 | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.87/0.61    inference(definition_unfolding,[],[f35,f62,f38,f62,f62])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    sK1 = sK2 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.87/0.61    inference(cnf_transformation,[],[f20])).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (6447)------------------------------
% 1.87/0.61  % (6447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (6447)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (6447)Memory used [KB]: 11001
% 1.87/0.61  % (6447)Time elapsed: 0.150 s
% 1.87/0.61  % (6447)------------------------------
% 1.87/0.61  % (6447)------------------------------
% 1.87/0.61  % (6458)Refutation not found, incomplete strategy% (6458)------------------------------
% 1.87/0.61  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (6440)Success in time 0.244 s
%------------------------------------------------------------------------------
