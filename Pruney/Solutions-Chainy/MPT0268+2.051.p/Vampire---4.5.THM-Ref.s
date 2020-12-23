%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:43 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 249 expanded)
%              Number of leaves         :   20 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (1140 expanded)
%              Number of equality atoms :  142 ( 422 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f874,f878,f886,f914])).

fof(f914,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f911,f895])).

fof(f895,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(sK0,k3_enumset1(X0,X0,X0,X1,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f86,f99,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f99,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
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
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f911,plain,
    ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl6_1 ),
    inference(superposition,[],[f72,f94])).

fof(f94,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f886,plain,
    ( ~ spl6_4
    | spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f299,f97,f93,f191])).

fof(f191,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f299,plain,
    ( ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f104,f183,f48])).

fof(f183,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f182,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f182,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0)
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(superposition,[],[f134,f71])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f134,plain,
    ( ! [X0] :
        ( sK0 != k5_xboole_0(sK0,X0)
        | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0)
        | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0) )
    | spl6_1 ),
    inference(superposition,[],[f95,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f104,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f98,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f878,plain,
    ( spl6_3
    | spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f877,f93,f191,f187])).

fof(f187,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f877,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f444,f86])).

fof(f444,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | spl6_1 ),
    inference(superposition,[],[f161,f71])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k5_xboole_0(sK0,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1) )
    | spl6_1 ),
    inference(superposition,[],[f118,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,
    ( ~ r2_hidden(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f95,f95,f95,f91])).

fof(f91,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f874,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f818,f852])).

fof(f852,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),X0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f836,f71])).

fof(f836,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f72,f316,f48])).

fof(f316,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f189,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f189,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f187])).

fof(f818,plain,
    ( r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f189,f316,f82])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f97,f93])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f38,f45,f68])).

fof(f38,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f100,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f69,f97,f93])).

fof(f69,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f39,f45,f68])).

fof(f39,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (8631)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (8647)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (8624)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (8631)Refutation not found, incomplete strategy% (8631)------------------------------
% 0.20/0.51  % (8631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8631)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8631)Memory used [KB]: 10618
% 0.20/0.51  % (8631)Time elapsed: 0.102 s
% 0.20/0.51  % (8631)------------------------------
% 0.20/0.51  % (8631)------------------------------
% 0.20/0.51  % (8632)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (8636)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (8632)Refutation not found, incomplete strategy% (8632)------------------------------
% 0.20/0.52  % (8632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8632)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8632)Memory used [KB]: 10618
% 0.20/0.52  % (8632)Time elapsed: 0.119 s
% 0.20/0.52  % (8632)------------------------------
% 0.20/0.52  % (8632)------------------------------
% 0.20/0.52  % (8637)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (8633)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (8639)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (8628)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (8626)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (8648)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (8622)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (8621)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (8629)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (8650)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (8645)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (8640)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (8627)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (8644)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (8642)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (8623)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (8623)Refutation not found, incomplete strategy% (8623)------------------------------
% 0.20/0.53  % (8623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8623)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8623)Memory used [KB]: 10618
% 0.20/0.53  % (8623)Time elapsed: 0.125 s
% 0.20/0.53  % (8623)------------------------------
% 0.20/0.53  % (8623)------------------------------
% 0.20/0.54  % (8625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (8635)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (8646)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (8634)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (8643)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (8638)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (8629)Refutation not found, incomplete strategy% (8629)------------------------------
% 0.20/0.55  % (8629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8629)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8629)Memory used [KB]: 10618
% 0.20/0.55  % (8629)Time elapsed: 0.150 s
% 0.20/0.55  % (8629)------------------------------
% 0.20/0.55  % (8629)------------------------------
% 0.20/0.55  % (8649)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (8630)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (8641)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.71/0.60  % (8647)Refutation found. Thanks to Tanya!
% 1.71/0.60  % SZS status Theorem for theBenchmark
% 1.71/0.60  % SZS output start Proof for theBenchmark
% 1.71/0.60  fof(f915,plain,(
% 1.71/0.60    $false),
% 1.71/0.60    inference(avatar_sat_refutation,[],[f100,f101,f874,f878,f886,f914])).
% 1.71/0.60  fof(f914,plain,(
% 1.71/0.60    ~spl6_1 | ~spl6_2),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f913])).
% 1.71/0.60  fof(f913,plain,(
% 1.71/0.60    $false | (~spl6_1 | ~spl6_2)),
% 1.71/0.60    inference(subsumption_resolution,[],[f911,f895])).
% 1.71/0.61  fof(f895,plain,(
% 1.71/0.61    ( ! [X0,X1] : (~r1_xboole_0(sK0,k3_enumset1(X0,X0,X0,X1,sK1))) ) | ~spl6_2),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f86,f99,f48])).
% 1.71/0.61  fof(f48,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f27])).
% 1.71/0.61  fof(f27,plain,(
% 1.71/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).
% 1.71/0.61  fof(f26,plain,(
% 1.71/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f18,plain,(
% 1.71/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.71/0.61    inference(ennf_transformation,[],[f15])).
% 1.71/0.61  fof(f15,plain,(
% 1.71/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.71/0.61    inference(rectify,[],[f2])).
% 1.71/0.61  fof(f2,axiom,(
% 1.71/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.71/0.61  fof(f99,plain,(
% 1.71/0.61    r2_hidden(sK1,sK0) | ~spl6_2),
% 1.71/0.61    inference(avatar_component_clause,[],[f97])).
% 1.71/0.61  fof(f97,plain,(
% 1.71/0.61    spl6_2 <=> r2_hidden(sK1,sK0)),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.71/0.61  fof(f86,plain,(
% 1.71/0.61    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 1.71/0.61    inference(equality_resolution,[],[f85])).
% 1.71/0.61  fof(f85,plain,(
% 1.71/0.61    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 1.71/0.61    inference(equality_resolution,[],[f78])).
% 1.71/0.61  fof(f78,plain,(
% 1.71/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.71/0.61    inference(definition_unfolding,[],[f61,f66])).
% 1.71/0.61  fof(f66,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f50,f57])).
% 1.71/0.61  fof(f57,plain,(
% 1.71/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f11])).
% 1.71/0.61  fof(f11,axiom,(
% 1.71/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.71/0.61  fof(f50,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f10])).
% 1.71/0.61  fof(f10,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.71/0.61  fof(f61,plain,(
% 1.71/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.71/0.61    inference(cnf_transformation,[],[f37])).
% 1.71/0.61  fof(f37,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.71/0.61  fof(f36,plain,(
% 1.71/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f35,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.71/0.61    inference(rectify,[],[f34])).
% 1.71/0.61  fof(f34,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.71/0.61    inference(flattening,[],[f33])).
% 1.71/0.61  fof(f33,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.71/0.61    inference(nnf_transformation,[],[f20])).
% 1.71/0.61  fof(f20,plain,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.71/0.61    inference(ennf_transformation,[],[f7])).
% 1.71/0.61  fof(f7,axiom,(
% 1.71/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.71/0.61  fof(f911,plain,(
% 1.71/0.61    r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl6_1),
% 1.71/0.61    inference(superposition,[],[f72,f94])).
% 1.71/0.61  fof(f94,plain,(
% 1.71/0.61    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl6_1),
% 1.71/0.61    inference(avatar_component_clause,[],[f93])).
% 1.71/0.61  fof(f93,plain,(
% 1.71/0.61    spl6_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.71/0.61  fof(f72,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f43,f45])).
% 1.71/0.61  fof(f45,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.61    inference(cnf_transformation,[],[f4])).
% 1.71/0.61  fof(f4,axiom,(
% 1.71/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.61  fof(f43,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f6])).
% 1.71/0.61  fof(f6,axiom,(
% 1.71/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.71/0.61  fof(f886,plain,(
% 1.71/0.61    ~spl6_4 | spl6_1 | spl6_2),
% 1.71/0.61    inference(avatar_split_clause,[],[f299,f97,f93,f191])).
% 1.71/0.61  fof(f191,plain,(
% 1.71/0.61    spl6_4 <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.71/0.61  fof(f299,plain,(
% 1.71/0.61    ~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl6_1 | spl6_2)),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f104,f183,f48])).
% 1.71/0.61  fof(f183,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | spl6_1),
% 1.71/0.61    inference(subsumption_resolution,[],[f182,f84])).
% 1.71/0.61  fof(f84,plain,(
% 1.71/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.71/0.61    inference(equality_resolution,[],[f51])).
% 1.71/0.61  fof(f51,plain,(
% 1.71/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.71/0.61    inference(cnf_transformation,[],[f32])).
% 1.71/0.61  fof(f32,plain,(
% 1.71/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.71/0.61  fof(f31,plain,(
% 1.71/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f30,plain,(
% 1.71/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.71/0.61    inference(rectify,[],[f29])).
% 1.71/0.61  fof(f29,plain,(
% 1.71/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.71/0.61    inference(flattening,[],[f28])).
% 1.71/0.61  fof(f28,plain,(
% 1.71/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.71/0.61    inference(nnf_transformation,[],[f1])).
% 1.71/0.61  fof(f1,axiom,(
% 1.71/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.71/0.61  fof(f182,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl6_1),
% 1.71/0.61    inference(trivial_inequality_removal,[],[f181])).
% 1.71/0.61  fof(f181,plain,(
% 1.71/0.61    sK0 != sK0 | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),sK0) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl6_1),
% 1.71/0.61    inference(superposition,[],[f134,f71])).
% 1.71/0.61  fof(f71,plain,(
% 1.71/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.71/0.61    inference(definition_unfolding,[],[f40,f45])).
% 1.71/0.61  fof(f40,plain,(
% 1.71/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.61    inference(cnf_transformation,[],[f5])).
% 1.71/0.61  fof(f5,axiom,(
% 1.71/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.71/0.61  fof(f134,plain,(
% 1.71/0.61    ( ! [X0] : (sK0 != k5_xboole_0(sK0,X0) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0)) ) | spl6_1),
% 1.71/0.61    inference(superposition,[],[f95,f54])).
% 1.71/0.61  fof(f54,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f32])).
% 1.71/0.61  fof(f95,plain,(
% 1.71/0.61    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl6_1),
% 1.71/0.61    inference(avatar_component_clause,[],[f93])).
% 1.71/0.61  fof(f104,plain,(
% 1.71/0.61    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl6_2),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f98,f73])).
% 1.71/0.61  fof(f73,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f49,f68])).
% 1.71/0.61  fof(f68,plain,(
% 1.71/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f41,f67])).
% 1.71/0.61  fof(f67,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.71/0.61    inference(definition_unfolding,[],[f44,f66])).
% 1.71/0.61  fof(f44,plain,(
% 1.71/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f9])).
% 1.71/0.61  fof(f9,axiom,(
% 1.71/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.71/0.61  fof(f41,plain,(
% 1.71/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f8])).
% 1.71/0.61  fof(f8,axiom,(
% 1.71/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.71/0.61  fof(f49,plain,(
% 1.71/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f19])).
% 1.71/0.61  fof(f19,plain,(
% 1.71/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.71/0.61    inference(ennf_transformation,[],[f12])).
% 1.71/0.61  fof(f12,axiom,(
% 1.71/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.71/0.61  fof(f98,plain,(
% 1.71/0.61    ~r2_hidden(sK1,sK0) | spl6_2),
% 1.71/0.61    inference(avatar_component_clause,[],[f97])).
% 1.71/0.61  fof(f878,plain,(
% 1.71/0.61    spl6_3 | spl6_4 | spl6_1),
% 1.71/0.61    inference(avatar_split_clause,[],[f877,f93,f191,f187])).
% 1.71/0.61  fof(f187,plain,(
% 1.71/0.61    spl6_3 <=> r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0))),
% 1.71/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.71/0.61  fof(f877,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl6_1),
% 1.71/0.61    inference(subsumption_resolution,[],[f444,f86])).
% 1.71/0.61  fof(f444,plain,(
% 1.71/0.61    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | spl6_1),
% 1.71/0.61    inference(superposition,[],[f161,f71])).
% 1.71/0.61  fof(f161,plain,(
% 1.71/0.61    ( ! [X1] : (~r2_hidden(k5_xboole_0(sK0,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1)) ) | spl6_1),
% 1.71/0.61    inference(superposition,[],[f118,f55])).
% 1.71/0.61  fof(f55,plain,(
% 1.71/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.71/0.61    inference(cnf_transformation,[],[f32])).
% 1.71/0.61  fof(f118,plain,(
% 1.71/0.61    ~r2_hidden(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl6_1),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f95,f95,f95,f91])).
% 1.71/0.61  fof(f91,plain,(
% 1.71/0.61    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.71/0.61    inference(equality_resolution,[],[f81])).
% 1.71/0.61  fof(f81,plain,(
% 1.71/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.71/0.61    inference(definition_unfolding,[],[f58,f66])).
% 1.71/0.61  fof(f58,plain,(
% 1.71/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.71/0.61    inference(cnf_transformation,[],[f37])).
% 1.71/0.61  fof(f874,plain,(
% 1.71/0.61    ~spl6_3),
% 1.71/0.61    inference(avatar_contradiction_clause,[],[f873])).
% 1.71/0.61  fof(f873,plain,(
% 1.71/0.61    $false | ~spl6_3),
% 1.71/0.61    inference(subsumption_resolution,[],[f818,f852])).
% 1.71/0.61  fof(f852,plain,(
% 1.71/0.61    ( ! [X0] : (~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),X0)) ) | ~spl6_3),
% 1.71/0.61    inference(forward_demodulation,[],[f836,f71])).
% 1.71/0.61  fof(f836,plain,(
% 1.71/0.61    ( ! [X0] : (~r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) ) | ~spl6_3),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f72,f316,f48])).
% 1.71/0.61  fof(f316,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_3),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f189,f83])).
% 1.71/0.61  fof(f83,plain,(
% 1.71/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.71/0.61    inference(equality_resolution,[],[f52])).
% 1.71/0.61  fof(f52,plain,(
% 1.71/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.71/0.61    inference(cnf_transformation,[],[f32])).
% 1.71/0.61  fof(f189,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(sK0,k1_xboole_0)) | ~spl6_3),
% 1.71/0.61    inference(avatar_component_clause,[],[f187])).
% 1.71/0.61  fof(f818,plain,(
% 1.71/0.61    r2_hidden(sK4(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0))) | ~spl6_3),
% 1.71/0.61    inference(unit_resulting_resolution,[],[f189,f316,f82])).
% 1.71/0.61  fof(f82,plain,(
% 1.71/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.71/0.61    inference(equality_resolution,[],[f53])).
% 1.71/0.61  fof(f53,plain,(
% 1.71/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.71/0.61    inference(cnf_transformation,[],[f32])).
% 1.71/0.61  fof(f101,plain,(
% 1.71/0.61    spl6_1 | ~spl6_2),
% 1.71/0.61    inference(avatar_split_clause,[],[f70,f97,f93])).
% 1.71/0.61  fof(f70,plain,(
% 1.71/0.61    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.71/0.61    inference(definition_unfolding,[],[f38,f45,f68])).
% 1.71/0.61  fof(f38,plain,(
% 1.71/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.71/0.61    inference(cnf_transformation,[],[f23])).
% 1.71/0.61  fof(f23,plain,(
% 1.71/0.61    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.71/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.71/0.61  fof(f22,plain,(
% 1.71/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.71/0.61    introduced(choice_axiom,[])).
% 1.71/0.61  fof(f21,plain,(
% 1.71/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.71/0.61    inference(nnf_transformation,[],[f16])).
% 1.71/0.61  fof(f16,plain,(
% 1.71/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.71/0.61    inference(ennf_transformation,[],[f14])).
% 1.71/0.61  fof(f14,negated_conjecture,(
% 1.71/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.71/0.61    inference(negated_conjecture,[],[f13])).
% 1.71/0.61  fof(f13,conjecture,(
% 1.71/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.71/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.71/0.61  fof(f100,plain,(
% 1.71/0.61    ~spl6_1 | spl6_2),
% 1.71/0.61    inference(avatar_split_clause,[],[f69,f97,f93])).
% 1.71/0.61  fof(f69,plain,(
% 1.71/0.61    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.71/0.61    inference(definition_unfolding,[],[f39,f45,f68])).
% 1.71/0.61  fof(f39,plain,(
% 1.71/0.61    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.71/0.61    inference(cnf_transformation,[],[f23])).
% 1.71/0.61  % SZS output end Proof for theBenchmark
% 1.71/0.61  % (8647)------------------------------
% 1.71/0.61  % (8647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (8647)Termination reason: Refutation
% 1.71/0.61  
% 1.71/0.61  % (8647)Memory used [KB]: 11385
% 1.71/0.61  % (8647)Time elapsed: 0.200 s
% 1.71/0.61  % (8647)------------------------------
% 1.71/0.61  % (8647)------------------------------
% 1.71/0.61  % (8620)Success in time 0.253 s
%------------------------------------------------------------------------------
