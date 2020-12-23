%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:27 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 435 expanded)
%              Number of leaves         :   23 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  312 ( 791 expanded)
%              Number of equality atoms :  170 ( 548 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f136,f780,f801,f851,f859])).

fof(f859,plain,
    ( spl5_1
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | spl5_1
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f112,f112,f112,f848,f108])).

fof(f108,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
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
    inference(rectify,[],[f35])).

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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f848,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f846])).

fof(f846,plain,
    ( spl5_12
  <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f112,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f851,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f841,f797,f846])).

fof(f797,plain,
    ( spl5_10
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f841,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f827,f107])).

fof(f107,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f827,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f815,f288])).

fof(f288,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f274,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f274,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f183])).

fof(f183,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f75,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f87,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f55,f55])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f815,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))
        | r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl5_10 ),
    inference(superposition,[],[f100,f799])).

fof(f799,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f797])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f801,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f784,f777,f797])).

fof(f777,plain,
    ( spl5_9
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

% (7204)Refutation not found, incomplete strategy% (7204)------------------------------
% (7204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7204)Termination reason: Refutation not found, incomplete strategy

% (7204)Memory used [KB]: 1663
% (7204)Time elapsed: 0.128 s
% (7204)------------------------------
% (7204)------------------------------
fof(f784,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_9 ),
    inference(superposition,[],[f681,f779])).

fof(f779,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f777])).

fof(f681,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f657,f59])).

fof(f657,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f329,f320])).

fof(f320,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f311,f288])).

fof(f311,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f73,f292])).

fof(f292,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f183,f288])).

fof(f329,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f58,f320])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f780,plain,
    ( spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f693,f133,f777])).

fof(f133,plain,
    ( spl5_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f693,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f692,f292])).

fof(f692,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f667,f172])).

fof(f172,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f73,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f667,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_3 ),
    inference(superposition,[],[f329,f135])).

fof(f135,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f136,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f74,f133])).

fof(f74,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f39,f72,f43,f72,f72])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f113,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f110])).

fof(f40,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (7181)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (7201)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (7186)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (7193)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (7201)Refutation not found, incomplete strategy% (7201)------------------------------
% 0.22/0.52  % (7201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7201)Memory used [KB]: 6268
% 0.22/0.52  % (7201)Time elapsed: 0.114 s
% 0.22/0.52  % (7201)------------------------------
% 0.22/0.52  % (7201)------------------------------
% 0.22/0.53  % (7193)Refutation not found, incomplete strategy% (7193)------------------------------
% 0.22/0.53  % (7193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7193)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7193)Memory used [KB]: 1663
% 0.22/0.53  % (7193)Time elapsed: 0.112 s
% 0.22/0.53  % (7193)------------------------------
% 0.22/0.53  % (7193)------------------------------
% 0.22/0.53  % (7177)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (7178)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (7176)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (7198)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (7182)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (7195)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (7179)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (7180)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (7202)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (7192)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (7183)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (7175)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (7194)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (7187)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (7185)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (7197)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (7200)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (7184)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (7199)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (7188)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (7204)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.56  % (7190)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.56  % (7191)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.56  % (7189)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.56  % (7189)Refutation not found, incomplete strategy% (7189)------------------------------
% 1.39/0.56  % (7189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (7189)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (7189)Memory used [KB]: 1663
% 1.39/0.56  % (7189)Time elapsed: 0.128 s
% 1.39/0.56  % (7189)------------------------------
% 1.39/0.56  % (7189)------------------------------
% 1.39/0.56  % (7191)Refutation not found, incomplete strategy% (7191)------------------------------
% 1.39/0.56  % (7191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (7191)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (7191)Memory used [KB]: 10618
% 1.39/0.56  % (7191)Time elapsed: 0.157 s
% 1.39/0.56  % (7191)------------------------------
% 1.39/0.56  % (7191)------------------------------
% 1.39/0.57  % (7196)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.57  % (7198)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.58  % (7203)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f860,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(avatar_sat_refutation,[],[f113,f136,f780,f801,f851,f859])).
% 1.64/0.58  fof(f859,plain,(
% 1.64/0.58    spl5_1 | ~spl5_12),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f853])).
% 1.64/0.58  fof(f853,plain,(
% 1.64/0.58    $false | (spl5_1 | ~spl5_12)),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f112,f112,f112,f848,f108])).
% 1.64/0.58  fof(f108,plain,(
% 1.64/0.58    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.64/0.58    inference(equality_resolution,[],[f95])).
% 1.64/0.58  fof(f95,plain,(
% 1.64/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.64/0.58    inference(definition_unfolding,[],[f60,f70])).
% 1.64/0.58  fof(f70,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.64/0.58    inference(cnf_transformation,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.64/0.58    inference(rectify,[],[f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.64/0.58    inference(flattening,[],[f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.64/0.58    inference(nnf_transformation,[],[f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.64/0.58  fof(f848,plain,(
% 1.64/0.58    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_12),
% 1.64/0.58    inference(avatar_component_clause,[],[f846])).
% 1.64/0.58  fof(f846,plain,(
% 1.64/0.58    spl5_12 <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.64/0.58  fof(f112,plain,(
% 1.64/0.58    sK0 != sK1 | spl5_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f110])).
% 1.64/0.58  fof(f110,plain,(
% 1.64/0.58    spl5_1 <=> sK0 = sK1),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.64/0.58  fof(f851,plain,(
% 1.64/0.58    spl5_12 | ~spl5_10),
% 1.64/0.58    inference(avatar_split_clause,[],[f841,f797,f846])).
% 1.64/0.58  fof(f797,plain,(
% 1.64/0.58    spl5_10 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.64/0.58  fof(f841,plain,(
% 1.64/0.58    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_10),
% 1.64/0.58    inference(resolution,[],[f827,f107])).
% 1.64/0.58  fof(f107,plain,(
% 1.64/0.58    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.64/0.58    inference(equality_resolution,[],[f106])).
% 1.64/0.58  fof(f106,plain,(
% 1.64/0.58    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.64/0.58    inference(equality_resolution,[],[f94])).
% 1.64/0.58  fof(f94,plain,(
% 1.64/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.64/0.58    inference(definition_unfolding,[],[f61,f70])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.64/0.58    inference(cnf_transformation,[],[f38])).
% 1.64/0.58  fof(f827,plain,(
% 1.64/0.58    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl5_10),
% 1.64/0.58    inference(forward_demodulation,[],[f815,f288])).
% 1.64/0.58  fof(f288,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.58    inference(forward_demodulation,[],[f274,f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.64/0.58  fof(f274,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(superposition,[],[f73,f183])).
% 1.64/0.58  fof(f183,plain,(
% 1.64/0.58    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))) )),
% 1.64/0.58    inference(superposition,[],[f75,f114])).
% 1.64/0.58  fof(f114,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.64/0.58    inference(resolution,[],[f87,f69])).
% 1.64/0.58  fof(f69,plain,(
% 1.64/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.64/0.58    inference(ennf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.64/0.58  fof(f87,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f57,f55])).
% 1.64/0.58  fof(f55,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.64/0.58  fof(f75,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f41,f55,f55])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.64/0.58  fof(f73,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f56,f55])).
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.64/0.58  fof(f815,plain,(
% 1.64/0.58    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)) | r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl5_10),
% 1.64/0.58    inference(superposition,[],[f100,f799])).
% 1.64/0.58  fof(f799,plain,(
% 1.64/0.58    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_10),
% 1.64/0.58    inference(avatar_component_clause,[],[f797])).
% 1.64/0.58  fof(f100,plain,(
% 1.64/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X4,X1)) )),
% 1.64/0.58    inference(equality_resolution,[],[f85])).
% 1.64/0.58  fof(f85,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.64/0.58    inference(definition_unfolding,[],[f50,f55])).
% 1.64/0.58  fof(f50,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.64/0.58    inference(cnf_transformation,[],[f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.58    inference(rectify,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.58    inference(flattening,[],[f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.58    inference(nnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.64/0.58  fof(f801,plain,(
% 1.64/0.58    spl5_10 | ~spl5_9),
% 1.64/0.58    inference(avatar_split_clause,[],[f784,f777,f797])).
% 1.64/0.58  fof(f777,plain,(
% 1.64/0.58    spl5_9 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.64/0.58  % (7204)Refutation not found, incomplete strategy% (7204)------------------------------
% 1.64/0.58  % (7204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (7204)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (7204)Memory used [KB]: 1663
% 1.64/0.58  % (7204)Time elapsed: 0.128 s
% 1.64/0.58  % (7204)------------------------------
% 1.64/0.58  % (7204)------------------------------
% 1.64/0.58  fof(f784,plain,(
% 1.64/0.58    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_9),
% 1.64/0.58    inference(superposition,[],[f681,f779])).
% 1.64/0.58  fof(f779,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_9),
% 1.64/0.58    inference(avatar_component_clause,[],[f777])).
% 1.64/0.58  fof(f681,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.64/0.58    inference(forward_demodulation,[],[f657,f59])).
% 1.64/0.58  fof(f657,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.64/0.58    inference(superposition,[],[f329,f320])).
% 1.64/0.58  fof(f320,plain,(
% 1.64/0.58    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f311,f288])).
% 1.64/0.58  fof(f311,plain,(
% 1.64/0.58    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))) )),
% 1.64/0.58    inference(superposition,[],[f73,f292])).
% 1.64/0.58  fof(f292,plain,(
% 1.64/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.64/0.58    inference(superposition,[],[f183,f288])).
% 1.64/0.58  fof(f329,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 1.64/0.58    inference(superposition,[],[f58,f320])).
% 1.64/0.58  fof(f58,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.64/0.58  fof(f780,plain,(
% 1.64/0.58    spl5_9 | ~spl5_3),
% 1.64/0.58    inference(avatar_split_clause,[],[f693,f133,f777])).
% 1.64/0.58  fof(f133,plain,(
% 1.64/0.58    spl5_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.64/0.58  fof(f693,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_3),
% 1.64/0.58    inference(forward_demodulation,[],[f692,f292])).
% 1.64/0.58  fof(f692,plain,(
% 1.64/0.58    k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_3),
% 1.64/0.58    inference(forward_demodulation,[],[f667,f172])).
% 1.64/0.58  fof(f172,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.64/0.58    inference(superposition,[],[f73,f76])).
% 1.64/0.58  fof(f76,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.64/0.58    inference(definition_unfolding,[],[f42,f55])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.64/0.58    inference(rectify,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.64/0.58  fof(f667,plain,(
% 1.64/0.58    k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_3),
% 1.64/0.58    inference(superposition,[],[f329,f135])).
% 1.64/0.58  fof(f135,plain,(
% 1.64/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_3),
% 1.64/0.58    inference(avatar_component_clause,[],[f133])).
% 1.64/0.58  fof(f136,plain,(
% 1.64/0.58    spl5_3),
% 1.64/0.58    inference(avatar_split_clause,[],[f74,f133])).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.64/0.58    inference(definition_unfolding,[],[f39,f72,f43,f72,f72])).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.64/0.58  fof(f72,plain,(
% 1.64/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f48,f71])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f68,f70])).
% 1.64/0.58  fof(f68,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,axiom,(
% 1.64/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.58  fof(f48,plain,(
% 1.64/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.64/0.58    inference(ennf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.64/0.58    inference(negated_conjecture,[],[f17])).
% 1.64/0.58  fof(f17,conjecture,(
% 1.64/0.58    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.64/0.58  fof(f113,plain,(
% 1.64/0.58    ~spl5_1),
% 1.64/0.58    inference(avatar_split_clause,[],[f40,f110])).
% 1.64/0.58  fof(f40,plain,(
% 1.64/0.58    sK0 != sK1),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (7198)------------------------------
% 1.64/0.58  % (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (7198)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (7198)Memory used [KB]: 11257
% 1.64/0.58  % (7198)Time elapsed: 0.140 s
% 1.64/0.58  % (7198)------------------------------
% 1.64/0.58  % (7198)------------------------------
% 1.64/0.58  % (7174)Success in time 0.22 s
%------------------------------------------------------------------------------
