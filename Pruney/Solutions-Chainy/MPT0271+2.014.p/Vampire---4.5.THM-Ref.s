%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:07 EST 2020

% Result     : Theorem 5.07s
% Output     : Refutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 220 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  357 ( 506 expanded)
%              Number of equality atoms :  163 ( 270 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1746,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f758,f764,f851,f879,f1043,f1094,f1439,f1661,f1745])).

fof(f1745,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1744])).

fof(f1744,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1738,f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1738,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_15 ),
    inference(resolution,[],[f1688,f119])).

fof(f119,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f104,f64])).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f80,f69])).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f80,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1688,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_15 ),
    inference(superposition,[],[f82,f1633])).

fof(f1633,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f1631,plain,
    ( spl4_15
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1661,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1660,f1436,f1631])).

fof(f1436,plain,
    ( spl4_10
  <=> k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1660,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f1603,f189])).

fof(f189,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f141,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f141,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f124,f96])).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f61,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f124,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f60,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1603,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_10 ),
    inference(superposition,[],[f235,f1438])).

fof(f1438,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f235,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f189,f189])).

fof(f1439,plain,
    ( spl4_10
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1434,f1091,f1040,f1436])).

fof(f1040,plain,
    ( spl4_8
  <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1091,plain,
    ( spl4_9
  <=> k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1434,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1093,f1042])).

fof(f1042,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1093,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f1094,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1089,f864,f1091])).

fof(f864,plain,
    ( spl4_5
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1089,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1054,f866])).

fof(f866,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f864])).

fof(f1054,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f147,f866])).

fof(f147,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k5_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f71,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f1043,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1038,f864,f1040])).

fof(f1038,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f63,f866])).

fof(f879,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f860,f848,f864])).

fof(f848,plain,
    ( spl4_4
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f860,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f601,f850])).

fof(f850,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f848])).

fof(f601,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(superposition,[],[f153,f145])).

fof(f145,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f71,f61])).

fof(f153,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f71,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f851,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f846,f86,f848])).

fof(f86,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f846,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f825,f66])).

fof(f825,plain,
    ( k3_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f191,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f191,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f141,f63])).

fof(f764,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f760,f755,f90])).

fof(f755,plain,
    ( spl4_3
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f760,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f757,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f757,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f755])).

fof(f758,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f753,f86,f755])).

fof(f753,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f751])).

fof(f751,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f88,f577])).

fof(f577,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f576,f67])).

fof(f576,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,X3) = k4_xboole_0(X3,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f63,f570])).

fof(f570,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f569,f141])).

fof(f569,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = k5_xboole_0(X3,k5_xboole_0(X3,X2))
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f540,f61])).

fof(f540,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f145,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f88,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f94,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f42,f90,f86])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f93,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f90,f86])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22399)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (22416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (22403)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (22409)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22407)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (22398)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (22420)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (22412)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (22412)Refutation not found, incomplete strategy% (22412)------------------------------
% 0.21/0.54  % (22412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22412)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22412)Memory used [KB]: 6140
% 0.21/0.54  % (22412)Time elapsed: 0.004 s
% 0.21/0.54  % (22412)------------------------------
% 0.21/0.54  % (22412)------------------------------
% 0.21/0.54  % (22400)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (22421)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22404)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (22401)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22397)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (22406)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (22423)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (22424)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (22415)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (22414)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22425)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (22414)Refutation not found, incomplete strategy% (22414)------------------------------
% 0.21/0.55  % (22414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22414)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22414)Memory used [KB]: 10618
% 0.21/0.55  % (22414)Time elapsed: 0.137 s
% 0.21/0.55  % (22414)------------------------------
% 0.21/0.55  % (22414)------------------------------
% 0.21/0.55  % (22410)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (22413)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (22411)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (22417)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (22426)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (22405)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (22408)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (22418)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (22402)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (22422)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.60  % (22419)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.17/0.65  % (22405)Refutation not found, incomplete strategy% (22405)------------------------------
% 2.17/0.65  % (22405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (22405)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.65  
% 2.17/0.65  % (22405)Memory used [KB]: 11257
% 2.17/0.65  % (22405)Time elapsed: 0.219 s
% 2.17/0.65  % (22405)------------------------------
% 2.17/0.65  % (22405)------------------------------
% 2.86/0.74  % (22430)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.86/0.79  % (22431)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.78/0.89  % (22402)Time limit reached!
% 3.78/0.89  % (22402)------------------------------
% 3.78/0.89  % (22402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.89  % (22402)Termination reason: Time limit
% 3.78/0.89  
% 3.78/0.89  % (22402)Memory used [KB]: 8955
% 3.78/0.89  % (22402)Time elapsed: 0.448 s
% 3.78/0.89  % (22402)------------------------------
% 3.78/0.89  % (22402)------------------------------
% 3.78/0.89  % (22456)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.16/0.91  % (22397)Time limit reached!
% 4.16/0.91  % (22397)------------------------------
% 4.16/0.91  % (22397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (22397)Termination reason: Time limit
% 4.16/0.91  % (22397)Termination phase: Saturation
% 4.16/0.91  
% 4.16/0.91  % (22397)Memory used [KB]: 2430
% 4.16/0.91  % (22397)Time elapsed: 0.500 s
% 4.16/0.91  % (22397)------------------------------
% 4.16/0.91  % (22397)------------------------------
% 4.16/0.92  % (22409)Time limit reached!
% 4.16/0.92  % (22409)------------------------------
% 4.16/0.92  % (22409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.92  % (22409)Termination reason: Time limit
% 4.16/0.92  % (22409)Termination phase: Saturation
% 4.16/0.92  
% 4.16/0.92  % (22409)Memory used [KB]: 9978
% 4.16/0.92  % (22409)Time elapsed: 0.500 s
% 4.16/0.92  % (22409)------------------------------
% 4.16/0.92  % (22409)------------------------------
% 4.16/0.93  % (22398)Time limit reached!
% 4.16/0.93  % (22398)------------------------------
% 4.16/0.93  % (22398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.93  % (22398)Termination reason: Time limit
% 4.16/0.93  
% 4.16/0.93  % (22398)Memory used [KB]: 7291
% 4.16/0.93  % (22398)Time elapsed: 0.514 s
% 4.16/0.93  % (22398)------------------------------
% 4.16/0.93  % (22398)------------------------------
% 4.16/0.93  % (22407)Time limit reached!
% 4.16/0.93  % (22407)------------------------------
% 4.16/0.93  % (22407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.94  % (22407)Termination reason: Time limit
% 4.16/0.94  
% 4.16/0.94  % (22407)Memory used [KB]: 13688
% 4.16/0.94  % (22407)Time elapsed: 0.519 s
% 4.16/0.94  % (22407)------------------------------
% 4.16/0.94  % (22407)------------------------------
% 4.47/1.02  % (22425)Time limit reached!
% 4.47/1.02  % (22425)------------------------------
% 4.47/1.02  % (22425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.02  % (22425)Termination reason: Time limit
% 4.47/1.02  
% 4.47/1.02  % (22425)Memory used [KB]: 7291
% 4.47/1.02  % (22425)Time elapsed: 0.608 s
% 4.47/1.02  % (22425)------------------------------
% 4.47/1.02  % (22425)------------------------------
% 5.07/1.05  % (22413)Time limit reached!
% 5.07/1.05  % (22413)------------------------------
% 5.07/1.05  % (22413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.05  % (22413)Termination reason: Time limit
% 5.07/1.05  
% 5.07/1.05  % (22413)Memory used [KB]: 13944
% 5.07/1.05  % (22413)Time elapsed: 0.636 s
% 5.07/1.05  % (22413)------------------------------
% 5.07/1.05  % (22413)------------------------------
% 5.07/1.05  % (22456)Refutation found. Thanks to Tanya!
% 5.07/1.05  % SZS status Theorem for theBenchmark
% 5.07/1.06  % (22457)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.07/1.07  % SZS output start Proof for theBenchmark
% 5.07/1.07  fof(f1746,plain,(
% 5.07/1.07    $false),
% 5.07/1.07    inference(avatar_sat_refutation,[],[f93,f94,f758,f764,f851,f879,f1043,f1094,f1439,f1661,f1745])).
% 5.07/1.07  fof(f1745,plain,(
% 5.07/1.07    spl4_2 | ~spl4_15),
% 5.07/1.07    inference(avatar_contradiction_clause,[],[f1744])).
% 5.07/1.07  fof(f1744,plain,(
% 5.07/1.07    $false | (spl4_2 | ~spl4_15)),
% 5.07/1.07    inference(subsumption_resolution,[],[f1738,f92])).
% 5.07/1.07  fof(f92,plain,(
% 5.07/1.07    ~r2_hidden(sK0,sK1) | spl4_2),
% 5.07/1.07    inference(avatar_component_clause,[],[f90])).
% 5.07/1.07  fof(f90,plain,(
% 5.07/1.07    spl4_2 <=> r2_hidden(sK0,sK1)),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 5.07/1.07  fof(f1738,plain,(
% 5.07/1.07    r2_hidden(sK0,sK1) | ~spl4_15),
% 5.07/1.07    inference(resolution,[],[f1688,f119])).
% 5.07/1.07  fof(f119,plain,(
% 5.07/1.07    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 5.07/1.07    inference(superposition,[],[f104,f64])).
% 5.07/1.07  fof(f64,plain,(
% 5.07/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f12])).
% 5.07/1.07  fof(f12,axiom,(
% 5.07/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 5.07/1.07  fof(f104,plain,(
% 5.07/1.07    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 5.07/1.07    inference(superposition,[],[f80,f69])).
% 5.07/1.07  fof(f69,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f13])).
% 5.07/1.07  fof(f13,axiom,(
% 5.07/1.07    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.07/1.07  fof(f80,plain,(
% 5.07/1.07    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 5.07/1.07    inference(equality_resolution,[],[f79])).
% 5.07/1.07  fof(f79,plain,(
% 5.07/1.07    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 5.07/1.07    inference(equality_resolution,[],[f45])).
% 5.07/1.07  fof(f45,plain,(
% 5.07/1.07    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.07/1.07    inference(cnf_transformation,[],[f35])).
% 5.07/1.07  fof(f35,plain,(
% 5.07/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.07/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 5.07/1.07  fof(f34,plain,(
% 5.07/1.07    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 5.07/1.07    introduced(choice_axiom,[])).
% 5.07/1.07  fof(f33,plain,(
% 5.07/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.07/1.07    inference(rectify,[],[f32])).
% 5.07/1.07  fof(f32,plain,(
% 5.07/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.07/1.07    inference(flattening,[],[f31])).
% 5.07/1.07  fof(f31,plain,(
% 5.07/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.07/1.07    inference(nnf_transformation,[],[f26])).
% 5.07/1.07  fof(f26,plain,(
% 5.07/1.07    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 5.07/1.07    inference(ennf_transformation,[],[f11])).
% 5.07/1.07  fof(f11,axiom,(
% 5.07/1.07    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 5.07/1.07  fof(f1688,plain,(
% 5.07/1.07    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1)) ) | ~spl4_15),
% 5.07/1.07    inference(superposition,[],[f82,f1633])).
% 5.07/1.07  fof(f1633,plain,(
% 5.07/1.07    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_15),
% 5.07/1.07    inference(avatar_component_clause,[],[f1631])).
% 5.07/1.07  fof(f1631,plain,(
% 5.07/1.07    spl4_15 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 5.07/1.07  fof(f82,plain,(
% 5.07/1.07    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.07/1.07    inference(equality_resolution,[],[f54])).
% 5.07/1.07  fof(f54,plain,(
% 5.07/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 5.07/1.07    inference(cnf_transformation,[],[f40])).
% 5.07/1.07  fof(f40,plain,(
% 5.07/1.07    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.07/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 5.07/1.07  fof(f39,plain,(
% 5.07/1.07    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 5.07/1.07    introduced(choice_axiom,[])).
% 5.07/1.07  fof(f38,plain,(
% 5.07/1.07    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.07/1.07    inference(rectify,[],[f37])).
% 5.07/1.07  fof(f37,plain,(
% 5.07/1.07    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.07/1.07    inference(flattening,[],[f36])).
% 5.07/1.07  fof(f36,plain,(
% 5.07/1.07    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 5.07/1.07    inference(nnf_transformation,[],[f3])).
% 5.07/1.07  fof(f3,axiom,(
% 5.07/1.07    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 5.07/1.07  fof(f1661,plain,(
% 5.07/1.07    spl4_15 | ~spl4_10),
% 5.07/1.07    inference(avatar_split_clause,[],[f1660,f1436,f1631])).
% 5.07/1.07  fof(f1436,plain,(
% 5.07/1.07    spl4_10 <=> k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 5.07/1.07  fof(f1660,plain,(
% 5.07/1.07    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_10),
% 5.07/1.07    inference(forward_demodulation,[],[f1603,f189])).
% 5.07/1.07  fof(f189,plain,(
% 5.07/1.07    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.07/1.07    inference(superposition,[],[f141,f61])).
% 5.07/1.07  fof(f61,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f2])).
% 5.07/1.07  fof(f2,axiom,(
% 5.07/1.07    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.07/1.07  fof(f141,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.07/1.07    inference(forward_demodulation,[],[f124,f96])).
% 5.07/1.07  fof(f96,plain,(
% 5.07/1.07    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.07/1.07    inference(superposition,[],[f61,f66])).
% 5.07/1.07  fof(f66,plain,(
% 5.07/1.07    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.07/1.07    inference(cnf_transformation,[],[f7])).
% 5.07/1.07  fof(f7,axiom,(
% 5.07/1.07    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.07/1.07  fof(f124,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.07/1.07    inference(superposition,[],[f60,f67])).
% 5.07/1.07  fof(f67,plain,(
% 5.07/1.07    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f9])).
% 5.07/1.07  fof(f9,axiom,(
% 5.07/1.07    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.07/1.07  fof(f60,plain,(
% 5.07/1.07    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.07/1.07    inference(cnf_transformation,[],[f8])).
% 5.07/1.07  fof(f8,axiom,(
% 5.07/1.07    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.07/1.07  fof(f1603,plain,(
% 5.07/1.07    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_10),
% 5.07/1.07    inference(superposition,[],[f235,f1438])).
% 5.07/1.07  fof(f1438,plain,(
% 5.07/1.07    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_10),
% 5.07/1.07    inference(avatar_component_clause,[],[f1436])).
% 5.07/1.07  fof(f235,plain,(
% 5.07/1.07    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 5.07/1.07    inference(superposition,[],[f189,f189])).
% 5.07/1.07  fof(f1439,plain,(
% 5.07/1.07    spl4_10 | ~spl4_8 | ~spl4_9),
% 5.07/1.07    inference(avatar_split_clause,[],[f1434,f1091,f1040,f1436])).
% 5.07/1.07  fof(f1040,plain,(
% 5.07/1.07    spl4_8 <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 5.07/1.07  fof(f1091,plain,(
% 5.07/1.07    spl4_9 <=> k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0)))),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 5.07/1.07  fof(f1434,plain,(
% 5.07/1.07    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) | (~spl4_8 | ~spl4_9)),
% 5.07/1.07    inference(forward_demodulation,[],[f1093,f1042])).
% 5.07/1.07  fof(f1042,plain,(
% 5.07/1.07    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_8),
% 5.07/1.07    inference(avatar_component_clause,[],[f1040])).
% 5.07/1.07  fof(f1093,plain,(
% 5.07/1.07    k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_9),
% 5.07/1.07    inference(avatar_component_clause,[],[f1091])).
% 5.07/1.07  fof(f1094,plain,(
% 5.07/1.07    spl4_9 | ~spl4_5),
% 5.07/1.07    inference(avatar_split_clause,[],[f1089,f864,f1091])).
% 5.07/1.07  fof(f864,plain,(
% 5.07/1.07    spl4_5 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 5.07/1.07  fof(f1089,plain,(
% 5.07/1.07    k1_tarski(sK0) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_5),
% 5.07/1.07    inference(forward_demodulation,[],[f1054,f866])).
% 5.07/1.07  fof(f866,plain,(
% 5.07/1.07    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_5),
% 5.07/1.07    inference(avatar_component_clause,[],[f864])).
% 5.07/1.07  fof(f1054,plain,(
% 5.07/1.07    k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k2_xboole_0(sK1,k1_tarski(sK0))) | ~spl4_5),
% 5.07/1.07    inference(superposition,[],[f147,f866])).
% 5.07/1.07  fof(f147,plain,(
% 5.07/1.07    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k5_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 5.07/1.07    inference(superposition,[],[f71,f63])).
% 5.07/1.07  fof(f63,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.07/1.07    inference(cnf_transformation,[],[f5])).
% 5.07/1.07  fof(f5,axiom,(
% 5.07/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.07/1.07  fof(f71,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.07/1.07    inference(cnf_transformation,[],[f10])).
% 5.07/1.07  fof(f10,axiom,(
% 5.07/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 5.07/1.07  fof(f1043,plain,(
% 5.07/1.07    spl4_8 | ~spl4_5),
% 5.07/1.07    inference(avatar_split_clause,[],[f1038,f864,f1040])).
% 5.07/1.07  fof(f1038,plain,(
% 5.07/1.07    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_5),
% 5.07/1.07    inference(superposition,[],[f63,f866])).
% 5.07/1.07  fof(f879,plain,(
% 5.07/1.07    spl4_5 | ~spl4_4),
% 5.07/1.07    inference(avatar_split_clause,[],[f860,f848,f864])).
% 5.07/1.07  fof(f848,plain,(
% 5.07/1.07    spl4_4 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 5.07/1.07  fof(f860,plain,(
% 5.07/1.07    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 5.07/1.07    inference(superposition,[],[f601,f850])).
% 5.07/1.07  fof(f850,plain,(
% 5.07/1.07    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl4_4),
% 5.07/1.07    inference(avatar_component_clause,[],[f848])).
% 5.07/1.07  fof(f601,plain,(
% 5.07/1.07    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3)) )),
% 5.07/1.07    inference(superposition,[],[f153,f145])).
% 5.07/1.07  fof(f145,plain,(
% 5.07/1.07    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 5.07/1.07    inference(superposition,[],[f71,f61])).
% 5.07/1.07  fof(f153,plain,(
% 5.07/1.07    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 5.07/1.07    inference(superposition,[],[f71,f62])).
% 5.07/1.07  fof(f62,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f1])).
% 5.07/1.07  fof(f1,axiom,(
% 5.07/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.07/1.07  fof(f851,plain,(
% 5.07/1.07    spl4_4 | ~spl4_1),
% 5.07/1.07    inference(avatar_split_clause,[],[f846,f86,f848])).
% 5.07/1.07  fof(f86,plain,(
% 5.07/1.07    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 5.07/1.07  fof(f846,plain,(
% 5.07/1.07    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 5.07/1.07    inference(forward_demodulation,[],[f825,f66])).
% 5.07/1.07  fof(f825,plain,(
% 5.07/1.07    k3_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~spl4_1),
% 5.07/1.07    inference(superposition,[],[f191,f87])).
% 5.07/1.07  fof(f87,plain,(
% 5.07/1.07    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 5.07/1.07    inference(avatar_component_clause,[],[f86])).
% 5.07/1.07  fof(f191,plain,(
% 5.07/1.07    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 5.07/1.07    inference(superposition,[],[f141,f63])).
% 5.07/1.07  fof(f764,plain,(
% 5.07/1.07    ~spl4_2 | spl4_3),
% 5.07/1.07    inference(avatar_split_clause,[],[f760,f755,f90])).
% 5.07/1.07  fof(f755,plain,(
% 5.07/1.07    spl4_3 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 5.07/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 5.07/1.07  fof(f760,plain,(
% 5.07/1.07    ~r2_hidden(sK0,sK1) | spl4_3),
% 5.07/1.07    inference(resolution,[],[f757,f59])).
% 5.07/1.07  fof(f59,plain,(
% 5.07/1.07    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f41])).
% 5.07/1.07  fof(f41,plain,(
% 5.07/1.07    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 5.07/1.07    inference(nnf_transformation,[],[f19])).
% 5.07/1.07  fof(f19,axiom,(
% 5.07/1.07    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 5.07/1.07  fof(f757,plain,(
% 5.07/1.07    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_3),
% 5.07/1.07    inference(avatar_component_clause,[],[f755])).
% 5.07/1.07  fof(f758,plain,(
% 5.07/1.07    ~spl4_3 | spl4_1),
% 5.07/1.07    inference(avatar_split_clause,[],[f753,f86,f755])).
% 5.07/1.07  fof(f753,plain,(
% 5.07/1.07    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.07/1.07    inference(trivial_inequality_removal,[],[f751])).
% 5.07/1.07  fof(f751,plain,(
% 5.07/1.07    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl4_1),
% 5.07/1.07    inference(superposition,[],[f88,f577])).
% 5.07/1.07  fof(f577,plain,(
% 5.07/1.07    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,X4) | ~r1_tarski(X3,X4)) )),
% 5.07/1.07    inference(forward_demodulation,[],[f576,f67])).
% 5.07/1.07  fof(f576,plain,(
% 5.07/1.07    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k4_xboole_0(X3,X4) | ~r1_tarski(X3,X4)) )),
% 5.07/1.07    inference(superposition,[],[f63,f570])).
% 5.07/1.07  fof(f570,plain,(
% 5.07/1.07    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X2 | ~r1_tarski(X2,X3)) )),
% 5.07/1.07    inference(forward_demodulation,[],[f569,f141])).
% 5.07/1.07  fof(f569,plain,(
% 5.07/1.07    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(X3,k5_xboole_0(X3,X2)) | ~r1_tarski(X2,X3)) )),
% 5.07/1.07    inference(forward_demodulation,[],[f540,f61])).
% 5.07/1.07  fof(f540,plain,(
% 5.07/1.07    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),X3) | ~r1_tarski(X2,X3)) )),
% 5.07/1.07    inference(superposition,[],[f145,f70])).
% 5.07/1.07  fof(f70,plain,(
% 5.07/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 5.07/1.07    inference(cnf_transformation,[],[f27])).
% 5.07/1.07  fof(f27,plain,(
% 5.07/1.07    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.07/1.07    inference(ennf_transformation,[],[f6])).
% 5.07/1.07  fof(f6,axiom,(
% 5.07/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.07/1.07  fof(f88,plain,(
% 5.07/1.07    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 5.07/1.07    inference(avatar_component_clause,[],[f86])).
% 5.07/1.07  fof(f94,plain,(
% 5.07/1.07    spl4_1 | spl4_2),
% 5.07/1.07    inference(avatar_split_clause,[],[f42,f90,f86])).
% 5.07/1.07  fof(f42,plain,(
% 5.07/1.07    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.07/1.07    inference(cnf_transformation,[],[f30])).
% 5.07/1.07  fof(f30,plain,(
% 5.07/1.07    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 5.07/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 5.07/1.07  fof(f29,plain,(
% 5.07/1.07    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 5.07/1.07    introduced(choice_axiom,[])).
% 5.07/1.07  fof(f28,plain,(
% 5.07/1.07    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 5.07/1.07    inference(nnf_transformation,[],[f25])).
% 5.07/1.07  fof(f25,plain,(
% 5.07/1.07    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 5.07/1.07    inference(ennf_transformation,[],[f23])).
% 5.07/1.07  fof(f23,negated_conjecture,(
% 5.07/1.07    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.07/1.07    inference(negated_conjecture,[],[f22])).
% 5.07/1.07  fof(f22,conjecture,(
% 5.07/1.07    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 5.07/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 5.07/1.07  fof(f93,plain,(
% 5.07/1.07    ~spl4_1 | ~spl4_2),
% 5.07/1.07    inference(avatar_split_clause,[],[f43,f90,f86])).
% 5.07/1.07  fof(f43,plain,(
% 5.07/1.07    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 5.07/1.07    inference(cnf_transformation,[],[f30])).
% 5.07/1.07  % SZS output end Proof for theBenchmark
% 5.07/1.07  % (22456)------------------------------
% 5.07/1.07  % (22456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.07  % (22456)Termination reason: Refutation
% 5.07/1.07  
% 5.07/1.07  % (22456)Memory used [KB]: 7931
% 5.07/1.07  % (22456)Time elapsed: 0.345 s
% 5.07/1.07  % (22456)------------------------------
% 5.07/1.07  % (22456)------------------------------
% 5.07/1.07  % (22396)Success in time 0.703 s
%------------------------------------------------------------------------------
