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
% DateTime   : Thu Dec  3 12:55:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 337 expanded)
%              Number of leaves         :   20 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  476 (1667 expanded)
%              Number of equality atoms :  108 ( 208 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f176,f183,f303,f324,f343])).

fof(f343,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f340,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f85,f84])).

fof(f84,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
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

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f85,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f18,f21])).

fof(f18,plain,(
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

fof(f340,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f332,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f59,f81])).

fof(f81,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f332,plain,
    ( ~ r2_hidden(sK2,k2_xboole_0(sK2,k1_enumset1(sK2,sK2,sK2)))
    | spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f89,f120])).

fof(f120,plain,
    ( sK2 = sK3
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_1
  <=> r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f324,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f323,f91,f118,f114])).

fof(f114,plain,
    ( spl6_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( spl6_2
  <=> r1_ordinal1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f323,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f111,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f111,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f43,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_ordinal1(sK2,sK3)
      | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
    & ( r1_ordinal1(sK2,sK3)
      | r2_hidden(sK2,k1_ordinal1(sK3)) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK2,X1)
            | ~ r2_hidden(sK2,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK2,X1)
            | r2_hidden(sK2,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK2,X1)
          | ~ r2_hidden(sK2,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK2,X1)
          | r2_hidden(sK2,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK2,sK3)
        | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
      & ( r1_ordinal1(sK2,sK3)
        | r2_hidden(sK2,k1_ordinal1(sK3)) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f110,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v3_ordinal1(sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f107,f44])).

fof(f44,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f52,f92])).

fof(f92,plain,
    ( r1_ordinal1(sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f303,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f295,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f295,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl6_1
    | spl6_2 ),
    inference(backward_demodulation,[],[f179,f290])).

fof(f290,plain,
    ( sK2 = sK3
    | ~ spl6_1
    | spl6_2 ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( sK2 = sK3
    | sK2 = sK3
    | sK2 = sK3
    | ~ spl6_1
    | spl6_2 ),
    inference(resolution,[],[f209,f278])).

fof(f278,plain,
    ( r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f269,f181])).

fof(f181,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl6_2 ),
    inference(resolution,[],[f179,f51])).

fof(f269,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f154,f88])).

fof(f88,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f57,f81])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f209,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f65,f85])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f179,plain,
    ( r2_hidden(sK3,sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f178,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK2)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f177,f44])).

fof(f177,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | spl6_2 ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f93,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f183,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f174,f181])).

fof(f174,plain,
    ( r2_hidden(sK2,sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f173,f44])).

fof(f173,plain,
    ( ~ v3_ordinal1(sK3)
    | r2_hidden(sK2,sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f171,f43])).

fof(f171,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK3)
    | r2_hidden(sK2,sK3)
    | spl6_3 ),
    inference(resolution,[],[f109,f116])).

fof(f116,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f52,f49])).

fof(f176,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f174,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl6_1 ),
    inference(resolution,[],[f125,f89])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f58,f81])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f78,f91,f87])).

fof(f78,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f48,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f45,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f77,f91,f87])).

fof(f77,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f46,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22736)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (22749)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (22744)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.50  % (22741)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (22741)Refutation not found, incomplete strategy% (22741)------------------------------
% 0.21/0.51  % (22741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22741)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22741)Memory used [KB]: 1791
% 0.21/0.51  % (22741)Time elapsed: 0.056 s
% 0.21/0.51  % (22741)------------------------------
% 0.21/0.51  % (22741)------------------------------
% 0.21/0.51  % (22731)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (22733)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22744)Refutation not found, incomplete strategy% (22744)------------------------------
% 0.21/0.51  % (22744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22744)Memory used [KB]: 1663
% 0.21/0.51  % (22744)Time elapsed: 0.095 s
% 0.21/0.51  % (22744)------------------------------
% 0.21/0.51  % (22744)------------------------------
% 0.21/0.51  % (22732)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (22753)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (22753)Refutation not found, incomplete strategy% (22753)------------------------------
% 0.21/0.52  % (22753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22753)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22753)Memory used [KB]: 6268
% 0.21/0.52  % (22753)Time elapsed: 0.108 s
% 0.21/0.52  % (22753)------------------------------
% 0.21/0.52  % (22753)------------------------------
% 0.21/0.52  % (22730)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (22734)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (22733)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (22728)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f94,f95,f176,f183,f303,f324,f343])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    spl6_1 | ~spl6_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    $false | (spl6_1 | ~spl6_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f340,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.52    inference(resolution,[],[f85,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.52    inference(equality_resolution,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(rectify,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.21/0.52    inference(definition_folding,[],[f18,f21])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    ~r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | (spl6_1 | ~spl6_4)),
% 0.21/0.52    inference(resolution,[],[f332,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f59,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.52    inference(definition_folding,[],[f2,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ~r2_hidden(sK2,k2_xboole_0(sK2,k1_enumset1(sK2,sK2,sK2))) | (spl6_1 | ~spl6_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f89,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    sK2 = sK3 | ~spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl6_4 <=> sK2 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) | spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl6_1 <=> r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    ~spl6_3 | spl6_4 | ~spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f323,f91,f118,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl6_3 <=> r1_tarski(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl6_2 <=> r1_ordinal1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f111,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_tarski(sK2,sK3) | ~spl6_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v3_ordinal1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r1_tarski(sK2,sK3) | ~v3_ordinal1(sK2) | ~spl6_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v3_ordinal1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    r1_tarski(sK2,sK3) | ~v3_ordinal1(sK3) | ~v3_ordinal1(sK2) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f52,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    r1_ordinal1(sK2,sK3) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.52  fof(f303,plain,(
% 0.21/0.52    ~spl6_1 | spl6_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.52  fof(f302,plain,(
% 0.21/0.52    $false | (~spl6_1 | spl6_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f295,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    r2_hidden(sK2,sK2) | (~spl6_1 | spl6_2)),
% 0.21/0.52    inference(backward_demodulation,[],[f179,f290])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    sK2 = sK3 | (~spl6_1 | spl6_2)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    sK2 = sK3 | sK2 = sK3 | sK2 = sK3 | (~spl6_1 | spl6_2)),
% 0.21/0.52    inference(resolution,[],[f209,f278])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl6_1 | spl6_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f269,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK3) | spl6_2),
% 0.21/0.52    inference(resolution,[],[f179,f51])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    r2_hidden(sK2,sK3) | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) | ~spl6_1),
% 0.21/0.52    inference(resolution,[],[f154,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) | ~spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(resolution,[],[f57,f81])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k1_enumset1(X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 0.21/0.52    inference(resolution,[],[f65,f85])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2) | spl6_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f43])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2) | ~v3_ordinal1(sK2) | spl6_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f177,f44])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2) | ~v3_ordinal1(sK3) | ~v3_ordinal1(sK2) | spl6_2),
% 0.21/0.52    inference(resolution,[],[f93,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~r1_ordinal1(sK2,sK3) | spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl6_2 | spl6_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    $false | (spl6_2 | spl6_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f181])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    r2_hidden(sK2,sK3) | spl6_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f44])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~v3_ordinal1(sK3) | r2_hidden(sK2,sK3) | spl6_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f43])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~v3_ordinal1(sK2) | ~v3_ordinal1(sK3) | r2_hidden(sK2,sK3) | spl6_3),
% 0.21/0.52    inference(resolution,[],[f109,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~r1_tarski(sK3,sK2) | spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f52,f49])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl6_1 | spl6_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    $false | (spl6_1 | spl6_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK3) | spl6_1),
% 0.21/0.52    inference(resolution,[],[f125,f89])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f58,f81])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl6_1 | spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f78,f91,f87])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 0.21/0.52    inference(definition_unfolding,[],[f45,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f48,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f77,f91,f87])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 0.21/0.52    inference(definition_unfolding,[],[f46,f76])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22733)------------------------------
% 0.21/0.52  % (22733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22733)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22733)Memory used [KB]: 10874
% 0.21/0.52  % (22733)Time elapsed: 0.068 s
% 0.21/0.52  % (22733)------------------------------
% 0.21/0.52  % (22733)------------------------------
% 0.21/0.53  % (22725)Success in time 0.167 s
%------------------------------------------------------------------------------
