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
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 216 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  489 (1286 expanded)
%              Number of equality atoms :  230 ( 674 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f254,f348,f375,f388,f409,f420,f446])).

fof(f446,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f440,f31])).

fof(f31,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
    & sK0 != sK2
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 )
   => ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
      & sK0 != sK2
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
      & X0 != X2
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
          & X0 != X2
          & X0 != X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

fof(f440,plain,
    ( sK0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f430,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f430,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f429,f58])).

fof(f58,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f429,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f428,f347])).

fof(f347,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl7_12
  <=> sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f428,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f427,f69])).

fof(f69,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK6(X0,X1,X2,X3) != X2
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X2
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X0
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
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
     => ( ( ( sK6(X0,X1,X2,X3) != X2
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X2
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X0
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f427,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f426,f347])).

fof(f426,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f359,f347])).

fof(f359,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2] :
      ( k2_tarski(sK1,sK2) != X2
      | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_enumset1(sK0,sK1,sK2))
      | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),X2) ) ),
    inference(superposition,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f32,plain,(
    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f420,plain,
    ( spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f418,f414])).

fof(f414,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f413,f60])).

fof(f60,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f413,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f412,f343])).

fof(f343,plain,
    ( sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl7_11
  <=> sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f412,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f411,f71])).

fof(f71,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f411,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f400,f343])).

fof(f400,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f359,f343])).

fof(f418,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl7_8
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f253,f343])).

fof(f253,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl7_8
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f409,plain,
    ( ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f403,f30])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f403,plain,
    ( sK0 = sK1
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f398,f67])).

fof(f398,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f252,f343])).

fof(f252,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f388,plain,
    ( spl7_8
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f384,f66])).

fof(f66,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f384,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl7_8
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f253,f339])).

fof(f339,plain,
    ( sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl7_10
  <=> sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f375,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f363,f247,f345,f341])).

fof(f247,plain,
    ( spl7_7
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f363,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_7 ),
    inference(resolution,[],[f249,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f249,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f247])).

fof(f348,plain,
    ( spl7_10
    | spl7_11
    | spl7_12
    | spl7_7 ),
    inference(avatar_split_clause,[],[f324,f247,f345,f341,f337])).

fof(f324,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl7_7 ),
    inference(resolution,[],[f285,f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f285,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | spl7_7 ),
    inference(subsumption_resolution,[],[f282,f248])).

fof(f248,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f247])).

fof(f282,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK2) != X0
      | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2))
      | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f254,plain,
    ( spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f243,f251,f247])).

fof(f243,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X1] :
      ( k2_tarski(sK1,sK2) != X1
      | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),k1_tarski(sK0))
      | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),X1) ) ),
    inference(superposition,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (4381)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (4386)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (4373)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (4383)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (4396)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (4378)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (4378)Refutation not found, incomplete strategy% (4378)------------------------------
% 0.21/0.50  % (4378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4378)Memory used [KB]: 6140
% 0.21/0.50  % (4378)Time elapsed: 0.088 s
% 0.21/0.50  % (4378)------------------------------
% 0.21/0.50  % (4378)------------------------------
% 0.21/0.50  % (4374)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (4388)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (4380)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (4391)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (4374)Refutation not found, incomplete strategy% (4374)------------------------------
% 0.21/0.51  % (4374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4374)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4374)Memory used [KB]: 10618
% 0.21/0.51  % (4374)Time elapsed: 0.087 s
% 0.21/0.51  % (4374)------------------------------
% 0.21/0.51  % (4374)------------------------------
% 0.21/0.51  % (4392)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (4375)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (4394)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (4379)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (4376)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (4382)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (4387)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (4393)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (4395)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.31/0.53  % (4379)Refutation not found, incomplete strategy% (4379)------------------------------
% 1.31/0.53  % (4379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (4379)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (4379)Memory used [KB]: 10618
% 1.31/0.53  % (4379)Time elapsed: 0.089 s
% 1.31/0.53  % (4379)------------------------------
% 1.31/0.53  % (4379)------------------------------
% 1.31/0.53  % (4384)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.31/0.53  % (4389)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.31/0.54  % (4385)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.31/0.54  % (4398)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.31/0.54  % (4397)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.54  % (4390)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.57  % (4384)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f448,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(avatar_sat_refutation,[],[f254,f348,f375,f388,f409,f420,f446])).
% 1.45/0.57  fof(f446,plain,(
% 1.45/0.57    ~spl7_12),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f445])).
% 1.45/0.57  fof(f445,plain,(
% 1.45/0.57    $false | ~spl7_12),
% 1.45/0.57    inference(subsumption_resolution,[],[f440,f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    sK0 != sK2),
% 1.45/0.57    inference(cnf_transformation,[],[f10])).
% 1.45/0.57  fof(f10,plain,(
% 1.45/0.57    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 1.45/0.57  fof(f9,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1) => (k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1)),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f7,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,negated_conjecture,(
% 1.45/0.57    ~! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 1.45/0.57    inference(negated_conjecture,[],[f5])).
% 1.45/0.57  fof(f5,conjecture,(
% 1.45/0.57    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).
% 1.45/0.57  fof(f440,plain,(
% 1.45/0.57    sK0 = sK2 | ~spl7_12),
% 1.45/0.57    inference(resolution,[],[f430,f67])).
% 1.45/0.57  fof(f67,plain,(
% 1.45/0.57    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.45/0.57    inference(equality_resolution,[],[f45])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f24])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.45/0.57    inference(rectify,[],[f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.45/0.57    inference(nnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.45/0.57  fof(f430,plain,(
% 1.45/0.57    r2_hidden(sK2,k1_tarski(sK0)) | ~spl7_12),
% 1.45/0.57    inference(subsumption_resolution,[],[f429,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.45/0.57    inference(equality_resolution,[],[f57])).
% 1.45/0.57  fof(f57,plain,(
% 1.45/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.45/0.57    inference(equality_resolution,[],[f35])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f13,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(rectify,[],[f12])).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(flattening,[],[f11])).
% 1.45/0.57  fof(f11,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(nnf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.45/0.57  fof(f429,plain,(
% 1.45/0.57    ~r2_hidden(sK2,k2_tarski(sK1,sK2)) | r2_hidden(sK2,k1_tarski(sK0)) | ~spl7_12),
% 1.45/0.57    inference(forward_demodulation,[],[f428,f347])).
% 1.45/0.57  fof(f347,plain,(
% 1.45/0.57    sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl7_12),
% 1.45/0.57    inference(avatar_component_clause,[],[f345])).
% 1.45/0.57  fof(f345,plain,(
% 1.45/0.57    spl7_12 <=> sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.45/0.57  fof(f428,plain,(
% 1.45/0.57    r2_hidden(sK2,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_12),
% 1.45/0.57    inference(subsumption_resolution,[],[f427,f69])).
% 1.45/0.57  fof(f69,plain,(
% 1.45/0.57    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.45/0.57    inference(equality_resolution,[],[f68])).
% 1.45/0.57  fof(f68,plain,(
% 1.45/0.57    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.45/0.57    inference(equality_resolution,[],[f52])).
% 1.45/0.57  fof(f52,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.57    inference(cnf_transformation,[],[f29])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.45/0.57    inference(rectify,[],[f26])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.45/0.57    inference(flattening,[],[f25])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.45/0.57    inference(nnf_transformation,[],[f8])).
% 1.45/0.57  fof(f8,plain,(
% 1.45/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.45/0.57    inference(ennf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.45/0.57  fof(f427,plain,(
% 1.45/0.57    ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK2,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_12),
% 1.45/0.57    inference(forward_demodulation,[],[f426,f347])).
% 1.45/0.57  fof(f426,plain,(
% 1.45/0.57    r2_hidden(sK2,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_12),
% 1.45/0.57    inference(forward_demodulation,[],[f359,f347])).
% 1.45/0.57  fof(f359,plain,(
% 1.45/0.57    r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))),
% 1.45/0.57    inference(equality_resolution,[],[f83])).
% 1.45/0.57  fof(f83,plain,(
% 1.45/0.57    ( ! [X2] : (k2_tarski(sK1,sK2) != X2 | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_enumset1(sK0,sK1,sK2)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),X2)) )),
% 1.45/0.57    inference(superposition,[],[f32,f44])).
% 1.45/0.57  fof(f44,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.57    inference(rectify,[],[f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.57    inference(flattening,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.57    inference(nnf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f10])).
% 1.45/0.57  fof(f420,plain,(
% 1.45/0.57    spl7_8 | ~spl7_11),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f419])).
% 1.45/0.57  fof(f419,plain,(
% 1.45/0.57    $false | (spl7_8 | ~spl7_11)),
% 1.45/0.57    inference(subsumption_resolution,[],[f418,f414])).
% 1.45/0.57  fof(f414,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_tarski(sK0)) | ~spl7_11),
% 1.45/0.57    inference(subsumption_resolution,[],[f413,f60])).
% 1.45/0.57  fof(f60,plain,(
% 1.45/0.57    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.45/0.57    inference(equality_resolution,[],[f59])).
% 1.45/0.57  fof(f59,plain,(
% 1.45/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.45/0.57    inference(equality_resolution,[],[f34])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f413,plain,(
% 1.45/0.57    ~r2_hidden(sK1,k2_tarski(sK1,sK2)) | r2_hidden(sK1,k1_tarski(sK0)) | ~spl7_11),
% 1.45/0.57    inference(forward_demodulation,[],[f412,f343])).
% 1.45/0.57  fof(f343,plain,(
% 1.45/0.57    sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl7_11),
% 1.45/0.57    inference(avatar_component_clause,[],[f341])).
% 1.45/0.57  fof(f341,plain,(
% 1.45/0.57    spl7_11 <=> sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.45/0.57  fof(f412,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_11),
% 1.45/0.57    inference(subsumption_resolution,[],[f411,f71])).
% 1.45/0.57  fof(f71,plain,(
% 1.45/0.57    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 1.45/0.57    inference(equality_resolution,[],[f70])).
% 1.45/0.57  fof(f70,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 1.45/0.57    inference(equality_resolution,[],[f51])).
% 1.45/0.57  fof(f51,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.57    inference(cnf_transformation,[],[f29])).
% 1.45/0.57  fof(f411,plain,(
% 1.45/0.57    ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_11),
% 1.45/0.57    inference(forward_demodulation,[],[f400,f343])).
% 1.45/0.57  fof(f400,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_11),
% 1.45/0.57    inference(forward_demodulation,[],[f359,f343])).
% 1.45/0.57  fof(f418,plain,(
% 1.45/0.57    ~r2_hidden(sK1,k1_tarski(sK0)) | (spl7_8 | ~spl7_11)),
% 1.45/0.57    inference(forward_demodulation,[],[f253,f343])).
% 1.45/0.57  fof(f253,plain,(
% 1.45/0.57    ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) | spl7_8),
% 1.45/0.57    inference(avatar_component_clause,[],[f251])).
% 1.45/0.57  fof(f251,plain,(
% 1.45/0.57    spl7_8 <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.45/0.57  fof(f409,plain,(
% 1.45/0.57    ~spl7_8 | ~spl7_11),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f408])).
% 1.45/0.57  fof(f408,plain,(
% 1.45/0.57    $false | (~spl7_8 | ~spl7_11)),
% 1.45/0.57    inference(subsumption_resolution,[],[f403,f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    sK0 != sK1),
% 1.45/0.57    inference(cnf_transformation,[],[f10])).
% 1.45/0.57  fof(f403,plain,(
% 1.45/0.57    sK0 = sK1 | (~spl7_8 | ~spl7_11)),
% 1.45/0.57    inference(resolution,[],[f398,f67])).
% 1.45/0.57  fof(f398,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_tarski(sK0)) | (~spl7_8 | ~spl7_11)),
% 1.45/0.57    inference(backward_demodulation,[],[f252,f343])).
% 1.45/0.57  fof(f252,plain,(
% 1.45/0.57    r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) | ~spl7_8),
% 1.45/0.57    inference(avatar_component_clause,[],[f251])).
% 1.45/0.57  fof(f388,plain,(
% 1.45/0.57    spl7_8 | ~spl7_10),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f387])).
% 1.45/0.57  fof(f387,plain,(
% 1.45/0.57    $false | (spl7_8 | ~spl7_10)),
% 1.45/0.57    inference(subsumption_resolution,[],[f384,f66])).
% 1.45/0.57  fof(f66,plain,(
% 1.45/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.45/0.57    inference(equality_resolution,[],[f65])).
% 1.45/0.57  fof(f65,plain,(
% 1.45/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.45/0.57    inference(equality_resolution,[],[f46])).
% 1.45/0.57  fof(f46,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f24])).
% 1.45/0.57  fof(f384,plain,(
% 1.45/0.57    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl7_8 | ~spl7_10)),
% 1.45/0.57    inference(backward_demodulation,[],[f253,f339])).
% 1.45/0.57  fof(f339,plain,(
% 1.45/0.57    sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl7_10),
% 1.45/0.57    inference(avatar_component_clause,[],[f337])).
% 1.45/0.57  fof(f337,plain,(
% 1.45/0.57    spl7_10 <=> sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.45/0.57  fof(f375,plain,(
% 1.45/0.57    spl7_11 | spl7_12 | ~spl7_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f363,f247,f345,f341])).
% 1.45/0.57  fof(f247,plain,(
% 1.45/0.57    spl7_7 <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.45/0.57  fof(f363,plain,(
% 1.45/0.57    sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl7_7),
% 1.45/0.57    inference(resolution,[],[f249,f61])).
% 1.45/0.57  fof(f61,plain,(
% 1.45/0.57    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.45/0.57    inference(equality_resolution,[],[f33])).
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f249,plain,(
% 1.45/0.57    r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | ~spl7_7),
% 1.45/0.57    inference(avatar_component_clause,[],[f247])).
% 1.45/0.57  fof(f348,plain,(
% 1.45/0.57    spl7_10 | spl7_11 | spl7_12 | spl7_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f324,f247,f345,f341,f337])).
% 1.45/0.57  fof(f324,plain,(
% 1.45/0.57    sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) | spl7_7),
% 1.45/0.57    inference(resolution,[],[f285,f74])).
% 1.45/0.57  fof(f74,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 1.45/0.57    inference(equality_resolution,[],[f49])).
% 1.45/0.57  fof(f49,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.57    inference(cnf_transformation,[],[f29])).
% 1.45/0.57  fof(f285,plain,(
% 1.45/0.57    r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | spl7_7),
% 1.45/0.57    inference(subsumption_resolution,[],[f282,f248])).
% 1.45/0.57  fof(f248,plain,(
% 1.45/0.57    ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) | spl7_7),
% 1.45/0.57    inference(avatar_component_clause,[],[f247])).
% 1.45/0.57  fof(f282,plain,(
% 1.45/0.57    r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))),
% 1.45/0.57    inference(equality_resolution,[],[f81])).
% 1.45/0.57  fof(f81,plain,(
% 1.45/0.57    ( ! [X0] : (k2_tarski(sK1,sK2) != X0 | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),X0)) )),
% 1.45/0.57    inference(superposition,[],[f32,f42])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  fof(f254,plain,(
% 1.45/0.57    spl7_7 | ~spl7_8),
% 1.45/0.57    inference(avatar_split_clause,[],[f243,f251,f247])).
% 1.45/0.57  fof(f243,plain,(
% 1.45/0.57    ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))),
% 1.45/0.57    inference(equality_resolution,[],[f82])).
% 1.45/0.57  fof(f82,plain,(
% 1.45/0.57    ( ! [X1] : (k2_tarski(sK1,sK2) != X1 | ~r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),k1_tarski(sK0)) | r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),X1)) )),
% 1.45/0.57    inference(superposition,[],[f32,f43])).
% 1.45/0.57  fof(f43,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (4384)------------------------------
% 1.45/0.57  % (4384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (4384)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (4384)Memory used [KB]: 10874
% 1.45/0.57  % (4384)Time elapsed: 0.155 s
% 1.45/0.57  % (4384)------------------------------
% 1.45/0.57  % (4384)------------------------------
% 1.45/0.57  % (4372)Success in time 0.198 s
%------------------------------------------------------------------------------
