%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0210+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f256,f350,f377,f390,f411,f422,f448])).

fof(f448,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f442,f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(f442,plain,
    ( sK0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f432,f67])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f432,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f431,f58])).

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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f431,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f430,f349])).

fof(f349,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl7_12
  <=> sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f430,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f429,f69])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f429,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f428,f349])).

fof(f428,plain,
    ( r2_hidden(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f361,f349])).

fof(f361,plain,
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f32,plain,(
    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f422,plain,
    ( spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f420,f416])).

fof(f416,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f415,f60])).

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

fof(f415,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f414,f345])).

fof(f345,plain,
    ( sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl7_11
  <=> sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f414,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f413,f71])).

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

fof(f413,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f402,f345])).

fof(f402,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f361,f345])).

fof(f420,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl7_8
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f255,f345])).

fof(f255,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl7_8
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f411,plain,
    ( ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f405,f30])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f405,plain,
    ( sK0 = sK1
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f400,f67])).

fof(f400,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f254,f345])).

fof(f254,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f253])).

fof(f390,plain,
    ( spl7_8
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f386,f66])).

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

fof(f386,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl7_8
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f255,f341])).

fof(f341,plain,
    ( sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl7_10
  <=> sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f377,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f365,f249,f347,f343])).

fof(f249,plain,
    ( spl7_7
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f365,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl7_7 ),
    inference(resolution,[],[f251,f61])).

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

fof(f251,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f350,plain,
    ( spl7_10
    | spl7_11
    | spl7_12
    | spl7_7 ),
    inference(avatar_split_clause,[],[f326,f249,f347,f343,f339])).

fof(f326,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | sK0 = sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl7_7 ),
    inference(resolution,[],[f287,f74])).

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

fof(f287,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | spl7_7 ),
    inference(subsumption_resolution,[],[f284,f250])).

fof(f250,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f284,plain,
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

fof(f256,plain,
    ( spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f245,f253,f249])).

fof(f245,plain,
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
