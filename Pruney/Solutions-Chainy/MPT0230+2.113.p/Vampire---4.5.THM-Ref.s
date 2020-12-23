%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:49 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 254 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 ( 574 expanded)
%              Number of equality atoms :  161 ( 380 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f249,f270,f307])).

fof(f307,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl7_3 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( sK1 != sK1
    | ~ spl7_3 ),
    inference(superposition,[],[f44,f244])).

fof(f244,plain,
    ( sK1 = sK3
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl7_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f44,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f270,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,
    ( sK1 != sK1
    | ~ spl7_4 ),
    inference(superposition,[],[f43,f248])).

fof(f248,plain,
    ( sK1 = sK2
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl7_4
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f43,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f249,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f240,f246,f242])).

fof(f240,plain,
    ( sK1 = sK2
    | sK1 = sK3 ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( sK1 = sK2
    | sK1 = sK3
    | sK1 = sK2 ),
    inference(resolution,[],[f230,f168])).

fof(f168,plain,(
    ! [X19,X17,X15,X20,X18,X16] :
      ( ~ sP0(X15,X19,X20,k6_enumset1(X16,X16,X16,X16,X16,X16,X17,X18))
      | X15 = X17
      | X15 = X18
      | X15 = X16 ) ),
    inference(resolution,[],[f139,f88])).

fof(f88,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
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
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f59,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f230,plain,(
    sP0(sK1,sK3,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(superposition,[],[f91,f225])).

fof(f225,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK1) ),
    inference(forward_demodulation,[],[f223,f112])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f110,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f94,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f93,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f93,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(resolution,[],[f82,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f79,f46])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f223,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f87,f117])).

fof(f117,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(forward_demodulation,[],[f115,f113])).

fof(f113,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f111,f46])).

fof(f111,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f79,f95])).

fof(f115,plain,(
    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f79,f109])).

fof(f109,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f42,f78,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f70,f74,f51,f75,f78])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n020.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:01:07 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.42  % (25687)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.44  % (25697)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.16/0.44  % (25679)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.16/0.44  % (25689)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.16/0.45  % (25687)Refutation found. Thanks to Tanya!
% 0.16/0.45  % SZS status Theorem for theBenchmark
% 0.16/0.46  % (25681)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.16/0.46  % (25676)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.16/0.46  % (25679)Refutation not found, incomplete strategy% (25679)------------------------------
% 0.16/0.46  % (25679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.46  % (25679)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.46  
% 0.16/0.46  % (25679)Memory used [KB]: 6268
% 0.16/0.46  % (25679)Time elapsed: 0.102 s
% 0.16/0.46  % (25679)------------------------------
% 0.16/0.46  % (25679)------------------------------
% 0.16/0.46  % SZS output start Proof for theBenchmark
% 0.16/0.46  fof(f308,plain,(
% 0.16/0.46    $false),
% 0.16/0.46    inference(avatar_sat_refutation,[],[f249,f270,f307])).
% 0.16/0.46  fof(f307,plain,(
% 0.16/0.46    ~spl7_3),
% 0.16/0.46    inference(avatar_contradiction_clause,[],[f306])).
% 0.16/0.46  fof(f306,plain,(
% 0.16/0.46    $false | ~spl7_3),
% 0.16/0.46    inference(trivial_inequality_removal,[],[f305])).
% 0.16/0.46  fof(f305,plain,(
% 0.16/0.46    sK1 != sK1 | ~spl7_3),
% 0.16/0.46    inference(superposition,[],[f44,f244])).
% 0.16/0.46  fof(f244,plain,(
% 0.16/0.46    sK1 = sK3 | ~spl7_3),
% 0.16/0.46    inference(avatar_component_clause,[],[f242])).
% 0.16/0.46  fof(f242,plain,(
% 0.16/0.46    spl7_3 <=> sK1 = sK3),
% 0.16/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.16/0.46  fof(f44,plain,(
% 0.16/0.46    sK1 != sK3),
% 0.16/0.46    inference(cnf_transformation,[],[f31])).
% 0.16/0.46  fof(f31,plain,(
% 0.16/0.46    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 0.16/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f30])).
% 0.16/0.46  fof(f30,plain,(
% 0.16/0.46    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.16/0.46    introduced(choice_axiom,[])).
% 0.16/0.46  fof(f23,plain,(
% 0.16/0.46    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.16/0.46    inference(ennf_transformation,[],[f20])).
% 0.16/0.46  fof(f20,negated_conjecture,(
% 0.16/0.46    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.16/0.46    inference(negated_conjecture,[],[f19])).
% 0.16/0.46  fof(f19,conjecture,(
% 0.16/0.46    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.16/0.46  fof(f270,plain,(
% 0.16/0.46    ~spl7_4),
% 0.16/0.46    inference(avatar_contradiction_clause,[],[f269])).
% 0.16/0.46  fof(f269,plain,(
% 0.16/0.46    $false | ~spl7_4),
% 0.16/0.46    inference(trivial_inequality_removal,[],[f268])).
% 0.16/0.46  fof(f268,plain,(
% 0.16/0.46    sK1 != sK1 | ~spl7_4),
% 0.16/0.46    inference(superposition,[],[f43,f248])).
% 0.16/0.46  fof(f248,plain,(
% 0.16/0.46    sK1 = sK2 | ~spl7_4),
% 0.16/0.46    inference(avatar_component_clause,[],[f246])).
% 0.16/0.46  fof(f246,plain,(
% 0.16/0.46    spl7_4 <=> sK1 = sK2),
% 0.16/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.16/0.46  fof(f43,plain,(
% 0.16/0.46    sK1 != sK2),
% 0.16/0.46    inference(cnf_transformation,[],[f31])).
% 0.16/0.46  fof(f249,plain,(
% 0.16/0.46    spl7_3 | spl7_4),
% 0.16/0.46    inference(avatar_split_clause,[],[f240,f246,f242])).
% 0.16/0.46  fof(f240,plain,(
% 0.16/0.46    sK1 = sK2 | sK1 = sK3),
% 0.16/0.46    inference(duplicate_literal_removal,[],[f233])).
% 0.16/0.46  fof(f233,plain,(
% 0.16/0.46    sK1 = sK2 | sK1 = sK3 | sK1 = sK2),
% 0.16/0.46    inference(resolution,[],[f230,f168])).
% 0.16/0.46  fof(f168,plain,(
% 0.16/0.46    ( ! [X19,X17,X15,X20,X18,X16] : (~sP0(X15,X19,X20,k6_enumset1(X16,X16,X16,X16,X16,X16,X17,X18)) | X15 = X17 | X15 = X18 | X15 = X16) )),
% 0.16/0.46    inference(resolution,[],[f139,f88])).
% 0.16/0.46  fof(f88,plain,(
% 0.16/0.46    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X1,X2,X3)) )),
% 0.16/0.46    inference(equality_resolution,[],[f62])).
% 0.16/0.46  fof(f62,plain,(
% 0.16/0.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f40])).
% 0.16/0.46  fof(f40,plain,(
% 0.16/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.16/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 0.16/0.46  fof(f39,plain,(
% 0.16/0.46    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.16/0.46    introduced(choice_axiom,[])).
% 0.16/0.46  fof(f38,plain,(
% 0.16/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.16/0.46    inference(rectify,[],[f37])).
% 0.16/0.46  fof(f37,plain,(
% 0.16/0.46    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.16/0.46    inference(flattening,[],[f36])).
% 0.16/0.46  fof(f36,plain,(
% 0.16/0.46    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.16/0.46    inference(nnf_transformation,[],[f28])).
% 0.16/0.46  fof(f28,plain,(
% 0.16/0.46    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.16/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.16/0.46  fof(f139,plain,(
% 0.16/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 0.16/0.46    inference(resolution,[],[f59,f91])).
% 0.16/0.46  fof(f91,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.16/0.46    inference(equality_resolution,[],[f86])).
% 0.16/0.46  fof(f86,plain,(
% 0.16/0.46    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.16/0.46    inference(definition_unfolding,[],[f67,f76])).
% 0.16/0.46  fof(f76,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f57,f75])).
% 0.16/0.46  fof(f75,plain,(
% 0.16/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f58,f74])).
% 0.16/0.46  fof(f74,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f69,f73])).
% 0.16/0.46  fof(f73,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f71,f72])).
% 0.16/0.46  fof(f72,plain,(
% 0.16/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f18])).
% 0.16/0.46  fof(f18,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.16/0.46  fof(f71,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f17])).
% 0.16/0.46  fof(f17,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.16/0.46  fof(f69,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f16])).
% 0.16/0.46  fof(f16,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.16/0.46  fof(f58,plain,(
% 0.16/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f15])).
% 0.16/0.46  fof(f15,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.16/0.46  fof(f57,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f14])).
% 0.16/0.46  fof(f14,axiom,(
% 0.16/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.16/0.46  fof(f67,plain,(
% 0.16/0.46    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.16/0.46    inference(cnf_transformation,[],[f41])).
% 0.16/0.46  fof(f41,plain,(
% 0.16/0.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.16/0.46    inference(nnf_transformation,[],[f29])).
% 0.16/0.46  fof(f29,plain,(
% 0.16/0.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.16/0.46    inference(definition_folding,[],[f27,f28])).
% 0.16/0.46  fof(f27,plain,(
% 0.16/0.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.16/0.46    inference(ennf_transformation,[],[f10])).
% 0.16/0.46  fof(f10,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.16/0.46  fof(f59,plain,(
% 0.16/0.46    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.16/0.46    inference(cnf_transformation,[],[f40])).
% 0.16/0.46  fof(f230,plain,(
% 0.16/0.46    sP0(sK1,sK3,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.16/0.46    inference(superposition,[],[f91,f225])).
% 0.16/0.46  fof(f225,plain,(
% 0.16/0.46    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK1)),
% 0.16/0.46    inference(forward_demodulation,[],[f223,f112])).
% 0.16/0.46  fof(f112,plain,(
% 0.16/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.16/0.46    inference(forward_demodulation,[],[f110,f95])).
% 0.16/0.46  fof(f95,plain,(
% 0.16/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.16/0.46    inference(resolution,[],[f94,f48])).
% 0.16/0.46  fof(f48,plain,(
% 0.16/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.16/0.46    inference(cnf_transformation,[],[f33])).
% 0.16/0.46  fof(f33,plain,(
% 0.16/0.46    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.16/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).
% 0.16/0.46  fof(f32,plain,(
% 0.16/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.16/0.46    introduced(choice_axiom,[])).
% 0.16/0.46  fof(f24,plain,(
% 0.16/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.16/0.46    inference(ennf_transformation,[],[f3])).
% 0.16/0.46  fof(f3,axiom,(
% 0.16/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.16/0.46  fof(f94,plain,(
% 0.16/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 0.16/0.46    inference(forward_demodulation,[],[f93,f46])).
% 0.16/0.46  fof(f46,plain,(
% 0.16/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.16/0.46    inference(cnf_transformation,[],[f6])).
% 0.16/0.46  fof(f6,axiom,(
% 0.16/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.16/0.46  fof(f93,plain,(
% 0.16/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 0.16/0.46    inference(resolution,[],[f82,f45])).
% 0.16/0.46  fof(f45,plain,(
% 0.16/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f8])).
% 0.16/0.46  fof(f8,axiom,(
% 0.16/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.16/0.46  fof(f82,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.16/0.46    inference(definition_unfolding,[],[f55,f53])).
% 0.16/0.46  fof(f53,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f7])).
% 0.16/0.46  fof(f7,axiom,(
% 0.16/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.16/0.46  fof(f55,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f35])).
% 0.16/0.46  fof(f35,plain,(
% 0.16/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.16/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f34])).
% 0.16/0.46  fof(f34,plain,(
% 0.16/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.16/0.46    introduced(choice_axiom,[])).
% 0.16/0.46  fof(f25,plain,(
% 0.16/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.16/0.46    inference(ennf_transformation,[],[f22])).
% 0.16/0.46  fof(f22,plain,(
% 0.16/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.16/0.46    inference(rectify,[],[f2])).
% 0.16/0.46  fof(f2,axiom,(
% 0.16/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.16/0.46  fof(f110,plain,(
% 0.16/0.46    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.16/0.46    inference(superposition,[],[f79,f46])).
% 0.16/0.46  fof(f79,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.16/0.46    inference(definition_unfolding,[],[f52,f53])).
% 0.16/0.46  fof(f52,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f4])).
% 0.16/0.46  fof(f4,axiom,(
% 0.16/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.16/0.46  fof(f223,plain,(
% 0.16/0.46    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)),
% 0.16/0.46    inference(superposition,[],[f87,f117])).
% 0.16/0.46  fof(f117,plain,(
% 0.16/0.46    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.16/0.46    inference(forward_demodulation,[],[f115,f113])).
% 0.16/0.46  fof(f113,plain,(
% 0.16/0.46    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.16/0.46    inference(forward_demodulation,[],[f111,f46])).
% 0.16/0.46  fof(f111,plain,(
% 0.16/0.46    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.16/0.46    inference(superposition,[],[f79,f95])).
% 0.16/0.46  fof(f115,plain,(
% 0.16/0.46    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.16/0.46    inference(superposition,[],[f79,f109])).
% 0.16/0.46  fof(f109,plain,(
% 0.16/0.46    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.16/0.46    inference(resolution,[],[f84,f80])).
% 0.16/0.46  fof(f80,plain,(
% 0.16/0.46    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.16/0.46    inference(definition_unfolding,[],[f42,f78,f77])).
% 0.16/0.46  fof(f77,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f50,f76])).
% 0.16/0.46  fof(f50,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f13])).
% 0.16/0.46  fof(f13,axiom,(
% 0.16/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.16/0.46  fof(f78,plain,(
% 0.16/0.46    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f47,f77])).
% 0.16/0.46  fof(f47,plain,(
% 0.16/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f12])).
% 0.16/0.46  fof(f12,axiom,(
% 0.16/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.16/0.46  fof(f42,plain,(
% 0.16/0.46    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 0.16/0.46    inference(cnf_transformation,[],[f31])).
% 0.16/0.46  fof(f84,plain,(
% 0.16/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.16/0.46    inference(definition_unfolding,[],[f56,f53])).
% 0.16/0.46  fof(f56,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f26])).
% 0.16/0.46  fof(f26,plain,(
% 0.16/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.16/0.46    inference(ennf_transformation,[],[f5])).
% 0.16/0.46  fof(f5,axiom,(
% 0.16/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.16/0.46  fof(f87,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) )),
% 0.16/0.46    inference(definition_unfolding,[],[f70,f74,f51,f75,f78])).
% 0.16/0.46  fof(f51,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f9])).
% 0.16/0.46  fof(f9,axiom,(
% 0.16/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.16/0.46  fof(f70,plain,(
% 0.16/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f11])).
% 0.16/0.46  fof(f11,axiom,(
% 0.16/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.16/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.16/0.46  % SZS output end Proof for theBenchmark
% 0.16/0.46  % (25687)------------------------------
% 0.16/0.46  % (25687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.46  % (25687)Termination reason: Refutation
% 0.16/0.46  
% 0.16/0.46  % (25687)Memory used [KB]: 6396
% 0.16/0.46  % (25687)Time elapsed: 0.101 s
% 0.16/0.46  % (25687)------------------------------
% 0.16/0.46  % (25687)------------------------------
% 0.16/0.46  % (25674)Success in time 0.142 s
%------------------------------------------------------------------------------
