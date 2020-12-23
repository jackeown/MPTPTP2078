%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 835 expanded)
%              Number of leaves         :   24 ( 278 expanded)
%              Depth                    :   20
%              Number of atoms          :  444 (4293 expanded)
%              Number of equality atoms :  292 (3249 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f268,f275,f311])).

fof(f311,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl7_1 ),
    inference(resolution,[],[f303,f112])).

fof(f112,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f95,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f66,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f303,plain,
    ( ! [X4] : ~ r2_hidden(sK4,k1_enumset1(X4,X4,X4))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f302,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f60,f95])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f302,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ r2_hidden(sK4,k1_enumset1(X4,X4,X4)) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f299,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(subsumption_resolution,[],[f117,f112])).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_enumset1(X0,X0,X0)
      | ~ r2_hidden(X0,k1_enumset1(X0,X0,X0)) ) ),
    inference(superposition,[],[f81,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f77,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f299,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ r2_hidden(sK4,k1_enumset1(X4,X4,X4))
        | k1_xboole_0 = k1_enumset1(X4,X4,X4) )
    | ~ spl7_1 ),
    inference(superposition,[],[f280,f243])).

fof(f243,plain,(
    ! [X0] : sK5(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | sK5(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(equality_factoring,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( sK5(k1_enumset1(X0,X0,X1)) = X0
      | sK5(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f120,f127])).

fof(f127,plain,(
    ! [X2,X3] : k1_xboole_0 != k1_enumset1(X2,X2,X3) ),
    inference(subsumption_resolution,[],[f125,f113])).

fof(f113,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f95,f93])).

fof(f93,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f125,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_enumset1(X2,X2,X3)
      | ~ r2_hidden(X3,k1_enumset1(X2,X2,X3)) ) ),
    inference(superposition,[],[f85,f111])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f69,f52,f52])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f120,plain,(
    ! [X0,X1] :
      ( sK5(k1_enumset1(X0,X0,X1)) = X0
      | sK5(k1_enumset1(X0,X0,X1)) = X1
      | k1_xboole_0 = k1_enumset1(X0,X0,X1) ) ),
    inference(resolution,[],[f119,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f280,plain,
    ( ! [X0] :
        ( sK4 != sK5(X0)
        | ~ r2_hidden(sK4,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1 ),
    inference(superposition,[],[f79,f279])).

fof(f279,plain,
    ( sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f276,f277])).

fof(f277,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f182,f99])).

fof(f99,plain,
    ( sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_1
  <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f182,plain,(
    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f181,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
            | k6_mcart_1(sK1,sK2,sK3,X3) = X3
            | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
          | k6_mcart_1(sK1,sK2,sK3,X3) = X3
          | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
   => ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f181,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f180,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f180,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f179,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f179,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f90,f76])).

fof(f76,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f42,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

% (7627)Refutation not found, incomplete strategy% (7627)------------------------------
% (7627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7627)Termination reason: Refutation not found, incomplete strategy

% (7627)Memory used [KB]: 10618
fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f59])).

% (7627)Time elapsed: 0.119 s
% (7627)------------------------------
% (7627)------------------------------
fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f276,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f269,f177])).

fof(f177,plain,(
    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f174,f41])).

fof(f174,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f89,f76])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f59])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f269,plain,(
    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f202,f182])).

% (7615)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (7628)Refutation not found, incomplete strategy% (7628)------------------------------
% (7628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7628)Termination reason: Refutation not found, incomplete strategy

% (7628)Memory used [KB]: 1791
% (7628)Time elapsed: 0.092 s
% (7628)------------------------------
% (7628)------------------------------
% (7629)Refutation not found, incomplete strategy% (7629)------------------------------
% (7629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7640)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (7634)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f202,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    inference(forward_demodulation,[],[f201,f167])).

fof(f167,plain,(
    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f166,f39])).

fof(f166,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f165,f40])).

fof(f165,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f76])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f59])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

% (7630)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f201,plain,(
    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f200,f39])).

fof(f200,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f199,f40])).

fof(f199,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f198,f41])).

fof(f198,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f87,f76])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f50,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f275,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f273,f114])).

fof(f114,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f91,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f91,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f273,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f269,f270])).

fof(f270,plain,
    ( sK4 = k2_mcart_1(sK4)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f167,f107])).

fof(f107,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_3
  <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f268,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_2 ),
    inference(resolution,[],[f256,f112])).

fof(f256,plain,
    ( ! [X12] : ~ r2_hidden(sK4,k1_enumset1(X12,X12,X12))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f255,f119])).

fof(f255,plain,
    ( ! [X12] :
        ( sK4 != X12
        | ~ r2_hidden(sK4,k1_enumset1(X12,X12,X12)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f248,f118])).

fof(f248,plain,
    ( ! [X12] :
        ( sK4 != X12
        | ~ r2_hidden(sK4,k1_enumset1(X12,X12,X12))
        | k1_xboole_0 = k1_enumset1(X12,X12,X12) )
    | ~ spl7_2 ),
    inference(superposition,[],[f206,f243])).

fof(f206,plain,
    ( ! [X1] :
        ( sK4 != sK5(X1)
        | ~ r2_hidden(sK4,X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_2 ),
    inference(superposition,[],[f78,f204])).

fof(f204,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f203,f182])).

fof(f203,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f202,f103])).

fof(f103,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_2
  <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

% (7616)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f78,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f51,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f43,f105,f101,f97])).

fof(f43,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (7619)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (7617)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (7621)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (7613)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7633)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (7618)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (7611)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (7626)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (7632)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (7625)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.55  % (7625)Refutation not found, incomplete strategy% (7625)------------------------------
% 1.41/0.55  % (7625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (7625)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (7625)Memory used [KB]: 1791
% 1.41/0.55  % (7625)Time elapsed: 0.127 s
% 1.41/0.55  % (7625)------------------------------
% 1.41/0.55  % (7625)------------------------------
% 1.41/0.55  % (7614)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.55  % (7627)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (7628)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.55  % (7624)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.55  % (7629)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (7617)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f312,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(avatar_sat_refutation,[],[f108,f268,f275,f311])).
% 1.41/0.56  fof(f311,plain,(
% 1.41/0.56    ~spl7_1),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f304])).
% 1.41/0.56  fof(f304,plain,(
% 1.41/0.56    $false | ~spl7_1),
% 1.41/0.56    inference(resolution,[],[f303,f112])).
% 1.41/0.56  fof(f112,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.41/0.56    inference(resolution,[],[f95,f94])).
% 1.41/0.56  fof(f94,plain,(
% 1.41/0.56    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.41/0.56    inference(equality_resolution,[],[f61])).
% 1.41/0.56  fof(f61,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f35])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.41/0.56    inference(rectify,[],[f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.41/0.56    inference(flattening,[],[f31])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.41/0.56    inference(nnf_transformation,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.41/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.56  fof(f95,plain,(
% 1.41/0.56    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.41/0.56    inference(equality_resolution,[],[f83])).
% 1.41/0.56  fof(f83,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.41/0.56    inference(definition_unfolding,[],[f66,f52])).
% 1.41/0.56  fof(f52,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.56  fof(f66,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.41/0.56    inference(cnf_transformation,[],[f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.41/0.56    inference(nnf_transformation,[],[f24])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.41/0.56    inference(definition_folding,[],[f4,f23])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.41/0.56  fof(f303,plain,(
% 1.41/0.56    ( ! [X4] : (~r2_hidden(sK4,k1_enumset1(X4,X4,X4))) ) | ~spl7_1),
% 1.41/0.56    inference(subsumption_resolution,[],[f302,f119])).
% 1.41/0.56  fof(f119,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_enumset1(X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.41/0.56    inference(resolution,[],[f60,f95])).
% 1.41/0.56  fof(f60,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.41/0.56    inference(cnf_transformation,[],[f35])).
% 1.41/0.56  fof(f302,plain,(
% 1.41/0.56    ( ! [X4] : (sK4 != X4 | ~r2_hidden(sK4,k1_enumset1(X4,X4,X4))) ) | ~spl7_1),
% 1.41/0.56    inference(subsumption_resolution,[],[f299,f118])).
% 1.41/0.56  fof(f118,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f117,f112])).
% 1.41/0.56  fof(f117,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0) | ~r2_hidden(X0,k1_enumset1(X0,X0,X0))) )),
% 1.41/0.56    inference(superposition,[],[f81,f111])).
% 1.41/0.56  fof(f111,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.41/0.56    inference(forward_demodulation,[],[f77,f45])).
% 1.41/0.56  fof(f45,plain,(
% 1.41/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.41/0.56  fof(f77,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f44,f53])).
% 1.41/0.56  fof(f53,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.41/0.56  fof(f81,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f56,f75])).
% 1.41/0.56  fof(f75,plain,(
% 1.41/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f46,f52])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.56  fof(f56,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f30])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.41/0.56    inference(nnf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.41/0.56  fof(f299,plain,(
% 1.41/0.56    ( ! [X4] : (sK4 != X4 | ~r2_hidden(sK4,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) ) | ~spl7_1),
% 1.41/0.56    inference(superposition,[],[f280,f243])).
% 1.41/0.56  fof(f243,plain,(
% 1.41/0.56    ( ! [X0] : (sK5(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.41/0.56    inference(equality_resolution,[],[f192])).
% 1.41/0.56  fof(f192,plain,(
% 1.41/0.56    ( ! [X0,X1] : (X0 != X1 | sK5(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.41/0.56    inference(equality_factoring,[],[f183])).
% 1.41/0.56  fof(f183,plain,(
% 1.41/0.56    ( ! [X0,X1] : (sK5(k1_enumset1(X0,X0,X1)) = X0 | sK5(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f120,f127])).
% 1.41/0.56  fof(f127,plain,(
% 1.41/0.56    ( ! [X2,X3] : (k1_xboole_0 != k1_enumset1(X2,X2,X3)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f125,f113])).
% 1.41/0.56  fof(f113,plain,(
% 1.41/0.56    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 1.41/0.56    inference(resolution,[],[f95,f93])).
% 1.41/0.56  fof(f93,plain,(
% 1.41/0.56    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.41/0.56    inference(equality_resolution,[],[f62])).
% 1.41/0.56  fof(f62,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f35])).
% 1.41/0.56  fof(f125,plain,(
% 1.41/0.56    ( ! [X2,X3] : (k1_xboole_0 != k1_enumset1(X2,X2,X3) | ~r2_hidden(X3,k1_enumset1(X2,X2,X3))) )),
% 1.41/0.56    inference(superposition,[],[f85,f111])).
% 1.41/0.56  fof(f85,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f69,f52,f52])).
% 1.41/0.56  fof(f69,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.41/0.56    inference(flattening,[],[f37])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.41/0.56    inference(nnf_transformation,[],[f8])).
% 1.41/0.56  fof(f8,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.41/0.56  fof(f120,plain,(
% 1.41/0.56    ( ! [X0,X1] : (sK5(k1_enumset1(X0,X0,X1)) = X0 | sK5(k1_enumset1(X0,X0,X1)) = X1 | k1_xboole_0 = k1_enumset1(X0,X0,X1)) )),
% 1.41/0.56    inference(resolution,[],[f119,f49])).
% 1.41/0.56  fof(f49,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.41/0.56    inference(ennf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,axiom,(
% 1.41/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.41/0.56  fof(f280,plain,(
% 1.41/0.56    ( ! [X0] : (sK4 != sK5(X0) | ~r2_hidden(sK4,X0) | k1_xboole_0 = X0) ) | ~spl7_1),
% 1.41/0.56    inference(superposition,[],[f79,f279])).
% 1.41/0.56  fof(f279,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | ~spl7_1),
% 1.41/0.56    inference(forward_demodulation,[],[f276,f277])).
% 1.41/0.56  fof(f277,plain,(
% 1.41/0.56    sK4 = k1_mcart_1(k1_mcart_1(sK4)) | ~spl7_1),
% 1.41/0.56    inference(backward_demodulation,[],[f182,f99])).
% 1.41/0.56  fof(f99,plain,(
% 1.41/0.56    sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_1),
% 1.41/0.56    inference(avatar_component_clause,[],[f97])).
% 1.41/0.56  fof(f97,plain,(
% 1.41/0.56    spl7_1 <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.41/0.56  fof(f182,plain,(
% 1.41/0.56    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 1.41/0.56    inference(subsumption_resolution,[],[f181,f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    k1_xboole_0 != sK1),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f26,f25])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1)),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    ? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) => ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.41/0.56    inference(ennf_transformation,[],[f17])).
% 1.41/0.56  fof(f17,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.41/0.56    inference(negated_conjecture,[],[f16])).
% 1.41/0.56  fof(f16,conjecture,(
% 1.41/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.41/0.56  fof(f181,plain,(
% 1.41/0.56    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f180,f40])).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    k1_xboole_0 != sK2),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f180,plain,(
% 1.41/0.56    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f179,f41])).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    k1_xboole_0 != sK3),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f179,plain,(
% 1.41/0.56    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(resolution,[],[f90,f76])).
% 1.41/0.56  fof(f76,plain,(
% 1.41/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.41/0.56    inference(definition_unfolding,[],[f42,f59])).
% 1.41/0.56  fof(f59,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  % (7627)Refutation not found, incomplete strategy% (7627)------------------------------
% 1.41/0.56  % (7627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (7627)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (7627)Memory used [KB]: 10618
% 1.41/0.56  fof(f90,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f72,f59])).
% 1.41/0.56  % (7627)Time elapsed: 0.119 s
% 1.41/0.56  % (7627)------------------------------
% 1.41/0.56  % (7627)------------------------------
% 1.41/0.56  fof(f72,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.41/0.56    inference(ennf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.41/0.56  fof(f276,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))),
% 1.41/0.56    inference(forward_demodulation,[],[f269,f177])).
% 1.41/0.56  fof(f177,plain,(
% 1.41/0.56    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.41/0.56    inference(subsumption_resolution,[],[f176,f39])).
% 1.41/0.56  fof(f176,plain,(
% 1.41/0.56    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f175,f40])).
% 1.41/0.56  fof(f175,plain,(
% 1.41/0.56    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f174,f41])).
% 1.41/0.56  fof(f174,plain,(
% 1.41/0.56    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(resolution,[],[f89,f76])).
% 1.41/0.56  fof(f89,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f73,f59])).
% 1.41/0.56  fof(f73,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f269,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.41/0.56    inference(forward_demodulation,[],[f202,f182])).
% 1.41/0.56  % (7615)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.56  % (7628)Refutation not found, incomplete strategy% (7628)------------------------------
% 1.41/0.56  % (7628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (7628)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (7628)Memory used [KB]: 1791
% 1.41/0.56  % (7628)Time elapsed: 0.092 s
% 1.41/0.56  % (7628)------------------------------
% 1.41/0.56  % (7628)------------------------------
% 1.41/0.56  % (7629)Refutation not found, incomplete strategy% (7629)------------------------------
% 1.41/0.56  % (7629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (7640)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.56  % (7634)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.56  fof(f202,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 1.41/0.56    inference(forward_demodulation,[],[f201,f167])).
% 1.41/0.56  fof(f167,plain,(
% 1.41/0.56    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 1.41/0.56    inference(subsumption_resolution,[],[f166,f39])).
% 1.41/0.56  fof(f166,plain,(
% 1.41/0.56    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f165,f40])).
% 1.41/0.56  fof(f165,plain,(
% 1.41/0.56    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f164,f41])).
% 1.41/0.56  fof(f164,plain,(
% 1.41/0.56    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(resolution,[],[f88,f76])).
% 1.41/0.56  fof(f88,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f74,f59])).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  % (7630)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.56  fof(f201,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))),
% 1.41/0.56    inference(subsumption_resolution,[],[f200,f39])).
% 1.41/0.56  fof(f200,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f199,f40])).
% 1.41/0.56  fof(f199,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(subsumption_resolution,[],[f198,f41])).
% 1.41/0.56  fof(f198,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.41/0.56    inference(resolution,[],[f87,f76])).
% 1.41/0.56  fof(f87,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f71,f58,f59])).
% 1.41/0.56  fof(f58,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.41/0.56  fof(f71,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.41/0.56    inference(ennf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.41/0.56  fof(f79,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f50,f58])).
% 1.41/0.56  fof(f50,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f275,plain,(
% 1.41/0.56    ~spl7_3),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f274])).
% 1.41/0.56  fof(f274,plain,(
% 1.41/0.56    $false | ~spl7_3),
% 1.41/0.56    inference(subsumption_resolution,[],[f273,f114])).
% 1.41/0.56  fof(f114,plain,(
% 1.41/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.41/0.56    inference(forward_demodulation,[],[f91,f55])).
% 1.41/0.56  fof(f55,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,axiom,(
% 1.41/0.56    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.41/0.56  fof(f91,plain,(
% 1.41/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.41/0.56    inference(equality_resolution,[],[f48])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.41/0.56    inference(ennf_transformation,[],[f11])).
% 1.41/0.56  fof(f11,axiom,(
% 1.41/0.56    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.41/0.56  fof(f273,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4) | ~spl7_3),
% 1.41/0.56    inference(forward_demodulation,[],[f269,f270])).
% 1.41/0.56  fof(f270,plain,(
% 1.41/0.56    sK4 = k2_mcart_1(sK4) | ~spl7_3),
% 1.41/0.56    inference(backward_demodulation,[],[f167,f107])).
% 1.41/0.56  fof(f107,plain,(
% 1.41/0.56    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_3),
% 1.41/0.56    inference(avatar_component_clause,[],[f105])).
% 1.41/0.56  fof(f105,plain,(
% 1.41/0.56    spl7_3 <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.41/0.56  fof(f268,plain,(
% 1.41/0.56    ~spl7_2),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 1.41/0.56  fof(f261,plain,(
% 1.41/0.56    $false | ~spl7_2),
% 1.41/0.56    inference(resolution,[],[f256,f112])).
% 1.41/0.56  fof(f256,plain,(
% 1.41/0.56    ( ! [X12] : (~r2_hidden(sK4,k1_enumset1(X12,X12,X12))) ) | ~spl7_2),
% 1.41/0.56    inference(subsumption_resolution,[],[f255,f119])).
% 1.41/0.56  fof(f255,plain,(
% 1.41/0.56    ( ! [X12] : (sK4 != X12 | ~r2_hidden(sK4,k1_enumset1(X12,X12,X12))) ) | ~spl7_2),
% 1.41/0.56    inference(subsumption_resolution,[],[f248,f118])).
% 1.41/0.56  fof(f248,plain,(
% 1.41/0.56    ( ! [X12] : (sK4 != X12 | ~r2_hidden(sK4,k1_enumset1(X12,X12,X12)) | k1_xboole_0 = k1_enumset1(X12,X12,X12)) ) | ~spl7_2),
% 1.41/0.56    inference(superposition,[],[f206,f243])).
% 1.41/0.56  fof(f206,plain,(
% 1.41/0.56    ( ! [X1] : (sK4 != sK5(X1) | ~r2_hidden(sK4,X1) | k1_xboole_0 = X1) ) | ~spl7_2),
% 1.41/0.56    inference(superposition,[],[f78,f204])).
% 1.41/0.56  fof(f204,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) | ~spl7_2),
% 1.41/0.56    inference(forward_demodulation,[],[f203,f182])).
% 1.41/0.56  fof(f203,plain,(
% 1.41/0.56    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4)) | ~spl7_2),
% 1.41/0.56    inference(forward_demodulation,[],[f202,f103])).
% 1.41/0.56  fof(f103,plain,(
% 1.41/0.56    sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_2),
% 1.41/0.56    inference(avatar_component_clause,[],[f101])).
% 1.41/0.56  fof(f101,plain,(
% 1.41/0.56    spl7_2 <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.41/0.56  % (7616)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.56  fof(f78,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(definition_unfolding,[],[f51,f58])).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f108,plain,(
% 1.41/0.56    spl7_1 | spl7_2 | spl7_3),
% 1.41/0.56    inference(avatar_split_clause,[],[f43,f105,f101,f97])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (7617)------------------------------
% 1.41/0.56  % (7617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (7617)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (7617)Memory used [KB]: 10874
% 1.41/0.56  % (7617)Time elapsed: 0.124 s
% 1.41/0.56  % (7617)------------------------------
% 1.41/0.56  % (7617)------------------------------
% 1.41/0.56  % (7612)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.56  % (7631)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.56  % (7610)Success in time 0.194 s
%------------------------------------------------------------------------------
