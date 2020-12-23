%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 326 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  434 (1336 expanded)
%              Number of equality atoms :  256 ( 849 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f330,f338,f352,f359,f376,f377,f577,f785])).

fof(f785,plain,
    ( ~ spl7_1
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(resolution,[],[f742,f109])).

fof(f109,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f88,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f88,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f742,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(superposition,[],[f112,f703])).

% (17479)Refutation not found, incomplete strategy% (17479)------------------------------
% (17479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f703,plain,
    ( k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f696])).

% (17479)Termination reason: Refutation not found, incomplete strategy

% (17479)Memory used [KB]: 1791
% (17479)Time elapsed: 0.125 s
% (17479)------------------------------
% (17479)------------------------------
fof(f696,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(resolution,[],[f580,f112])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k1_enumset1(X0,X0,X0))
        | sK4 != X0
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(superposition,[],[f147,f579])).

fof(f579,plain,
    ( sK4 = k4_tarski(k4_tarski(sK4,k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f342,f96])).

fof(f96,plain,
    ( sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_1
  <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f342,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl7_8
  <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f79,f136])).

fof(f136,plain,(
    ! [X0] :
      ( sK5(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(resolution,[],[f135,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f133,f109])).

fof(f133,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | X2 = X3
      | ~ r2_hidden(X3,k1_enumset1(X2,X2,X2)) ) ),
    inference(superposition,[],[f82,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f77,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

% (17493)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f92,f91])).

fof(f91,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

% (17490)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f92,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f577,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl7_7 ),
    inference(resolution,[],[f534,f109])).

fof(f534,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_7 ),
    inference(superposition,[],[f112,f487])).

fof(f487,plain,
    ( k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f480])).

fof(f480,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_7 ),
    inference(resolution,[],[f380,f112])).

fof(f380,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4,k1_enumset1(X1,X1,X1))
        | sK4 != X1
        | k1_xboole_0 = k1_enumset1(X1,X1,X1) )
    | ~ spl7_7 ),
    inference(superposition,[],[f146,f329])).

fof(f329,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl7_7
  <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f146,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_enumset1(X4,X4,X4))
      | k1_xboole_0 = k1_enumset1(X4,X4,X4) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_enumset1(X4,X4,X4))
      | k1_xboole_0 = k1_enumset1(X4,X4,X4)
      | k1_xboole_0 = k1_enumset1(X4,X4,X4) ) ),
    inference(superposition,[],[f78,f136])).

fof(f78,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f52,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f377,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_8 ),
    inference(avatar_split_clause,[],[f361,f340,f323,f319,f315])).

fof(f315,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f319,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f323,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f361,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f76,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f60,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f76,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f376,plain,
    ( ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f371])).

fof(f371,plain,
    ( sK4 != sK4
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(superposition,[],[f107,f360])).

fof(f360,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4)
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f342,f104])).

fof(f104,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_3
  <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f107,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

% (17490)Refutation not found, incomplete strategy% (17490)------------------------------
% (17490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17490)Termination reason: Refutation not found, incomplete strategy

% (17490)Memory used [KB]: 10618
% (17490)Time elapsed: 0.125 s
% (17490)------------------------------
% (17490)------------------------------
% (17481)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f86,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f359,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl7_6 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_6 ),
    inference(superposition,[],[f41,f325])).

fof(f325,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f323])).

fof(f41,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f352,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f350])).

fof(f350,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_5 ),
    inference(superposition,[],[f40,f321])).

fof(f321,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f319])).

% (17482)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f338,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_4 ),
    inference(superposition,[],[f39,f317])).

fof(f317,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f315])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f330,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f313,f98,f327,f323,f319,f315])).

fof(f98,plain,
    ( spl7_2
  <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f313,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f312,f100])).

fof(f100,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f312,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f85,f76])).

fof(f105,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f43,f102,f98,f94])).

fof(f43,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (17491)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (17507)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (17483)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (17488)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (17480)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (17499)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.52  % (17501)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.52  % (17479)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.52  % (17491)Refutation found. Thanks to Tanya!
% 1.32/0.52  % SZS status Theorem for theBenchmark
% 1.32/0.52  % SZS output start Proof for theBenchmark
% 1.32/0.52  fof(f786,plain,(
% 1.32/0.52    $false),
% 1.32/0.52    inference(avatar_sat_refutation,[],[f105,f330,f338,f352,f359,f376,f377,f577,f785])).
% 1.32/0.52  fof(f785,plain,(
% 1.32/0.52    ~spl7_1 | ~spl7_8),
% 1.32/0.52    inference(avatar_contradiction_clause,[],[f784])).
% 1.32/0.52  fof(f784,plain,(
% 1.32/0.52    $false | (~spl7_1 | ~spl7_8)),
% 1.32/0.52    inference(resolution,[],[f742,f109])).
% 1.32/0.52  fof(f109,plain,(
% 1.32/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.52    inference(superposition,[],[f88,f45])).
% 1.32/0.52  fof(f45,plain,(
% 1.32/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f4])).
% 1.32/0.52  fof(f4,axiom,(
% 1.32/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.32/0.52  fof(f88,plain,(
% 1.32/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.32/0.52    inference(equality_resolution,[],[f83])).
% 1.32/0.52  fof(f83,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.32/0.52    inference(definition_unfolding,[],[f62,f75])).
% 1.32/0.52  fof(f75,plain,(
% 1.32/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f47,f53])).
% 1.32/0.52  fof(f53,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f7])).
% 1.32/0.52  fof(f7,axiom,(
% 1.32/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.52  fof(f47,plain,(
% 1.32/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f6])).
% 1.32/0.52  fof(f6,axiom,(
% 1.32/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.52  fof(f62,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f32])).
% 1.32/0.52  fof(f32,plain,(
% 1.32/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.32/0.52    inference(flattening,[],[f31])).
% 1.32/0.52  fof(f31,plain,(
% 1.32/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.32/0.52    inference(nnf_transformation,[],[f8])).
% 1.32/0.52  fof(f8,axiom,(
% 1.32/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.32/0.52  fof(f742,plain,(
% 1.32/0.52    r2_hidden(sK4,k1_xboole_0) | (~spl7_1 | ~spl7_8)),
% 1.32/0.52    inference(superposition,[],[f112,f703])).
% 1.32/0.52  % (17479)Refutation not found, incomplete strategy% (17479)------------------------------
% 1.32/0.52  % (17479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  fof(f703,plain,(
% 1.32/0.52    k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | (~spl7_1 | ~spl7_8)),
% 1.32/0.52    inference(trivial_inequality_removal,[],[f696])).
% 1.32/0.53  % (17479)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (17479)Memory used [KB]: 1791
% 1.32/0.53  % (17479)Time elapsed: 0.125 s
% 1.32/0.53  % (17479)------------------------------
% 1.32/0.53  % (17479)------------------------------
% 1.32/0.53  fof(f696,plain,(
% 1.32/0.53    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | (~spl7_1 | ~spl7_8)),
% 1.32/0.53    inference(resolution,[],[f580,f112])).
% 1.32/0.53  fof(f580,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK4,k1_enumset1(X0,X0,X0)) | sK4 != X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | (~spl7_1 | ~spl7_8)),
% 1.32/0.53    inference(superposition,[],[f147,f579])).
% 1.32/0.53  fof(f579,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(sK4,k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | (~spl7_1 | ~spl7_8)),
% 1.32/0.53    inference(backward_demodulation,[],[f342,f96])).
% 1.32/0.53  fof(f96,plain,(
% 1.32/0.53    sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_1),
% 1.32/0.53    inference(avatar_component_clause,[],[f94])).
% 1.32/0.53  fof(f94,plain,(
% 1.32/0.53    spl7_1 <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.32/0.53  fof(f342,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | ~spl7_8),
% 1.32/0.53    inference(avatar_component_clause,[],[f340])).
% 1.32/0.53  fof(f340,plain,(
% 1.32/0.53    spl7_8 <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.32/0.53  fof(f147,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f142])).
% 1.32/0.53  fof(f142,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f79,f136])).
% 1.32/0.53  fof(f136,plain,(
% 1.32/0.53    ( ! [X0] : (sK5(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.32/0.53    inference(resolution,[],[f135,f50])).
% 1.32/0.53  fof(f50,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,axiom,(
% 1.32/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.32/0.53  fof(f135,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | X0 = X1) )),
% 1.32/0.53    inference(resolution,[],[f133,f109])).
% 1.32/0.53  fof(f133,plain,(
% 1.32/0.53    ( ! [X2,X3] : (r2_hidden(X3,k1_xboole_0) | X2 = X3 | ~r2_hidden(X3,k1_enumset1(X2,X2,X2))) )),
% 1.32/0.53    inference(superposition,[],[f82,f106])).
% 1.32/0.53  fof(f106,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.32/0.53    inference(backward_demodulation,[],[f77,f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.32/0.53  fof(f77,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f44,f54])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.32/0.53  % (17493)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  fof(f82,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f63,f75])).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f32])).
% 1.32/0.53  fof(f79,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(definition_unfolding,[],[f51,f60])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f112,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.32/0.53    inference(resolution,[],[f92,f91])).
% 1.32/0.53  fof(f91,plain,(
% 1.32/0.53    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.32/0.53    inference(equality_resolution,[],[f66])).
% 1.32/0.53  fof(f66,plain,(
% 1.32/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.32/0.53    inference(rectify,[],[f34])).
% 1.32/0.53  % (17490)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.32/0.53    inference(flattening,[],[f33])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.32/0.53    inference(nnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.32/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.53  fof(f92,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.32/0.53    inference(equality_resolution,[],[f73])).
% 1.32/0.53  fof(f73,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.32/0.53    inference(cnf_transformation,[],[f38])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.53    inference(nnf_transformation,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.32/0.53    inference(definition_folding,[],[f22,f23])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.32/0.53  fof(f577,plain,(
% 1.32/0.53    ~spl7_7),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f576])).
% 1.32/0.53  fof(f576,plain,(
% 1.32/0.53    $false | ~spl7_7),
% 1.32/0.53    inference(resolution,[],[f534,f109])).
% 1.32/0.53  fof(f534,plain,(
% 1.32/0.53    r2_hidden(sK4,k1_xboole_0) | ~spl7_7),
% 1.32/0.53    inference(superposition,[],[f112,f487])).
% 1.32/0.53  fof(f487,plain,(
% 1.32/0.53    k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | ~spl7_7),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f480])).
% 1.32/0.53  fof(f480,plain,(
% 1.32/0.53    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | ~spl7_7),
% 1.32/0.53    inference(resolution,[],[f380,f112])).
% 1.32/0.53  fof(f380,plain,(
% 1.32/0.53    ( ! [X1] : (~r2_hidden(sK4,k1_enumset1(X1,X1,X1)) | sK4 != X1 | k1_xboole_0 = k1_enumset1(X1,X1,X1)) ) | ~spl7_7),
% 1.32/0.53    inference(superposition,[],[f146,f329])).
% 1.32/0.53  fof(f329,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4)) | ~spl7_7),
% 1.32/0.53    inference(avatar_component_clause,[],[f327])).
% 1.32/0.53  fof(f327,plain,(
% 1.32/0.53    spl7_7 <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4))),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.32/0.53  fof(f146,plain,(
% 1.32/0.53    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) )),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f143])).
% 1.32/0.53  fof(f143,plain,(
% 1.32/0.53    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) )),
% 1.32/0.53    inference(superposition,[],[f78,f136])).
% 1.32/0.53  fof(f78,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(definition_unfolding,[],[f52,f60])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f377,plain,(
% 1.32/0.53    spl7_4 | spl7_5 | spl7_6 | spl7_8),
% 1.32/0.53    inference(avatar_split_clause,[],[f361,f340,f323,f319,f315])).
% 1.32/0.53  fof(f315,plain,(
% 1.32/0.53    spl7_4 <=> k1_xboole_0 = sK1),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.32/0.53  fof(f319,plain,(
% 1.32/0.53    spl7_5 <=> k1_xboole_0 = sK2),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.32/0.53  fof(f323,plain,(
% 1.32/0.53    spl7_6 <=> k1_xboole_0 = sK3),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.32/0.53  fof(f361,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.32/0.53    inference(resolution,[],[f76,f85])).
% 1.32/0.53  fof(f85,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(definition_unfolding,[],[f64,f60,f59])).
% 1.32/0.53  fof(f59,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.32/0.53  fof(f64,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.32/0.53    inference(definition_unfolding,[],[f42,f59])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f26,f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1)),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) => ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.32/0.53    inference(negated_conjecture,[],[f16])).
% 1.32/0.53  fof(f16,conjecture,(
% 1.32/0.53    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.32/0.53  fof(f376,plain,(
% 1.32/0.53    ~spl7_3 | ~spl7_8),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f375])).
% 1.32/0.53  fof(f375,plain,(
% 1.32/0.53    $false | (~spl7_3 | ~spl7_8)),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f371])).
% 1.32/0.53  fof(f371,plain,(
% 1.32/0.53    sK4 != sK4 | (~spl7_3 | ~spl7_8)),
% 1.32/0.53    inference(superposition,[],[f107,f360])).
% 1.32/0.53  fof(f360,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4) | (~spl7_3 | ~spl7_8)),
% 1.32/0.53    inference(forward_demodulation,[],[f342,f104])).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_3),
% 1.32/0.53    inference(avatar_component_clause,[],[f102])).
% 1.32/0.53  fof(f102,plain,(
% 1.32/0.53    spl7_3 <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.32/0.53  fof(f107,plain,(
% 1.32/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.32/0.53    inference(backward_demodulation,[],[f86,f56])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,axiom,(
% 1.32/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.32/0.53  % (17490)Refutation not found, incomplete strategy% (17490)------------------------------
% 1.32/0.53  % (17490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (17490)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (17490)Memory used [KB]: 10618
% 1.32/0.53  % (17490)Time elapsed: 0.125 s
% 1.32/0.53  % (17490)------------------------------
% 1.32/0.53  % (17490)------------------------------
% 1.32/0.53  % (17481)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  fof(f86,plain,(
% 1.32/0.53    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.32/0.53    inference(equality_resolution,[],[f49])).
% 1.32/0.53  fof(f49,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.32/0.53  fof(f359,plain,(
% 1.32/0.53    ~spl7_6),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f358])).
% 1.32/0.53  fof(f358,plain,(
% 1.32/0.53    $false | ~spl7_6),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f357])).
% 1.32/0.53  fof(f357,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0 | ~spl7_6),
% 1.32/0.53    inference(superposition,[],[f41,f325])).
% 1.32/0.53  fof(f325,plain,(
% 1.32/0.53    k1_xboole_0 = sK3 | ~spl7_6),
% 1.32/0.53    inference(avatar_component_clause,[],[f323])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    k1_xboole_0 != sK3),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f352,plain,(
% 1.32/0.53    ~spl7_5),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f351])).
% 1.32/0.53  fof(f351,plain,(
% 1.32/0.53    $false | ~spl7_5),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f350])).
% 1.32/0.53  fof(f350,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0 | ~spl7_5),
% 1.32/0.53    inference(superposition,[],[f40,f321])).
% 1.32/0.53  fof(f321,plain,(
% 1.32/0.53    k1_xboole_0 = sK2 | ~spl7_5),
% 1.32/0.53    inference(avatar_component_clause,[],[f319])).
% 1.32/0.53  % (17482)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    k1_xboole_0 != sK2),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f338,plain,(
% 1.32/0.53    ~spl7_4),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f337])).
% 1.32/0.53  fof(f337,plain,(
% 1.32/0.53    $false | ~spl7_4),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f336])).
% 1.32/0.53  fof(f336,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0 | ~spl7_4),
% 1.32/0.53    inference(superposition,[],[f39,f317])).
% 1.32/0.53  fof(f317,plain,(
% 1.32/0.53    k1_xboole_0 = sK1 | ~spl7_4),
% 1.32/0.53    inference(avatar_component_clause,[],[f315])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    k1_xboole_0 != sK1),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f330,plain,(
% 1.32/0.53    spl7_4 | spl7_5 | spl7_6 | spl7_7 | ~spl7_2),
% 1.32/0.53    inference(avatar_split_clause,[],[f313,f98,f327,f323,f319,f315])).
% 1.32/0.53  fof(f98,plain,(
% 1.32/0.53    spl7_2 <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.32/0.53  fof(f313,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~spl7_2),
% 1.32/0.53    inference(forward_demodulation,[],[f312,f100])).
% 1.32/0.53  fof(f100,plain,(
% 1.32/0.53    sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_2),
% 1.32/0.53    inference(avatar_component_clause,[],[f98])).
% 1.32/0.53  fof(f312,plain,(
% 1.32/0.53    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.32/0.53    inference(resolution,[],[f85,f76])).
% 1.32/0.53  fof(f105,plain,(
% 1.32/0.53    spl7_1 | spl7_2 | spl7_3),
% 1.32/0.53    inference(avatar_split_clause,[],[f43,f102,f98,f94])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (17491)------------------------------
% 1.32/0.53  % (17491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (17491)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (17491)Memory used [KB]: 6652
% 1.32/0.53  % (17491)Time elapsed: 0.122 s
% 1.32/0.53  % (17491)------------------------------
% 1.32/0.53  % (17491)------------------------------
% 1.32/0.53  % (17478)Success in time 0.179 s
%------------------------------------------------------------------------------
