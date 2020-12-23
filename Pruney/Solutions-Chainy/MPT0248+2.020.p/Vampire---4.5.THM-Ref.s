%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:51 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 961 expanded)
%              Number of leaves         :   35 ( 326 expanded)
%              Depth                    :   17
%              Number of atoms          :  459 (2023 expanded)
%              Number of equality atoms :  172 (1446 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f128,f129,f208,f233,f249,f324,f504,f527,f535,f543,f760,f768])).

fof(f768,plain,
    ( spl7_2
    | spl7_11
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f767,f758,f247,f119])).

fof(f119,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f247,plain,
    ( spl7_11
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f758,plain,
    ( spl7_22
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f767,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_22 ),
    inference(superposition,[],[f54,f759])).

fof(f759,plain,
    ( sK0 = sK3(sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f758])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f760,plain,
    ( spl7_2
    | spl7_22
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f750,f116,f758,f119])).

fof(f116,plain,
    ( spl7_1
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f750,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f743,f54])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl7_1 ),
    inference(resolution,[],[f602,f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f134,f111])).

fof(f111,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f133,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f93,f92])).

fof(f92,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f48,f88,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f602,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f582,f66])).

fof(f582,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f400,f140])).

fof(f140,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f400,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f93,f157])).

fof(f157,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f156,f92])).

fof(f156,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f155,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f57,f87,f87])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f155,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f154,f97])).

fof(f97,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f61,f87,f87])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f154,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f97,f131])).

% (9783)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f131,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) ),
    inference(superposition,[],[f96,f92])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f60,f87])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f543,plain,
    ( spl7_5
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f144,f232])).

fof(f232,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_9
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl7_5 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1)
    | spl7_5 ),
    inference(resolution,[],[f139,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f83,f86])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f139,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_5
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f535,plain,
    ( ~ spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f533,f116,f138])).

fof(f533,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f133,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f527,plain,
    ( ~ spl7_11
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl7_11
    | spl7_17 ),
    inference(subsumption_resolution,[],[f248,f516])).

fof(f516,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl7_17 ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl7_17 ),
    inference(resolution,[],[f502,f104])).

fof(f502,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl7_17
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f248,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f504,plain,
    ( ~ spl7_17
    | spl7_4 ),
    inference(avatar_split_clause,[],[f498,f126,f501])).

fof(f126,plain,
    ( spl7_4
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f498,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) ),
    inference(resolution,[],[f400,f65])).

fof(f324,plain,
    ( ~ spl7_3
    | spl7_5
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl7_3
    | spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f168,f313])).

fof(f313,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f312,f289])).

fof(f289,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f282,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f282,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),sK2)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f159,f204])).

fof(f204,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f159,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(superposition,[],[f130,f132])).

fof(f132,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f94,f92])).

fof(f94,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f130,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(X0,sK1),sK2) = k4_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f103,f92])).

fof(f103,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f312,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_xboole_0,sK2))
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f245,f204])).

fof(f245,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_10
  <=> r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl7_5 ),
    inference(resolution,[],[f145,f144])).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f114,f132])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f249,plain,
    ( spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f236,f247,f244])).

fof(f236,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f153,f110])).

fof(f110,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f153,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X2,sK2)
      | r2_hidden(X2,k4_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f112,f131])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f233,plain,
    ( spl7_3
    | spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f229,f206,f231,f123])).

fof(f206,plain,
    ( spl7_6
  <=> sK0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f229,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl7_6 ),
    inference(superposition,[],[f54,f207])).

fof(f207,plain,
    ( sK0 = sK3(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f198,f206,f123])).

fof(f198,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f187,f54])).

fof(f129,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f91,f126,f116])).

fof(f91,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f49,f88,f88])).

fof(f49,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f90,f126,f123])).

fof(f90,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f50,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f89,f119,f116])).

fof(f89,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f51,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (9771)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (9765)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (9787)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (9781)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (9762)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (9763)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.52  % (9779)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.52  % (9782)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (9772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.52  % (9774)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.52  % (9760)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (9773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (9784)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.53  % (9785)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.53  % (9766)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (9777)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (9788)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (9780)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (9776)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.54  % (9771)Refutation not found, incomplete strategy% (9771)------------------------------
% 1.40/0.54  % (9771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (9768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.54  % (9771)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (9771)Memory used [KB]: 10874
% 1.40/0.54  % (9771)Time elapsed: 0.113 s
% 1.40/0.54  % (9771)------------------------------
% 1.40/0.54  % (9771)------------------------------
% 1.40/0.54  % (9769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.54  % (9786)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (9761)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.55  % (9789)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (9778)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (9770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.56  % (9775)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.56  % (9770)Refutation not found, incomplete strategy% (9770)------------------------------
% 1.40/0.56  % (9770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (9770)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (9770)Memory used [KB]: 10618
% 1.40/0.56  % (9770)Time elapsed: 0.151 s
% 1.40/0.56  % (9770)------------------------------
% 1.40/0.56  % (9770)------------------------------
% 1.40/0.56  % (9762)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.56  % SZS output start Proof for theBenchmark
% 1.40/0.56  fof(f769,plain,(
% 1.40/0.56    $false),
% 1.40/0.56    inference(avatar_sat_refutation,[],[f121,f128,f129,f208,f233,f249,f324,f504,f527,f535,f543,f760,f768])).
% 1.40/0.56  fof(f768,plain,(
% 1.40/0.56    spl7_2 | spl7_11 | ~spl7_22),
% 1.40/0.56    inference(avatar_split_clause,[],[f767,f758,f247,f119])).
% 1.40/0.56  fof(f119,plain,(
% 1.40/0.56    spl7_2 <=> k1_xboole_0 = sK2),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.40/0.56  fof(f247,plain,(
% 1.40/0.56    spl7_11 <=> r2_hidden(sK0,sK2)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.40/0.56  fof(f758,plain,(
% 1.40/0.56    spl7_22 <=> sK0 = sK3(sK2)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.40/0.56  fof(f767,plain,(
% 1.40/0.56    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl7_22),
% 1.40/0.56    inference(superposition,[],[f54,f759])).
% 1.40/0.56  fof(f759,plain,(
% 1.40/0.56    sK0 = sK3(sK2) | ~spl7_22),
% 1.40/0.56    inference(avatar_component_clause,[],[f758])).
% 1.40/0.56  fof(f54,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f30])).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f29])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.40/0.56    inference(ennf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.40/0.56  fof(f760,plain,(
% 1.40/0.56    spl7_2 | spl7_22 | ~spl7_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f750,f116,f758,f119])).
% 1.40/0.56  fof(f116,plain,(
% 1.40/0.56    spl7_1 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.40/0.56  fof(f750,plain,(
% 1.40/0.56    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl7_1),
% 1.40/0.56    inference(resolution,[],[f743,f54])).
% 1.40/0.56  fof(f743,plain,(
% 1.40/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl7_1),
% 1.40/0.56    inference(resolution,[],[f602,f187])).
% 1.40/0.56  fof(f187,plain,(
% 1.40/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.40/0.56    inference(resolution,[],[f134,f111])).
% 1.40/0.56  fof(f111,plain,(
% 1.40/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.40/0.56    inference(equality_resolution,[],[f102])).
% 1.40/0.56  fof(f102,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.40/0.56    inference(definition_unfolding,[],[f69,f88])).
% 1.40/0.56  fof(f88,plain,(
% 1.40/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f53,f86])).
% 1.40/0.56  fof(f86,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f59,f85])).
% 1.40/0.56  fof(f85,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f73,f84])).
% 1.40/0.56  fof(f84,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f18])).
% 1.40/0.56  fof(f18,axiom,(
% 1.40/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  fof(f17,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.56  fof(f59,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f16])).
% 1.40/0.56  fof(f16,axiom,(
% 1.40/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  fof(f15,axiom,(
% 1.40/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.56  fof(f69,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f40])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.40/0.56  fof(f39,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f38,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.56    inference(rectify,[],[f37])).
% 1.40/0.56  fof(f37,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.56    inference(nnf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,axiom,(
% 1.40/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.40/0.56  fof(f134,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.40/0.56    inference(resolution,[],[f133,f66])).
% 1.40/0.56  fof(f66,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f36])).
% 1.40/0.56  fof(f36,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(rectify,[],[f33])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(nnf_transformation,[],[f26])).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.56  fof(f133,plain,(
% 1.40/0.56    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.40/0.56    inference(superposition,[],[f93,f92])).
% 1.40/0.56  fof(f92,plain,(
% 1.40/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.40/0.56    inference(definition_unfolding,[],[f48,f88,f87])).
% 1.40/0.56  fof(f87,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f58,f86])).
% 1.40/0.56  fof(f58,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f19])).
% 1.40/0.56  fof(f19,axiom,(
% 1.40/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.40/0.56  fof(f48,plain,(
% 1.40/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f22])).
% 1.40/0.56  fof(f22,negated_conjecture,(
% 1.40/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.40/0.56    inference(negated_conjecture,[],[f21])).
% 1.40/0.56  fof(f21,conjecture,(
% 1.40/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.40/0.56  fof(f93,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f55,f87])).
% 1.40/0.56  fof(f55,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f13])).
% 1.40/0.56  fof(f13,axiom,(
% 1.40/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.40/0.56  fof(f602,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) ) | ~spl7_1),
% 1.40/0.56    inference(resolution,[],[f582,f66])).
% 1.40/0.56  fof(f582,plain,(
% 1.40/0.56    r1_tarski(sK2,sK1) | ~spl7_1),
% 1.40/0.56    inference(backward_demodulation,[],[f400,f140])).
% 1.40/0.56  fof(f140,plain,(
% 1.40/0.56    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl7_1),
% 1.40/0.56    inference(avatar_component_clause,[],[f116])).
% 1.40/0.56  fof(f400,plain,(
% 1.40/0.56    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.40/0.56    inference(superposition,[],[f93,f157])).
% 1.40/0.56  fof(f157,plain,(
% 1.40/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.40/0.56    inference(forward_demodulation,[],[f156,f92])).
% 1.40/0.56  fof(f156,plain,(
% 1.40/0.56    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.40/0.56    inference(forward_demodulation,[],[f155,f95])).
% 1.40/0.56  fof(f95,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f57,f87,f87])).
% 1.40/0.56  fof(f57,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.40/0.56  fof(f155,plain,(
% 1.40/0.56    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.40/0.56    inference(forward_demodulation,[],[f154,f97])).
% 1.40/0.56  fof(f97,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f61,f87,f87])).
% 1.40/0.56  fof(f61,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f8])).
% 1.40/0.56  fof(f8,axiom,(
% 1.40/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.40/0.56  fof(f154,plain,(
% 1.40/0.56    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k4_xboole_0(sK1,sK2)))),
% 1.40/0.56    inference(superposition,[],[f97,f131])).
% 1.40/0.56  % (9783)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.56  fof(f131,plain,(
% 1.40/0.56    k4_xboole_0(sK1,sK2) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),
% 1.40/0.56    inference(superposition,[],[f96,f92])).
% 1.40/0.56  fof(f96,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f60,f87])).
% 1.40/0.56  fof(f60,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f10])).
% 1.40/0.56  fof(f10,axiom,(
% 1.40/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.40/0.56  fof(f543,plain,(
% 1.40/0.56    spl7_5 | ~spl7_9),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f542])).
% 1.40/0.56  fof(f542,plain,(
% 1.40/0.56    $false | (spl7_5 | ~spl7_9)),
% 1.40/0.56    inference(subsumption_resolution,[],[f144,f232])).
% 1.40/0.56  fof(f232,plain,(
% 1.40/0.56    r2_hidden(sK0,sK1) | ~spl7_9),
% 1.40/0.56    inference(avatar_component_clause,[],[f231])).
% 1.40/0.56  fof(f231,plain,(
% 1.40/0.56    spl7_9 <=> r2_hidden(sK0,sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.40/0.56  fof(f144,plain,(
% 1.40/0.56    ~r2_hidden(sK0,sK1) | spl7_5),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f142])).
% 1.40/0.56  fof(f142,plain,(
% 1.40/0.56    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1) | spl7_5),
% 1.40/0.56    inference(resolution,[],[f139,f104])).
% 1.40/0.56  fof(f104,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.40/0.56    inference(definition_unfolding,[],[f83,f86])).
% 1.40/0.56  fof(f83,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f47])).
% 1.40/0.56  fof(f47,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.40/0.56    inference(flattening,[],[f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.40/0.56    inference(nnf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.40/0.56  fof(f139,plain,(
% 1.40/0.56    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | spl7_5),
% 1.40/0.56    inference(avatar_component_clause,[],[f138])).
% 1.40/0.56  fof(f138,plain,(
% 1.40/0.56    spl7_5 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.40/0.56  fof(f535,plain,(
% 1.40/0.56    ~spl7_5 | spl7_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f533,f116,f138])).
% 1.40/0.56  fof(f533,plain,(
% 1.40/0.56    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.40/0.56    inference(resolution,[],[f133,f65])).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f32])).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.56    inference(flattening,[],[f31])).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.56    inference(nnf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.56  fof(f527,plain,(
% 1.40/0.56    ~spl7_11 | spl7_17),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f526])).
% 1.40/0.56  fof(f526,plain,(
% 1.40/0.56    $false | (~spl7_11 | spl7_17)),
% 1.40/0.56    inference(subsumption_resolution,[],[f248,f516])).
% 1.40/0.56  fof(f516,plain,(
% 1.40/0.56    ~r2_hidden(sK0,sK2) | spl7_17),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f514])).
% 1.40/0.56  fof(f514,plain,(
% 1.40/0.56    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2) | spl7_17),
% 1.40/0.56    inference(resolution,[],[f502,f104])).
% 1.40/0.56  fof(f502,plain,(
% 1.40/0.56    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | spl7_17),
% 1.40/0.56    inference(avatar_component_clause,[],[f501])).
% 1.40/0.56  fof(f501,plain,(
% 1.40/0.56    spl7_17 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.40/0.56  fof(f248,plain,(
% 1.40/0.56    r2_hidden(sK0,sK2) | ~spl7_11),
% 1.40/0.56    inference(avatar_component_clause,[],[f247])).
% 1.40/0.56  fof(f504,plain,(
% 1.40/0.56    ~spl7_17 | spl7_4),
% 1.40/0.56    inference(avatar_split_clause,[],[f498,f126,f501])).
% 1.40/0.56  fof(f126,plain,(
% 1.40/0.56    spl7_4 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.40/0.56  fof(f498,plain,(
% 1.40/0.56    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),
% 1.40/0.56    inference(resolution,[],[f400,f65])).
% 1.40/0.56  fof(f324,plain,(
% 1.40/0.56    ~spl7_3 | spl7_5 | ~spl7_10),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f321])).
% 1.40/0.56  fof(f321,plain,(
% 1.40/0.56    $false | (~spl7_3 | spl7_5 | ~spl7_10)),
% 1.40/0.56    inference(subsumption_resolution,[],[f168,f313])).
% 1.40/0.56  fof(f313,plain,(
% 1.40/0.56    r2_hidden(sK0,k1_xboole_0) | (~spl7_3 | ~spl7_10)),
% 1.40/0.56    inference(forward_demodulation,[],[f312,f289])).
% 1.40/0.56  fof(f289,plain,(
% 1.40/0.56    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl7_3),
% 1.40/0.56    inference(forward_demodulation,[],[f282,f52])).
% 1.40/0.56  fof(f52,plain,(
% 1.40/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f9])).
% 1.40/0.56  fof(f9,axiom,(
% 1.40/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.40/0.56  fof(f282,plain,(
% 1.40/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),sK2) | ~spl7_3),
% 1.40/0.56    inference(backward_demodulation,[],[f159,f204])).
% 1.40/0.56  fof(f204,plain,(
% 1.40/0.56    k1_xboole_0 = sK1 | ~spl7_3),
% 1.40/0.56    inference(avatar_component_clause,[],[f123])).
% 1.40/0.56  fof(f123,plain,(
% 1.40/0.56    spl7_3 <=> k1_xboole_0 = sK1),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.40/0.56  fof(f159,plain,(
% 1.40/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2)),
% 1.40/0.56    inference(superposition,[],[f130,f132])).
% 1.40/0.56  fof(f132,plain,(
% 1.40/0.56    k1_xboole_0 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.40/0.56    inference(superposition,[],[f94,f92])).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f56,f87])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f12])).
% 1.40/0.56  fof(f12,axiom,(
% 1.40/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.40/0.56  fof(f130,plain,(
% 1.40/0.56    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,sK1),sK2) = k4_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 1.40/0.56    inference(superposition,[],[f103,f92])).
% 1.40/0.56  fof(f103,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 1.40/0.56    inference(definition_unfolding,[],[f74,f87])).
% 1.40/0.56  fof(f74,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f11])).
% 1.40/0.56  fof(f11,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.40/0.56  fof(f312,plain,(
% 1.40/0.56    r2_hidden(sK0,k4_xboole_0(k1_xboole_0,sK2)) | (~spl7_3 | ~spl7_10)),
% 1.40/0.56    inference(forward_demodulation,[],[f245,f204])).
% 1.40/0.56  fof(f245,plain,(
% 1.40/0.56    r2_hidden(sK0,k4_xboole_0(sK1,sK2)) | ~spl7_10),
% 1.40/0.56    inference(avatar_component_clause,[],[f244])).
% 1.40/0.56  fof(f244,plain,(
% 1.40/0.56    spl7_10 <=> r2_hidden(sK0,k4_xboole_0(sK1,sK2))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.40/0.56  fof(f168,plain,(
% 1.40/0.56    ~r2_hidden(sK0,k1_xboole_0) | spl7_5),
% 1.40/0.56    inference(resolution,[],[f145,f144])).
% 1.40/0.56  fof(f145,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.40/0.56    inference(superposition,[],[f114,f132])).
% 1.40/0.56  fof(f114,plain,(
% 1.40/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.40/0.56    inference(equality_resolution,[],[f75])).
% 1.40/0.56  fof(f75,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.40/0.56    inference(cnf_transformation,[],[f45])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.40/0.56  fof(f44,plain,(
% 1.40/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f43,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(rectify,[],[f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(flattening,[],[f41])).
% 1.40/0.56  fof(f41,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.40/0.56    inference(nnf_transformation,[],[f4])).
% 1.40/0.56  fof(f4,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.40/0.56  fof(f249,plain,(
% 1.40/0.56    spl7_10 | spl7_11),
% 1.40/0.56    inference(avatar_split_clause,[],[f236,f247,f244])).
% 1.40/0.56  fof(f236,plain,(
% 1.40/0.56    r2_hidden(sK0,sK2) | r2_hidden(sK0,k4_xboole_0(sK1,sK2))),
% 1.40/0.56    inference(resolution,[],[f153,f110])).
% 1.40/0.56  fof(f110,plain,(
% 1.40/0.56    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.40/0.56    inference(equality_resolution,[],[f109])).
% 1.40/0.56  fof(f109,plain,(
% 1.40/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.40/0.56    inference(equality_resolution,[],[f101])).
% 1.40/0.56  fof(f101,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.40/0.56    inference(definition_unfolding,[],[f70,f88])).
% 1.40/0.56  fof(f70,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f40])).
% 1.40/0.56  fof(f153,plain,(
% 1.40/0.56    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X2,sK2) | r2_hidden(X2,k4_xboole_0(sK1,sK2))) )),
% 1.40/0.56    inference(superposition,[],[f112,f131])).
% 1.40/0.56  fof(f112,plain,(
% 1.40/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.40/0.56    inference(equality_resolution,[],[f77])).
% 1.40/0.56  fof(f77,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.40/0.56    inference(cnf_transformation,[],[f45])).
% 1.40/0.56  fof(f233,plain,(
% 1.40/0.56    spl7_3 | spl7_9 | ~spl7_6),
% 1.40/0.56    inference(avatar_split_clause,[],[f229,f206,f231,f123])).
% 1.40/0.56  fof(f206,plain,(
% 1.40/0.56    spl7_6 <=> sK0 = sK3(sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.40/0.56  fof(f229,plain,(
% 1.40/0.56    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | ~spl7_6),
% 1.40/0.56    inference(superposition,[],[f54,f207])).
% 1.40/0.56  fof(f207,plain,(
% 1.40/0.56    sK0 = sK3(sK1) | ~spl7_6),
% 1.40/0.56    inference(avatar_component_clause,[],[f206])).
% 1.40/0.56  fof(f208,plain,(
% 1.40/0.56    spl7_3 | spl7_6),
% 1.40/0.56    inference(avatar_split_clause,[],[f198,f206,f123])).
% 1.40/0.56  fof(f198,plain,(
% 1.40/0.56    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 1.40/0.56    inference(resolution,[],[f187,f54])).
% 1.40/0.56  fof(f129,plain,(
% 1.40/0.56    ~spl7_1 | ~spl7_4),
% 1.40/0.56    inference(avatar_split_clause,[],[f91,f126,f116])).
% 1.40/0.56  fof(f91,plain,(
% 1.40/0.56    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.40/0.56    inference(definition_unfolding,[],[f49,f88,f88])).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  fof(f128,plain,(
% 1.40/0.56    ~spl7_3 | ~spl7_4),
% 1.40/0.56    inference(avatar_split_clause,[],[f90,f126,f123])).
% 1.40/0.56  fof(f90,plain,(
% 1.40/0.56    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.40/0.56    inference(definition_unfolding,[],[f50,f88])).
% 1.40/0.56  fof(f50,plain,(
% 1.40/0.56    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  fof(f121,plain,(
% 1.40/0.56    ~spl7_1 | ~spl7_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f89,f119,f116])).
% 1.40/0.56  fof(f89,plain,(
% 1.40/0.56    k1_xboole_0 != sK2 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.40/0.56    inference(definition_unfolding,[],[f51,f88])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (9762)------------------------------
% 1.40/0.56  % (9762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (9762)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (9762)Memory used [KB]: 11129
% 1.40/0.56  % (9762)Time elapsed: 0.144 s
% 1.40/0.56  % (9762)------------------------------
% 1.40/0.56  % (9762)------------------------------
% 1.40/0.56  % (9759)Success in time 0.199 s
%------------------------------------------------------------------------------
