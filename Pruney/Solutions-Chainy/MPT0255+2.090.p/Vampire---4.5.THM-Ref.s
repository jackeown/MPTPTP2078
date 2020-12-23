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
% DateTime   : Thu Dec  3 12:39:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 534 expanded)
%              Number of leaves         :   29 ( 176 expanded)
%              Depth                    :   20
%              Number of atoms          :  275 ( 807 expanded)
%              Number of equality atoms :  102 ( 534 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f755,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f542,f650,f715,f754])).

fof(f754,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f734,f85])).

fof(f85,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f734,plain,
    ( ! [X0] : ~ sP0(X0,sK3,sK2,sK2)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f732,f482])).

fof(f482,plain,(
    ! [X15] : ~ r2_hidden(X15,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f477,f142])).

fof(f142,plain,(
    ! [X19] : r1_xboole_0(k1_xboole_0,X19) ),
    inference(subsumption_resolution,[],[f140,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f140,plain,(
    ! [X19] :
      ( r1_xboole_0(k1_xboole_0,X19)
      | ~ r1_tarski(k1_xboole_0,X19) ) ),
    inference(superposition,[],[f101,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f50,f89])).

fof(f89,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f49,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f477,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(k1_xboole_0,X14)
      | ~ r2_hidden(X15,k1_xboole_0) ) ),
    inference(resolution,[],[f132,f44])).

fof(f132,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_xboole_0(X6,X7)
      | ~ r2_hidden(X8,X6) ) ),
    inference(superposition,[],[f56,f57])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f732,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK3,sK2,sK2)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f561,f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sP0(sK6(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sP0(sK6(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f561,plain,
    ( sP1(sK2,sK2,sK3,k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl7_5
  <=> sP1(sK2,sK2,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f715,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl7_1 ),
    inference(resolution,[],[f710,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f27,f29,f28])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f710,plain,
    ( ! [X20] : ~ sP1(sK2,sK2,sK3,X20)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f709,f537])).

fof(f537,plain,
    ( ! [X1] :
        ( ~ sP1(sK2,sK2,sK3,X1)
        | ~ r1_tarski(X1,sK4) )
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl7_1
  <=> ! [X1] :
        ( ~ sP1(sK2,sK2,sK3,X1)
        | ~ r1_tarski(X1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f709,plain,(
    ! [X20] :
      ( r1_tarski(X20,sK4)
      | ~ sP1(sK2,sK2,sK3,X20) ) ),
    inference(subsumption_resolution,[],[f698,f432])).

fof(f432,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f343,f106])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f343,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k5_xboole_0(X5,X6),X5)
      | r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f135,f183])).

fof(f183,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f165,f89])).

fof(f165,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f59,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f135,plain,(
    ! [X14,X13] :
      ( r1_tarski(k5_xboole_0(X14,X13),X14)
      | ~ r1_tarski(X13,X14) ) ),
    inference(superposition,[],[f106,f57])).

fof(f698,plain,(
    ! [X20] :
      ( ~ r1_tarski(k3_xboole_0(X20,sK4),sK4)
      | r1_tarski(X20,sK4)
      | ~ sP1(sK2,sK2,sK3,X20) ) ),
    inference(superposition,[],[f344,f570])).

fof(f570,plain,(
    ! [X10] :
      ( k3_xboole_0(X10,sK4) = k5_xboole_0(X10,sK4)
      | ~ sP1(sK2,sK2,sK3,X10) ) ),
    inference(forward_demodulation,[],[f522,f46])).

fof(f522,plain,(
    ! [X10] :
      ( k5_xboole_0(X10,sK4) = k5_xboole_0(k3_xboole_0(X10,sK4),k1_xboole_0)
      | ~ sP1(sK2,sK2,sK3,X10) ) ),
    inference(superposition,[],[f183,f495])).

fof(f495,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,sK4),k5_xboole_0(X0,sK4))
      | ~ sP1(sK2,sK2,sK3,X0) ) ),
    inference(forward_demodulation,[],[f494,f49])).

fof(f494,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,sK4),k3_xboole_0(X0,sK4))
      | ~ sP1(sK2,sK2,sK3,X0) ) ),
    inference(forward_demodulation,[],[f490,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f490,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4))
      | ~ sP1(sK2,sK2,sK3,X0) ) ),
    inference(superposition,[],[f80,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f43,f79,f78])).

fof(f43,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f344,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k5_xboole_0(X8,X7),X7)
      | r1_tarski(X8,X7) ) ),
    inference(superposition,[],[f135,f187])).

fof(f187,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f183,f49])).

fof(f650,plain,
    ( ~ spl7_2
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | ~ spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f647,f562])).

fof(f562,plain,
    ( ~ sP1(sK2,sK2,sK3,k1_xboole_0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f560])).

fof(f647,plain,
    ( sP1(sK2,sK2,sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f88,f598])).

fof(f598,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f597,f88])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ sP1(sK2,sK2,sK3,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f596,f44])).

fof(f596,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | ~ sP1(sK2,sK2,sK3,X0) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f533,f541])).

fof(f541,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f533,plain,(
    ! [X0] :
      ( ~ sP1(sK2,sK2,sK3,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK4,X0) ) ),
    inference(forward_demodulation,[],[f505,f187])).

fof(f505,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(sK4,k5_xboole_0(X0,sK4))
      | ~ sP1(sK2,sK2,sK3,X0)
      | ~ r1_tarski(sK4,X0) ) ),
    inference(superposition,[],[f495,f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f57,f48])).

fof(f542,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f534,f539,f536])).

fof(f534,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK4
      | ~ sP1(sK2,sK2,sK3,X1)
      | ~ r1_tarski(X1,sK4) ) ),
    inference(forward_demodulation,[],[f506,f183])).

fof(f506,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X1,sK4))
      | ~ sP1(sK2,sK2,sK3,X1)
      | ~ r1_tarski(X1,sK4) ) ),
    inference(superposition,[],[f495,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (18196)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.48  % (18217)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.48  % (18193)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (18209)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (18204)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (18190)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (18192)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (18199)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (18217)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f755,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f542,f650,f715,f754])).
% 0.20/0.51  fof(f754,plain,(
% 0.20/0.51    ~spl7_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f748])).
% 0.20/0.51  fof(f748,plain,(
% 0.20/0.51    $false | ~spl7_5),
% 0.20/0.51    inference(resolution,[],[f734,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.51    inference(rectify,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 0.20/0.51    inference(flattening,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f734,plain,(
% 0.20/0.51    ( ! [X0] : (~sP0(X0,sK3,sK2,sK2)) ) | ~spl7_5),
% 0.20/0.51    inference(subsumption_resolution,[],[f732,f482])).
% 0.20/0.51  fof(f482,plain,(
% 0.20/0.51    ( ! [X15] : (~r2_hidden(X15,k1_xboole_0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f477,f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X19] : (r1_xboole_0(k1_xboole_0,X19)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f140,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ( ! [X19] : (r1_xboole_0(k1_xboole_0,X19) | ~r1_tarski(k1_xboole_0,X19)) )),
% 0.20/0.51    inference(superposition,[],[f101,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) )),
% 0.20/0.51    inference(superposition,[],[f50,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.51    inference(superposition,[],[f49,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.20/0.51  fof(f477,plain,(
% 0.20/0.51    ( ! [X14,X15] : (~r1_xboole_0(k1_xboole_0,X14) | ~r2_hidden(X15,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f132,f44])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | ~r1_xboole_0(X6,X7) | ~r2_hidden(X8,X6)) )),
% 0.20/0.51    inference(superposition,[],[f56,f57])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.51  fof(f732,plain,(
% 0.20/0.51    ( ! [X0] : (~sP0(X0,sK3,sK2,sK2) | r2_hidden(X0,k1_xboole_0)) ) | ~spl7_5),
% 0.20/0.51    inference(resolution,[],[f561,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK6(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sP0(sK6(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK6(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sP0(sK6(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(rectify,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.51    inference(nnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f561,plain,(
% 0.20/0.51    sP1(sK2,sK2,sK3,k1_xboole_0) | ~spl7_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f560])).
% 0.20/0.51  fof(f560,plain,(
% 0.20/0.51    spl7_5 <=> sP1(sK2,sK2,sK3,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.51  fof(f715,plain,(
% 0.20/0.51    ~spl7_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f714])).
% 0.20/0.51  fof(f714,plain,(
% 0.20/0.51    $false | ~spl7_1),
% 0.20/0.51    inference(resolution,[],[f710,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.51    inference(definition_unfolding,[],[f69,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f58,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f60,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f71,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f72,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(nnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 0.20/0.51    inference(definition_folding,[],[f27,f29,f28])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.51  fof(f710,plain,(
% 0.20/0.51    ( ! [X20] : (~sP1(sK2,sK2,sK3,X20)) ) | ~spl7_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f709,f537])).
% 0.20/0.51  fof(f537,plain,(
% 0.20/0.51    ( ! [X1] : (~sP1(sK2,sK2,sK3,X1) | ~r1_tarski(X1,sK4)) ) | ~spl7_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f536])).
% 0.20/0.51  fof(f536,plain,(
% 0.20/0.51    spl7_1 <=> ! [X1] : (~sP1(sK2,sK2,sK3,X1) | ~r1_tarski(X1,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.51  fof(f709,plain,(
% 0.20/0.51    ( ! [X20] : (r1_tarski(X20,sK4) | ~sP1(sK2,sK2,sK3,X20)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f698,f432])).
% 0.20/0.51  fof(f432,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X3)) )),
% 0.20/0.51    inference(resolution,[],[f343,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.20/0.51    inference(superposition,[],[f81,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f47,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f343,plain,(
% 0.20/0.51    ( ! [X6,X5] : (~r1_tarski(k5_xboole_0(X5,X6),X5) | r1_tarski(X6,X5)) )),
% 0.20/0.51    inference(superposition,[],[f135,f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.51    inference(forward_demodulation,[],[f165,f89])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f59,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X14,X13] : (r1_tarski(k5_xboole_0(X14,X13),X14) | ~r1_tarski(X13,X14)) )),
% 0.20/0.51    inference(superposition,[],[f106,f57])).
% 0.20/0.51  fof(f698,plain,(
% 0.20/0.51    ( ! [X20] : (~r1_tarski(k3_xboole_0(X20,sK4),sK4) | r1_tarski(X20,sK4) | ~sP1(sK2,sK2,sK3,X20)) )),
% 0.20/0.51    inference(superposition,[],[f344,f570])).
% 0.20/0.51  fof(f570,plain,(
% 0.20/0.51    ( ! [X10] : (k3_xboole_0(X10,sK4) = k5_xboole_0(X10,sK4) | ~sP1(sK2,sK2,sK3,X10)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f522,f46])).
% 0.20/0.51  fof(f522,plain,(
% 0.20/0.51    ( ! [X10] : (k5_xboole_0(X10,sK4) = k5_xboole_0(k3_xboole_0(X10,sK4),k1_xboole_0) | ~sP1(sK2,sK2,sK3,X10)) )),
% 0.20/0.51    inference(superposition,[],[f183,f495])).
% 0.20/0.51  fof(f495,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,sK4),k5_xboole_0(X0,sK4)) | ~sP1(sK2,sK2,sK3,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f494,f49])).
% 0.20/0.51  fof(f494,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,sK4),k3_xboole_0(X0,sK4)) | ~sP1(sK2,sK2,sK3,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f490,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f54,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f51,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f52,f77])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.51  fof(f490,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) | ~sP1(sK2,sK2,sK3,X0)) )),
% 0.20/0.51    inference(superposition,[],[f80,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f70,f77])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),
% 0.20/0.51    inference(definition_unfolding,[],[f43,f79,f78])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.51    inference(ennf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.51    inference(negated_conjecture,[],[f21])).
% 0.20/0.51  fof(f21,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.20/0.51  fof(f344,plain,(
% 0.20/0.51    ( ! [X8,X7] : (~r1_tarski(k5_xboole_0(X8,X7),X7) | r1_tarski(X8,X7)) )),
% 0.20/0.51    inference(superposition,[],[f135,f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.20/0.51    inference(superposition,[],[f183,f49])).
% 0.20/0.51  fof(f650,plain,(
% 0.20/0.51    ~spl7_2 | spl7_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f649])).
% 0.20/0.51  fof(f649,plain,(
% 0.20/0.51    $false | (~spl7_2 | spl7_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f647,f562])).
% 0.20/0.51  fof(f562,plain,(
% 0.20/0.51    ~sP1(sK2,sK2,sK3,k1_xboole_0) | spl7_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f560])).
% 0.20/0.51  fof(f647,plain,(
% 0.20/0.51    sP1(sK2,sK2,sK3,k1_xboole_0) | ~spl7_2),
% 0.20/0.51    inference(superposition,[],[f88,f598])).
% 0.20/0.51  fof(f598,plain,(
% 0.20/0.51    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl7_2),
% 0.20/0.51    inference(resolution,[],[f597,f88])).
% 0.20/0.51  fof(f597,plain,(
% 0.20/0.51    ( ! [X0] : (~sP1(sK2,sK2,sK3,X0) | k1_xboole_0 = X0) ) | ~spl7_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f596,f44])).
% 0.20/0.51  fof(f596,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = X0 | ~sP1(sK2,sK2,sK3,X0)) ) | ~spl7_2),
% 0.20/0.51    inference(forward_demodulation,[],[f533,f541])).
% 0.20/0.51  fof(f541,plain,(
% 0.20/0.51    k1_xboole_0 = sK4 | ~spl7_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f539])).
% 0.20/0.51  fof(f539,plain,(
% 0.20/0.51    spl7_2 <=> k1_xboole_0 = sK4),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.51  fof(f533,plain,(
% 0.20/0.51    ( ! [X0] : (~sP1(sK2,sK2,sK3,X0) | k1_xboole_0 = X0 | ~r1_tarski(sK4,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f505,f187])).
% 0.20/0.51  fof(f505,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(sK4,k5_xboole_0(X0,sK4)) | ~sP1(sK2,sK2,sK3,X0) | ~r1_tarski(sK4,X0)) )),
% 0.20/0.51    inference(superposition,[],[f495,f127])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.20/0.51    inference(superposition,[],[f57,f48])).
% 0.20/0.51  fof(f542,plain,(
% 0.20/0.51    spl7_1 | spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f534,f539,f536])).
% 0.20/0.51  fof(f534,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = sK4 | ~sP1(sK2,sK2,sK3,X1) | ~r1_tarski(X1,sK4)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f506,f183])).
% 0.20/0.51  fof(f506,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X1,sK4)) | ~sP1(sK2,sK2,sK3,X1) | ~r1_tarski(X1,sK4)) )),
% 0.20/0.51    inference(superposition,[],[f495,f57])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (18217)------------------------------
% 0.20/0.51  % (18217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18217)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (18217)Memory used [KB]: 6524
% 0.20/0.51  % (18217)Time elapsed: 0.106 s
% 0.20/0.51  % (18217)------------------------------
% 0.20/0.51  % (18217)------------------------------
% 0.20/0.51  % (18200)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (18189)Success in time 0.152 s
%------------------------------------------------------------------------------
