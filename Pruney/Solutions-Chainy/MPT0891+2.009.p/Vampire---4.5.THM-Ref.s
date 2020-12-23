%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 452 expanded)
%              Number of leaves         :   36 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  668 (1776 expanded)
%              Number of equality atoms :  323 ( 996 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f1028,f1036,f1044,f1052,f1159,f1426,f1484,f1499,f1507,f1653,f1658,f1673,f1740])).

fof(f1740,plain,
    ( spl9_11
    | ~ spl9_12
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1739,f1655,f1504,f1156,f122,f1481,f1477])).

fof(f1477,plain,
    ( spl9_11
  <=> k1_xboole_0 = k1_enumset1(sK5,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1481,plain,
    ( spl9_12
  <=> r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f122,plain,
    ( spl9_1
  <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1156,plain,
    ( spl9_9
  <=> k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1504,plain,
    ( spl9_13
  <=> sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1655,plain,
    ( spl9_14
  <=> k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1739,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5))
    | k1_xboole_0 = k1_enumset1(sK5,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(equality_resolution,[],[f1709])).

fof(f1709,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f1708])).

fof(f1708,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0)
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(superposition,[],[f1679,f232])).

fof(f232,plain,(
    ! [X0] :
      ( sK6(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(resolution,[],[f231,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f230,f142])).

fof(f142,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f116,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f116,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f78,f97])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f230,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | X2 = X3
      | ~ r2_hidden(X3,k1_enumset1(X2,X2,X2)) ) ),
    inference(superposition,[],[f103,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f156,f60])).

fof(f156,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(resolution,[],[f155,f137])).

fof(f137,plain,(
    ! [X1] : sP0(k1_xboole_0,X1,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f115,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f115,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f75,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f155,plain,(
    ! [X6,X4,X5] :
      ( ~ sP0(k1_xboole_0,X6,X5)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f70,f142])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f97])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1679,plain,
    ( ! [X0] :
        ( sK5 != sK6(X0)
        | ~ r2_hidden(sK5,X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(superposition,[],[f100,f1677])).

fof(f1677,plain,
    ( sK5 = k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5))
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f1674,f1675])).

fof(f1675,plain,
    ( sK5 = k1_mcart_1(k1_mcart_1(sK5))
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(backward_demodulation,[],[f1158,f124])).

fof(f124,plain,
    ( sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1158,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1674,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5))
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f1506,f1657])).

fof(f1657,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f1506,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f100,plain,(
    ! [X4,X2,X0,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK6(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1673,plain,
    ( ~ spl9_3
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f1672])).

fof(f1672,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(trivial_inequality_removal,[],[f1671])).

fof(f1671,plain,
    ( sK5 != sK5
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(superposition,[],[f134,f1662])).

fof(f1662,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),sK5)
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f1512,f1657])).

fof(f1512,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5)
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(forward_demodulation,[],[f1506,f1510])).

fof(f1510,plain,
    ( sK5 = k2_mcart_1(sK5)
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f1027,f132])).

fof(f132,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_3
  <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1027,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1025,plain,
    ( spl9_7
  <=> k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f134,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f113,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f113,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f1658,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_14 ),
    inference(avatar_split_clause,[],[f1054,f1655,f1021,f1017,f1013])).

fof(f1013,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1017,plain,
    ( spl9_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1021,plain,
    ( spl9_6
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1054,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f111,f98])).

fof(f98,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f53,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
    & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f30,f29])).

fof(f29,plain,
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
          ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
            | k6_mcart_1(sK2,sK3,sK4,X3) = X3
            | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
          | k6_mcart_1(sK2,sK3,sK4,X3) = X3
          | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
   => ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
      & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f85,f68])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f1653,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f1652])).

fof(f1652,plain,
    ( $false
    | ~ spl9_11 ),
    inference(resolution,[],[f1594,f142])).

fof(f1594,plain,
    ( r2_hidden(sK5,k1_xboole_0)
    | ~ spl9_11 ),
    inference(superposition,[],[f144,f1479])).

fof(f1479,plain,
    ( k1_xboole_0 = k1_enumset1(sK5,sK5,sK5)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f144,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f120,f119])).

fof(f119,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK8(X0,X1,X2,X3) != X0
              & sK8(X0,X1,X2,X3) != X1
              & sK8(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sK8(X0,X1,X2,X3) = X0
            | sK8(X0,X1,X2,X3) = X1
            | sK8(X0,X1,X2,X3) = X2
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).

fof(f47,plain,(
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
     => ( ( ( sK8(X0,X1,X2,X3) != X0
            & sK8(X0,X1,X2,X3) != X1
            & sK8(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sK8(X0,X1,X2,X3) = X0
          | sK8(X0,X1,X2,X3) = X1
          | sK8(X0,X1,X2,X3) = X2
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f120,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f24,f27])).

fof(f24,plain,(
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

fof(f1507,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_13
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f1502,f1156,f1025,f1504,f1021,f1017,f1013])).

fof(f1502,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f1419,f1158])).

fof(f1419,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f1418,f1027])).

fof(f1418,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f109,f98])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f83,f67,f68])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f1499,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1485])).

fof(f1485,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f1483,f144])).

fof(f1483,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1484,plain,
    ( spl9_11
    | ~ spl9_12
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f1475,f1423,f1481,f1477])).

fof(f1423,plain,
    ( spl9_10
  <=> sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1475,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5))
    | k1_xboole_0 = k1_enumset1(sK5,sK5,sK5)
    | ~ spl9_10 ),
    inference(equality_resolution,[],[f1446])).

fof(f1446,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl9_10 ),
    inference(duplicate_literal_removal,[],[f1445])).

fof(f1445,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0)
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl9_10 ),
    inference(superposition,[],[f1428,f232])).

fof(f1428,plain,
    ( ! [X1] :
        ( sK5 != sK6(X1)
        | ~ r2_hidden(sK5,X1)
        | k1_xboole_0 = X1 )
    | ~ spl9_10 ),
    inference(superposition,[],[f99,f1425])).

fof(f1425,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f99,plain,(
    ! [X4,X2,X0,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f62,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK6(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1426,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_10
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f1421,f1156,f1025,f126,f1423,f1021,f1017,f1013])).

fof(f126,plain,
    ( spl9_2
  <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1421,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f1420,f1158])).

fof(f1420,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k2_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f1419,f128])).

fof(f128,plain,
    ( sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1159,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_9 ),
    inference(avatar_split_clause,[],[f1154,f1156,f1021,f1017,f1013])).

fof(f1154,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f112,f98])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f68])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1052,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f1051])).

fof(f1051,plain,
    ( $false
    | ~ spl9_6 ),
    inference(trivial_inequality_removal,[],[f1050])).

fof(f1050,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl9_6 ),
    inference(superposition,[],[f52,f1023])).

fof(f1023,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f52,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f1044,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f1043])).

fof(f1043,plain,
    ( $false
    | ~ spl9_5 ),
    inference(trivial_inequality_removal,[],[f1042])).

fof(f1042,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl9_5 ),
    inference(superposition,[],[f51,f1019])).

fof(f1019,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f1017])).

fof(f51,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f1036,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f1035])).

fof(f1035,plain,
    ( $false
    | ~ spl9_4 ),
    inference(trivial_inequality_removal,[],[f1034])).

fof(f1034,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl9_4 ),
    inference(superposition,[],[f50,f1015])).

fof(f1015,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f1028,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f1011,f1025,f1021,f1017,f1013])).

fof(f1011,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f110,f98])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f86,f68])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f133,plain,
    ( spl9_1
    | spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f54,f130,f126,f122])).

fof(f54,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26790)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26792)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (26781)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (26800)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (26798)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (26779)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (26784)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (26796)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (26780)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (26789)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (26795)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (26804)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (26802)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (26795)Refutation not found, incomplete strategy% (26795)------------------------------
% 0.22/0.53  % (26795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26795)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26795)Memory used [KB]: 10618
% 0.22/0.53  % (26795)Time elapsed: 0.129 s
% 0.22/0.53  % (26795)------------------------------
% 0.22/0.53  % (26795)------------------------------
% 0.22/0.54  % (26780)Refutation not found, incomplete strategy% (26780)------------------------------
% 0.22/0.54  % (26780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26787)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (26778)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (26783)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (26778)Refutation not found, incomplete strategy% (26778)------------------------------
% 0.22/0.54  % (26778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26778)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26778)Memory used [KB]: 1791
% 0.22/0.54  % (26778)Time elapsed: 0.127 s
% 0.22/0.54  % (26778)------------------------------
% 0.22/0.54  % (26778)------------------------------
% 0.22/0.54  % (26780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26780)Memory used [KB]: 10746
% 0.22/0.54  % (26780)Time elapsed: 0.123 s
% 0.22/0.54  % (26780)------------------------------
% 0.22/0.54  % (26780)------------------------------
% 0.22/0.54  % (26787)Refutation not found, incomplete strategy% (26787)------------------------------
% 0.22/0.54  % (26787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26787)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26787)Memory used [KB]: 10746
% 0.22/0.54  % (26787)Time elapsed: 0.145 s
% 0.22/0.54  % (26787)------------------------------
% 0.22/0.54  % (26787)------------------------------
% 0.22/0.54  % (26788)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (26798)Refutation not found, incomplete strategy% (26798)------------------------------
% 0.22/0.54  % (26798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26798)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26798)Memory used [KB]: 10746
% 0.22/0.54  % (26798)Time elapsed: 0.105 s
% 0.22/0.54  % (26798)------------------------------
% 0.22/0.54  % (26798)------------------------------
% 0.22/0.54  % (26782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (26803)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (26791)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (26794)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (26782)Refutation not found, incomplete strategy% (26782)------------------------------
% 0.22/0.54  % (26782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26782)Memory used [KB]: 6268
% 0.22/0.54  % (26782)Time elapsed: 0.137 s
% 0.22/0.54  % (26782)------------------------------
% 0.22/0.54  % (26782)------------------------------
% 0.22/0.54  % (26801)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (26786)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (26793)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (26797)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (26785)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (26786)Refutation not found, incomplete strategy% (26786)------------------------------
% 0.22/0.55  % (26786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26786)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26786)Memory used [KB]: 10746
% 0.22/0.55  % (26786)Time elapsed: 0.140 s
% 0.22/0.55  % (26786)------------------------------
% 0.22/0.55  % (26786)------------------------------
% 0.22/0.55  % (26806)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26789)Refutation not found, incomplete strategy% (26789)------------------------------
% 0.22/0.55  % (26789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26789)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26789)Memory used [KB]: 10618
% 0.22/0.55  % (26789)Time elapsed: 0.152 s
% 0.22/0.55  % (26789)------------------------------
% 0.22/0.55  % (26789)------------------------------
% 0.22/0.55  % (26799)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (26807)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (26799)Refutation not found, incomplete strategy% (26799)------------------------------
% 0.22/0.56  % (26799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26799)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26799)Memory used [KB]: 1791
% 0.22/0.56  % (26799)Time elapsed: 0.150 s
% 0.22/0.56  % (26799)------------------------------
% 0.22/0.56  % (26799)------------------------------
% 0.22/0.56  % (26805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (26801)Refutation not found, incomplete strategy% (26801)------------------------------
% 0.22/0.57  % (26801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26801)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26801)Memory used [KB]: 1791
% 0.22/0.57  % (26801)Time elapsed: 0.142 s
% 0.22/0.57  % (26801)------------------------------
% 0.22/0.57  % (26801)------------------------------
% 0.22/0.57  % (26788)Refutation not found, incomplete strategy% (26788)------------------------------
% 0.22/0.57  % (26788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26788)Memory used [KB]: 10746
% 0.22/0.57  % (26788)Time elapsed: 0.161 s
% 0.22/0.57  % (26788)------------------------------
% 0.22/0.57  % (26788)------------------------------
% 1.82/0.60  % (26790)Refutation found. Thanks to Tanya!
% 1.82/0.60  % SZS status Theorem for theBenchmark
% 1.82/0.60  % SZS output start Proof for theBenchmark
% 1.82/0.60  fof(f1741,plain,(
% 1.82/0.60    $false),
% 1.82/0.60    inference(avatar_sat_refutation,[],[f133,f1028,f1036,f1044,f1052,f1159,f1426,f1484,f1499,f1507,f1653,f1658,f1673,f1740])).
% 1.82/0.60  fof(f1740,plain,(
% 1.82/0.60    spl9_11 | ~spl9_12 | ~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14),
% 1.82/0.60    inference(avatar_split_clause,[],[f1739,f1655,f1504,f1156,f122,f1481,f1477])).
% 1.82/0.60  fof(f1477,plain,(
% 1.82/0.60    spl9_11 <=> k1_xboole_0 = k1_enumset1(sK5,sK5,sK5)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.82/0.60  fof(f1481,plain,(
% 1.82/0.60    spl9_12 <=> r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.82/0.60  fof(f122,plain,(
% 1.82/0.60    spl9_1 <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.82/0.60  fof(f1156,plain,(
% 1.82/0.60    spl9_9 <=> k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.82/0.60  fof(f1504,plain,(
% 1.82/0.60    spl9_13 <=> sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.82/0.60  fof(f1655,plain,(
% 1.82/0.60    spl9_14 <=> k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.82/0.60  fof(f1739,plain,(
% 1.82/0.60    ~r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) | k1_xboole_0 = k1_enumset1(sK5,sK5,sK5) | (~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(equality_resolution,[],[f1709])).
% 1.82/0.60  fof(f1709,plain,(
% 1.82/0.60    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | (~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f1708])).
% 1.82/0.60  fof(f1708,plain,(
% 1.82/0.60    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | (~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(superposition,[],[f1679,f232])).
% 1.82/0.60  fof(f232,plain,(
% 1.82/0.60    ( ! [X0] : (sK6(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.82/0.60    inference(resolution,[],[f231,f60])).
% 1.82/0.60  fof(f60,plain,(
% 1.82/0.60    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f33])).
% 1.82/0.60  fof(f33,plain,(
% 1.82/0.60    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f32])).
% 1.82/0.60  fof(f32,plain,(
% 1.82/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f21,plain,(
% 1.82/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.82/0.60    inference(ennf_transformation,[],[f13])).
% 1.82/0.60  fof(f13,axiom,(
% 1.82/0.60    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.82/0.60  fof(f231,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | X0 = X1) )),
% 1.82/0.60    inference(resolution,[],[f230,f142])).
% 1.82/0.60  fof(f142,plain,(
% 1.82/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.82/0.60    inference(superposition,[],[f116,f55])).
% 1.82/0.60  fof(f55,plain,(
% 1.82/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.82/0.60  fof(f116,plain,(
% 1.82/0.60    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.82/0.60    inference(equality_resolution,[],[f104])).
% 1.82/0.60  fof(f104,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f78,f97])).
% 1.82/0.60  fof(f97,plain,(
% 1.82/0.60    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f57,f63])).
% 1.82/0.60  fof(f63,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f7])).
% 1.82/0.60  fof(f7,axiom,(
% 1.82/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.60  fof(f57,plain,(
% 1.82/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f6])).
% 1.82/0.60  fof(f6,axiom,(
% 1.82/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.82/0.60  fof(f78,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f41])).
% 1.82/0.60  fof(f41,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.82/0.60    inference(flattening,[],[f40])).
% 1.82/0.60  fof(f40,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.82/0.60    inference(nnf_transformation,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.82/0.60  fof(f230,plain,(
% 1.82/0.60    ( ! [X2,X3] : (r2_hidden(X3,k1_xboole_0) | X2 = X3 | ~r2_hidden(X3,k1_enumset1(X2,X2,X2))) )),
% 1.82/0.60    inference(superposition,[],[f103,f160])).
% 1.82/0.60  fof(f160,plain,(
% 1.82/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.82/0.60    inference(resolution,[],[f156,f60])).
% 1.82/0.60  fof(f156,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.82/0.60    inference(resolution,[],[f155,f137])).
% 1.82/0.60  fof(f137,plain,(
% 1.82/0.60    ( ! [X1] : (sP0(k1_xboole_0,X1,k4_xboole_0(X1,X1))) )),
% 1.82/0.60    inference(superposition,[],[f115,f56])).
% 1.82/0.60  fof(f56,plain,(
% 1.82/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f2])).
% 1.82/0.60  fof(f2,axiom,(
% 1.82/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.82/0.60  fof(f115,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.82/0.60    inference(equality_resolution,[],[f102])).
% 1.82/0.60  fof(f102,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.82/0.60    inference(definition_unfolding,[],[f75,f64])).
% 1.82/0.60  fof(f64,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f3])).
% 1.82/0.60  fof(f3,axiom,(
% 1.82/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.82/0.60    inference(cnf_transformation,[],[f39])).
% 1.82/0.60  fof(f39,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.82/0.60    inference(nnf_transformation,[],[f26])).
% 1.82/0.60  fof(f26,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.82/0.60    inference(definition_folding,[],[f1,f25])).
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.82/0.60  fof(f1,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.82/0.60  fof(f155,plain,(
% 1.82/0.60    ( ! [X6,X4,X5] : (~sP0(k1_xboole_0,X6,X5) | ~r2_hidden(X4,X5)) )),
% 1.82/0.60    inference(resolution,[],[f70,f142])).
% 1.82/0.60  fof(f70,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f38])).
% 1.82/0.60  fof(f38,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 1.82/0.60  fof(f37,plain,(
% 1.82/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f36,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.82/0.60    inference(rectify,[],[f35])).
% 1.82/0.60  fof(f35,plain,(
% 1.82/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.82/0.60    inference(flattening,[],[f34])).
% 1.82/0.60  fof(f34,plain,(
% 1.82/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.82/0.60    inference(nnf_transformation,[],[f25])).
% 1.82/0.60  fof(f103,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f79,f97])).
% 1.82/0.60  fof(f79,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f41])).
% 1.82/0.60  fof(f1679,plain,(
% 1.82/0.60    ( ! [X0] : (sK5 != sK6(X0) | ~r2_hidden(sK5,X0) | k1_xboole_0 = X0) ) | (~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(superposition,[],[f100,f1677])).
% 1.82/0.60  fof(f1677,plain,(
% 1.82/0.60    sK5 = k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) | (~spl9_1 | ~spl9_9 | ~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(backward_demodulation,[],[f1674,f1675])).
% 1.82/0.60  fof(f1675,plain,(
% 1.82/0.60    sK5 = k1_mcart_1(k1_mcart_1(sK5)) | (~spl9_1 | ~spl9_9)),
% 1.82/0.60    inference(backward_demodulation,[],[f1158,f124])).
% 1.82/0.60  fof(f124,plain,(
% 1.82/0.60    sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_1),
% 1.82/0.60    inference(avatar_component_clause,[],[f122])).
% 1.82/0.60  fof(f1158,plain,(
% 1.82/0.60    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) | ~spl9_9),
% 1.82/0.60    inference(avatar_component_clause,[],[f1156])).
% 1.82/0.60  fof(f1674,plain,(
% 1.82/0.60    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) | (~spl9_13 | ~spl9_14)),
% 1.82/0.60    inference(forward_demodulation,[],[f1506,f1657])).
% 1.82/0.60  fof(f1657,plain,(
% 1.82/0.60    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | ~spl9_14),
% 1.82/0.60    inference(avatar_component_clause,[],[f1655])).
% 1.82/0.60  fof(f1506,plain,(
% 1.82/0.60    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) | ~spl9_13),
% 1.82/0.60    inference(avatar_component_clause,[],[f1504])).
% 1.82/0.61  fof(f100,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3] : (sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f61,f67])).
% 1.82/0.61  fof(f67,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f10])).
% 1.82/0.61  fof(f10,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.82/0.61  fof(f61,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f33])).
% 1.82/0.61  fof(f1673,plain,(
% 1.82/0.61    ~spl9_3 | ~spl9_7 | ~spl9_13 | ~spl9_14),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1672])).
% 1.82/0.61  fof(f1672,plain,(
% 1.82/0.61    $false | (~spl9_3 | ~spl9_7 | ~spl9_13 | ~spl9_14)),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1671])).
% 1.82/0.61  fof(f1671,plain,(
% 1.82/0.61    sK5 != sK5 | (~spl9_3 | ~spl9_7 | ~spl9_13 | ~spl9_14)),
% 1.82/0.61    inference(superposition,[],[f134,f1662])).
% 1.82/0.61  fof(f1662,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),sK5) | (~spl9_3 | ~spl9_7 | ~spl9_13 | ~spl9_14)),
% 1.82/0.61    inference(backward_demodulation,[],[f1512,f1657])).
% 1.82/0.61  fof(f1512,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5) | (~spl9_3 | ~spl9_7 | ~spl9_13)),
% 1.82/0.61    inference(forward_demodulation,[],[f1506,f1510])).
% 1.82/0.61  fof(f1510,plain,(
% 1.82/0.61    sK5 = k2_mcart_1(sK5) | (~spl9_3 | ~spl9_7)),
% 1.82/0.61    inference(backward_demodulation,[],[f1027,f132])).
% 1.82/0.61  fof(f132,plain,(
% 1.82/0.61    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_3),
% 1.82/0.61    inference(avatar_component_clause,[],[f130])).
% 1.82/0.61  fof(f130,plain,(
% 1.82/0.61    spl9_3 <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.82/0.61  fof(f1027,plain,(
% 1.82/0.61    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) | ~spl9_7),
% 1.82/0.61    inference(avatar_component_clause,[],[f1025])).
% 1.82/0.61  fof(f1025,plain,(
% 1.82/0.61    spl9_7 <=> k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.82/0.61  fof(f134,plain,(
% 1.82/0.61    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.82/0.61    inference(backward_demodulation,[],[f113,f66])).
% 1.82/0.61  fof(f66,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.82/0.61    inference(cnf_transformation,[],[f16])).
% 1.82/0.61  fof(f16,axiom,(
% 1.82/0.61    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.82/0.61  fof(f113,plain,(
% 1.82/0.61    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.82/0.61    inference(equality_resolution,[],[f59])).
% 1.82/0.61  fof(f59,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f20])).
% 1.82/0.61  fof(f20,plain,(
% 1.82/0.61    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.82/0.61  fof(f1658,plain,(
% 1.82/0.61    spl9_4 | spl9_5 | spl9_6 | spl9_14),
% 1.82/0.61    inference(avatar_split_clause,[],[f1054,f1655,f1021,f1017,f1013])).
% 1.82/0.61  fof(f1013,plain,(
% 1.82/0.61    spl9_4 <=> k1_xboole_0 = sK2),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.82/0.61  fof(f1017,plain,(
% 1.82/0.61    spl9_5 <=> k1_xboole_0 = sK3),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.82/0.61  fof(f1021,plain,(
% 1.82/0.61    spl9_6 <=> k1_xboole_0 = sK4),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.82/0.61  fof(f1054,plain,(
% 1.82/0.61    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.82/0.61    inference(resolution,[],[f111,f98])).
% 1.82/0.61  fof(f98,plain,(
% 1.82/0.61    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.82/0.61    inference(definition_unfolding,[],[f53,f68])).
% 1.82/0.61  fof(f68,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f11])).
% 1.82/0.61  fof(f11,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.82/0.61  fof(f53,plain,(
% 1.82/0.61    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f30,f29])).
% 1.82/0.61  fof(f29,plain,(
% 1.82/0.61    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f30,plain,(
% 1.82/0.61    ? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) => ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)))),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f19,plain,(
% 1.82/0.61    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f18])).
% 1.82/0.61  fof(f18,negated_conjecture,(
% 1.82/0.61    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    inference(negated_conjecture,[],[f17])).
% 1.82/0.61  fof(f17,conjecture,(
% 1.82/0.61    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.82/0.61  fof(f111,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f85,f68])).
% 1.82/0.61  fof(f85,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f23])).
% 1.82/0.61  fof(f23,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f15])).
% 1.82/0.61  fof(f15,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.82/0.61  fof(f1653,plain,(
% 1.82/0.61    ~spl9_11),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1652])).
% 1.82/0.61  fof(f1652,plain,(
% 1.82/0.61    $false | ~spl9_11),
% 1.82/0.61    inference(resolution,[],[f1594,f142])).
% 1.82/0.61  fof(f1594,plain,(
% 1.82/0.61    r2_hidden(sK5,k1_xboole_0) | ~spl9_11),
% 1.82/0.61    inference(superposition,[],[f144,f1479])).
% 1.82/0.61  fof(f1479,plain,(
% 1.82/0.61    k1_xboole_0 = k1_enumset1(sK5,sK5,sK5) | ~spl9_11),
% 1.82/0.61    inference(avatar_component_clause,[],[f1477])).
% 1.82/0.61  fof(f144,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.82/0.61    inference(resolution,[],[f120,f119])).
% 1.82/0.61  fof(f119,plain,(
% 1.82/0.61    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.82/0.61    inference(equality_resolution,[],[f88])).
% 1.82/0.61  fof(f88,plain,(
% 1.82/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f48])).
% 1.82/0.61  fof(f48,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).
% 1.82/0.61  fof(f47,plain,(
% 1.82/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f46,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.82/0.61    inference(rectify,[],[f45])).
% 1.82/0.61  fof(f45,plain,(
% 1.82/0.61    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.82/0.61    inference(flattening,[],[f44])).
% 1.82/0.61  fof(f44,plain,(
% 1.82/0.61    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.82/0.61    inference(nnf_transformation,[],[f27])).
% 1.82/0.61  fof(f27,plain,(
% 1.82/0.61    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.82/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.82/0.61  fof(f120,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.82/0.61    inference(equality_resolution,[],[f95])).
% 1.82/0.61  fof(f95,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.82/0.61    inference(cnf_transformation,[],[f49])).
% 1.82/0.61  fof(f49,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.82/0.61    inference(nnf_transformation,[],[f28])).
% 1.82/0.61  fof(f28,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 1.82/0.61    inference(definition_folding,[],[f24,f27])).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.82/0.61    inference(ennf_transformation,[],[f5])).
% 1.82/0.61  fof(f5,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.82/0.61  fof(f1507,plain,(
% 1.82/0.61    spl9_4 | spl9_5 | spl9_6 | spl9_13 | ~spl9_7 | ~spl9_9),
% 1.82/0.61    inference(avatar_split_clause,[],[f1502,f1156,f1025,f1504,f1021,f1017,f1013])).
% 1.82/0.61  fof(f1502,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | (~spl9_7 | ~spl9_9)),
% 1.82/0.61    inference(forward_demodulation,[],[f1419,f1158])).
% 1.82/0.61  fof(f1419,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | ~spl9_7),
% 1.82/0.61    inference(forward_demodulation,[],[f1418,f1027])).
% 1.82/0.61  fof(f1418,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.82/0.61    inference(resolution,[],[f109,f98])).
% 1.82/0.61  fof(f109,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f83,f67,f68])).
% 1.82/0.61  fof(f83,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f22])).
% 1.82/0.61  fof(f22,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.82/0.61  fof(f1499,plain,(
% 1.82/0.61    spl9_12),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1485])).
% 1.82/0.61  fof(f1485,plain,(
% 1.82/0.61    $false | spl9_12),
% 1.82/0.61    inference(resolution,[],[f1483,f144])).
% 1.82/0.61  fof(f1483,plain,(
% 1.82/0.61    ~r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) | spl9_12),
% 1.82/0.61    inference(avatar_component_clause,[],[f1481])).
% 1.82/0.61  fof(f1484,plain,(
% 1.82/0.61    spl9_11 | ~spl9_12 | ~spl9_10),
% 1.82/0.61    inference(avatar_split_clause,[],[f1475,f1423,f1481,f1477])).
% 1.82/0.61  fof(f1423,plain,(
% 1.82/0.61    spl9_10 <=> sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.82/0.61  fof(f1475,plain,(
% 1.82/0.61    ~r2_hidden(sK5,k1_enumset1(sK5,sK5,sK5)) | k1_xboole_0 = k1_enumset1(sK5,sK5,sK5) | ~spl9_10),
% 1.82/0.61    inference(equality_resolution,[],[f1446])).
% 1.82/0.61  fof(f1446,plain,(
% 1.82/0.61    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl9_10),
% 1.82/0.61    inference(duplicate_literal_removal,[],[f1445])).
% 1.82/0.61  fof(f1445,plain,(
% 1.82/0.61    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl9_10),
% 1.82/0.61    inference(superposition,[],[f1428,f232])).
% 1.82/0.61  fof(f1428,plain,(
% 1.82/0.61    ( ! [X1] : (sK5 != sK6(X1) | ~r2_hidden(sK5,X1) | k1_xboole_0 = X1) ) | ~spl9_10),
% 1.82/0.61    inference(superposition,[],[f99,f1425])).
% 1.82/0.61  fof(f1425,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5)) | ~spl9_10),
% 1.82/0.61    inference(avatar_component_clause,[],[f1423])).
% 1.82/0.61  fof(f99,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3] : (sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f62,f67])).
% 1.82/0.61  fof(f62,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f33])).
% 1.82/0.61  fof(f1426,plain,(
% 1.82/0.61    spl9_4 | spl9_5 | spl9_6 | spl9_10 | ~spl9_2 | ~spl9_7 | ~spl9_9),
% 1.82/0.61    inference(avatar_split_clause,[],[f1421,f1156,f1025,f126,f1423,f1021,f1017,f1013])).
% 1.82/0.61  fof(f126,plain,(
% 1.82/0.61    spl9_2 <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.82/0.61  fof(f1421,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | (~spl9_2 | ~spl9_7 | ~spl9_9)),
% 1.82/0.61    inference(forward_demodulation,[],[f1420,f1158])).
% 1.82/0.61  fof(f1420,plain,(
% 1.82/0.61    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k2_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | (~spl9_2 | ~spl9_7)),
% 1.82/0.61    inference(forward_demodulation,[],[f1419,f128])).
% 1.82/0.61  fof(f128,plain,(
% 1.82/0.61    sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f126])).
% 1.82/0.61  fof(f1159,plain,(
% 1.82/0.61    spl9_4 | spl9_5 | spl9_6 | spl9_9),
% 1.82/0.61    inference(avatar_split_clause,[],[f1154,f1156,f1021,f1017,f1013])).
% 1.82/0.61  fof(f1154,plain,(
% 1.82/0.61    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.82/0.61    inference(resolution,[],[f112,f98])).
% 1.82/0.61  fof(f112,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f84,f68])).
% 1.82/0.61  fof(f84,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f23])).
% 1.82/0.61  fof(f1052,plain,(
% 1.82/0.61    ~spl9_6),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1051])).
% 1.82/0.61  fof(f1051,plain,(
% 1.82/0.61    $false | ~spl9_6),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1050])).
% 1.82/0.61  fof(f1050,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl9_6),
% 1.82/0.61    inference(superposition,[],[f52,f1023])).
% 1.82/0.61  fof(f1023,plain,(
% 1.82/0.61    k1_xboole_0 = sK4 | ~spl9_6),
% 1.82/0.61    inference(avatar_component_clause,[],[f1021])).
% 1.82/0.61  fof(f52,plain,(
% 1.82/0.61    k1_xboole_0 != sK4),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f1044,plain,(
% 1.82/0.61    ~spl9_5),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1043])).
% 1.82/0.61  fof(f1043,plain,(
% 1.82/0.61    $false | ~spl9_5),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1042])).
% 1.82/0.61  fof(f1042,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl9_5),
% 1.82/0.61    inference(superposition,[],[f51,f1019])).
% 1.82/0.61  fof(f1019,plain,(
% 1.82/0.61    k1_xboole_0 = sK3 | ~spl9_5),
% 1.82/0.61    inference(avatar_component_clause,[],[f1017])).
% 1.82/0.61  fof(f51,plain,(
% 1.82/0.61    k1_xboole_0 != sK3),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f1036,plain,(
% 1.82/0.61    ~spl9_4),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1035])).
% 1.82/0.61  fof(f1035,plain,(
% 1.82/0.61    $false | ~spl9_4),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1034])).
% 1.82/0.61  fof(f1034,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl9_4),
% 1.82/0.61    inference(superposition,[],[f50,f1015])).
% 1.82/0.61  fof(f1015,plain,(
% 1.82/0.61    k1_xboole_0 = sK2 | ~spl9_4),
% 1.82/0.61    inference(avatar_component_clause,[],[f1013])).
% 1.82/0.61  fof(f50,plain,(
% 1.82/0.61    k1_xboole_0 != sK2),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f1028,plain,(
% 1.82/0.61    spl9_4 | spl9_5 | spl9_6 | spl9_7),
% 1.82/0.61    inference(avatar_split_clause,[],[f1011,f1025,f1021,f1017,f1013])).
% 1.82/0.61  fof(f1011,plain,(
% 1.82/0.61    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.82/0.61    inference(resolution,[],[f110,f98])).
% 1.82/0.61  fof(f110,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f86,f68])).
% 1.82/0.61  fof(f86,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f23])).
% 1.82/0.61  fof(f133,plain,(
% 1.82/0.61    spl9_1 | spl9_2 | spl9_3),
% 1.82/0.61    inference(avatar_split_clause,[],[f54,f130,f126,f122])).
% 1.82/0.61  fof(f54,plain,(
% 1.82/0.61    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (26790)------------------------------
% 1.82/0.61  % (26790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (26790)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (26790)Memory used [KB]: 7291
% 1.82/0.61  % (26790)Time elapsed: 0.175 s
% 1.82/0.61  % (26790)------------------------------
% 1.82/0.61  % (26790)------------------------------
% 1.82/0.61  % (26776)Success in time 0.242 s
%------------------------------------------------------------------------------
