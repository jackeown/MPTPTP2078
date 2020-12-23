%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:21 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 270 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  451 (1113 expanded)
%              Number of equality atoms :  183 ( 389 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f127,f134,f143,f398,f407,f426,f459,f491,f501,f508])).

fof(f508,plain,
    ( ~ spl7_4
    | spl7_17
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl7_4
    | spl7_17
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f490,f396,f500,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK3 = X0
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f228,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
        | sK3 = X0 )
    | ~ spl7_4 ),
    inference(superposition,[],[f101,f120])).

fof(f120,plain,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_4
  <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f101,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f500,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl7_21
  <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f396,plain,
    ( sK3 != sK6(sK3,k3_xboole_0(sK0,sK2))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl7_17
  <=> sK3 = sK6(sK3,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f490,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl7_20
  <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f501,plain,
    ( spl7_21
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f495,f391,f498])).

fof(f391,plain,
    ( spl7_16
  <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f495,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2)
    | ~ spl7_16 ),
    inference(resolution,[],[f393,f97])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f393,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f391])).

fof(f491,plain,
    ( spl7_20
    | ~ spl7_1
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f461,f404,f103,f488])).

fof(f103,plain,
    ( spl7_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f404,plain,
    ( spl7_18
  <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f461,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl7_1
    | ~ spl7_18 ),
    inference(resolution,[],[f406,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f154,f105])).

fof(f105,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f154,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,X6)
      | r2_hidden(X7,X6)
      | ~ r2_hidden(X7,X5) ) ),
    inference(superposition,[],[f97,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f65,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f406,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f404])).

fof(f459,plain,
    ( ~ spl7_19
    | spl7_5
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f412,f395,f118,f124,f415])).

fof(f415,plain,
    ( spl7_19
  <=> r2_hidden(sK3,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f124,plain,
    ( spl7_5
  <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f412,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2))
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f411,f120])).

fof(f411,plain,
    ( k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2))
    | ~ spl7_17 ),
    inference(trivial_inequality_removal,[],[f410])).

fof(f410,plain,
    ( sK3 != sK3
    | k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2))
    | ~ spl7_17 ),
    inference(superposition,[],[f85,f397])).

fof(f397,plain,
    ( sK3 = sK6(sK3,k3_xboole_0(sK0,sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f395])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | k3_enumset1(X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f426,plain,
    ( ~ spl7_2
    | ~ spl7_7
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7
    | spl7_19 ),
    inference(unit_resulting_resolution,[],[f110,f142,f417,f96])).

fof(f417,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK0,sK2))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f415])).

fof(f142,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_7
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f110,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f407,plain,
    ( spl7_18
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f400,f391,f404])).

fof(f400,plain,
    ( r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f393,f98])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f398,plain,
    ( spl7_16
    | spl7_17
    | spl7_3 ),
    inference(avatar_split_clause,[],[f368,f113,f395,f391])).

fof(f113,plain,
    ( spl7_3
  <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f368,plain,
    ( sK3 = sK6(sK3,k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2))
    | spl7_3 ),
    inference(equality_resolution,[],[f342])).

fof(f342,plain,
    ( ! [X1] :
        ( k3_xboole_0(sK0,sK2) != X1
        | sK3 = sK6(sK3,X1)
        | r2_hidden(sK6(sK3,X1),X1) )
    | spl7_3 ),
    inference(superposition,[],[f115,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f143,plain,
    ( spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f137,f131,f140])).

fof(f131,plain,
    ( spl7_6
  <=> r2_hidden(sK3,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f137,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f133])).

fof(f133,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f129,f118,f131])).

fof(f129,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | ~ spl7_4 ),
    inference(superposition,[],[f90,f120])).

fof(f90,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f127,plain,
    ( ~ spl7_5
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f122,f118,f113,f124])).

fof(f122,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f115,f120])).

fof(f121,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f74,f118])).

fof(f74,plain,(
    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f40,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f116,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f73,f113])).

fof(f73,plain,(
    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f42,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f41,f108])).

fof(f41,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f39,f103])).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (7789)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (7803)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (7798)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (7790)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (7799)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (7796)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (7791)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (7785)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (7788)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (7804)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (7792)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (7786)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (7805)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (7813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (7810)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (7812)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (7807)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (7797)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.55  % (7809)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (7801)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (7787)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.55  % (7801)Refutation not found, incomplete strategy% (7801)------------------------------
% 1.42/0.55  % (7801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (7801)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (7801)Memory used [KB]: 10618
% 1.42/0.55  % (7801)Time elapsed: 0.139 s
% 1.42/0.55  % (7801)------------------------------
% 1.42/0.55  % (7801)------------------------------
% 1.42/0.55  % (7808)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.55  % (7806)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.55  % (7793)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.55  % (7794)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  % (7814)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.56  % (7800)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.56  % (7811)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.58/0.56  % (7802)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.57  % (7795)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.58/0.58  % (7808)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f509,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f127,f134,f143,f398,f407,f426,f459,f491,f501,f508])).
% 1.58/0.58  fof(f508,plain,(
% 1.58/0.58    ~spl7_4 | spl7_17 | ~spl7_20 | ~spl7_21),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f504])).
% 1.58/0.58  fof(f504,plain,(
% 1.58/0.58    $false | (~spl7_4 | spl7_17 | ~spl7_20 | ~spl7_21)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f490,f396,f500,f230])).
% 1.58/0.58  fof(f230,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = X0 | ~r2_hidden(X0,sK1)) ) | ~spl7_4),
% 1.58/0.58    inference(resolution,[],[f228,f96])).
% 1.58/0.58  fof(f96,plain,(
% 1.58/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.58/0.58    inference(equality_resolution,[],[f53])).
% 1.58/0.58  fof(f53,plain,(
% 1.58/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.58/0.58    inference(cnf_transformation,[],[f33])).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f31,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.58    inference(rectify,[],[f30])).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.58    inference(flattening,[],[f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.58    inference(nnf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.58/0.58  fof(f228,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2)) | sK3 = X0) ) | ~spl7_4),
% 1.58/0.58    inference(superposition,[],[f101,f120])).
% 1.58/0.58  fof(f120,plain,(
% 1.58/0.58    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl7_4),
% 1.58/0.58    inference(avatar_component_clause,[],[f118])).
% 1.58/0.58  fof(f118,plain,(
% 1.58/0.58    spl7_4 <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.58/0.58  fof(f101,plain,(
% 1.58/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.58/0.58    inference(equality_resolution,[],[f88])).
% 1.58/0.58  fof(f88,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.58/0.58    inference(definition_unfolding,[],[f59,f72])).
% 1.58/0.58  fof(f72,plain,(
% 1.58/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.58/0.58    inference(definition_unfolding,[],[f64,f71])).
% 1.58/0.58  fof(f71,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.58/0.58    inference(definition_unfolding,[],[f68,f70])).
% 1.58/0.58  fof(f70,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.58/0.58    inference(definition_unfolding,[],[f67,f69])).
% 1.58/0.58  fof(f69,plain,(
% 1.58/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f11])).
% 1.58/0.58  fof(f11,axiom,(
% 1.58/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.58  fof(f67,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f10])).
% 1.58/0.58  fof(f10,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.58  fof(f68,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f9])).
% 1.58/0.58  fof(f9,axiom,(
% 1.58/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.58  fof(f64,plain,(
% 1.58/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,axiom,(
% 1.58/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.58  fof(f59,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f38])).
% 1.58/0.58  fof(f38,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 1.58/0.58  fof(f37,plain,(
% 1.58/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f36,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.58/0.58    inference(rectify,[],[f35])).
% 1.58/0.58  fof(f35,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f7])).
% 1.58/0.58  fof(f7,axiom,(
% 1.58/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.58/0.58  fof(f500,plain,(
% 1.58/0.58    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2) | ~spl7_21),
% 1.58/0.58    inference(avatar_component_clause,[],[f498])).
% 1.58/0.58  fof(f498,plain,(
% 1.58/0.58    spl7_21 <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.58/0.58  fof(f396,plain,(
% 1.58/0.58    sK3 != sK6(sK3,k3_xboole_0(sK0,sK2)) | spl7_17),
% 1.58/0.58    inference(avatar_component_clause,[],[f395])).
% 1.58/0.58  fof(f395,plain,(
% 1.58/0.58    spl7_17 <=> sK3 = sK6(sK3,k3_xboole_0(sK0,sK2))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.58/0.58  fof(f490,plain,(
% 1.58/0.58    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1) | ~spl7_20),
% 1.58/0.58    inference(avatar_component_clause,[],[f488])).
% 1.58/0.58  fof(f488,plain,(
% 1.58/0.58    spl7_20 <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.58/0.58  fof(f501,plain,(
% 1.58/0.58    spl7_21 | ~spl7_16),
% 1.58/0.58    inference(avatar_split_clause,[],[f495,f391,f498])).
% 1.58/0.58  fof(f391,plain,(
% 1.58/0.58    spl7_16 <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.58/0.59  fof(f495,plain,(
% 1.58/0.59    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK2) | ~spl7_16),
% 1.58/0.59    inference(resolution,[],[f393,f97])).
% 1.58/0.59  fof(f97,plain,(
% 1.58/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.58/0.59    inference(equality_resolution,[],[f52])).
% 1.58/0.59  fof(f52,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.58/0.59    inference(cnf_transformation,[],[f33])).
% 1.58/0.59  fof(f393,plain,(
% 1.58/0.59    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2)) | ~spl7_16),
% 1.58/0.59    inference(avatar_component_clause,[],[f391])).
% 1.58/0.59  fof(f491,plain,(
% 1.58/0.59    spl7_20 | ~spl7_1 | ~spl7_18),
% 1.58/0.59    inference(avatar_split_clause,[],[f461,f404,f103,f488])).
% 1.58/0.59  fof(f103,plain,(
% 1.58/0.59    spl7_1 <=> r1_tarski(sK0,sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.58/0.59  fof(f404,plain,(
% 1.58/0.59    spl7_18 <=> r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.58/0.59  fof(f461,plain,(
% 1.58/0.59    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK1) | (~spl7_1 | ~spl7_18)),
% 1.58/0.59    inference(resolution,[],[f406,f176])).
% 1.58/0.59  fof(f176,plain,(
% 1.58/0.59    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) ) | ~spl7_1),
% 1.58/0.59    inference(resolution,[],[f154,f105])).
% 1.58/0.59  fof(f105,plain,(
% 1.58/0.59    r1_tarski(sK0,sK1) | ~spl7_1),
% 1.58/0.59    inference(avatar_component_clause,[],[f103])).
% 1.58/0.59  fof(f154,plain,(
% 1.58/0.59    ( ! [X6,X7,X5] : (~r1_tarski(X5,X6) | r2_hidden(X7,X6) | ~r2_hidden(X7,X5)) )),
% 1.58/0.59    inference(superposition,[],[f97,f128])).
% 1.58/0.59  fof(f128,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(superposition,[],[f65,f66])).
% 1.58/0.59  fof(f66,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f21,plain,(
% 1.58/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.58/0.59    inference(ennf_transformation,[],[f2])).
% 1.58/0.59  fof(f2,axiom,(
% 1.58/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.58/0.59  fof(f65,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.58/0.59    inference(cnf_transformation,[],[f4])).
% 1.58/0.59  fof(f4,axiom,(
% 1.58/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.58/0.59  fof(f406,plain,(
% 1.58/0.59    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0) | ~spl7_18),
% 1.58/0.59    inference(avatar_component_clause,[],[f404])).
% 1.58/0.59  fof(f459,plain,(
% 1.58/0.59    ~spl7_19 | spl7_5 | ~spl7_4 | ~spl7_17),
% 1.58/0.59    inference(avatar_split_clause,[],[f412,f395,f118,f124,f415])).
% 1.58/0.59  fof(f415,plain,(
% 1.58/0.59    spl7_19 <=> r2_hidden(sK3,k3_xboole_0(sK0,sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.58/0.59  fof(f124,plain,(
% 1.58/0.59    spl7_5 <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.58/0.59  fof(f412,plain,(
% 1.58/0.59    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) | ~r2_hidden(sK3,k3_xboole_0(sK0,sK2)) | (~spl7_4 | ~spl7_17)),
% 1.58/0.59    inference(forward_demodulation,[],[f411,f120])).
% 1.58/0.59  fof(f411,plain,(
% 1.58/0.59    k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(sK3,k3_xboole_0(sK0,sK2)) | ~spl7_17),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f410])).
% 1.58/0.59  fof(f410,plain,(
% 1.58/0.59    sK3 != sK3 | k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(sK3,k3_xboole_0(sK0,sK2)) | ~spl7_17),
% 1.58/0.59    inference(superposition,[],[f85,f397])).
% 1.58/0.59  fof(f397,plain,(
% 1.58/0.59    sK3 = sK6(sK3,k3_xboole_0(sK0,sK2)) | ~spl7_17),
% 1.58/0.59    inference(avatar_component_clause,[],[f395])).
% 1.58/0.59  fof(f85,plain,(
% 1.58/0.59    ( ! [X0,X1] : (sK6(X0,X1) != X0 | k3_enumset1(X0,X0,X0,X0,X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f62,f72])).
% 1.58/0.59  fof(f62,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f38])).
% 1.58/0.59  fof(f426,plain,(
% 1.58/0.59    ~spl7_2 | ~spl7_7 | spl7_19),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f420])).
% 1.58/0.59  fof(f420,plain,(
% 1.58/0.59    $false | (~spl7_2 | ~spl7_7 | spl7_19)),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f110,f142,f417,f96])).
% 1.58/0.59  fof(f417,plain,(
% 1.58/0.59    ~r2_hidden(sK3,k3_xboole_0(sK0,sK2)) | spl7_19),
% 1.58/0.59    inference(avatar_component_clause,[],[f415])).
% 1.58/0.59  fof(f142,plain,(
% 1.58/0.59    r2_hidden(sK3,sK2) | ~spl7_7),
% 1.58/0.59    inference(avatar_component_clause,[],[f140])).
% 1.58/0.59  fof(f140,plain,(
% 1.58/0.59    spl7_7 <=> r2_hidden(sK3,sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.58/0.59  fof(f110,plain,(
% 1.58/0.59    r2_hidden(sK3,sK0) | ~spl7_2),
% 1.58/0.59    inference(avatar_component_clause,[],[f108])).
% 1.58/0.59  fof(f108,plain,(
% 1.58/0.59    spl7_2 <=> r2_hidden(sK3,sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.58/0.59  fof(f407,plain,(
% 1.58/0.59    spl7_18 | ~spl7_16),
% 1.58/0.59    inference(avatar_split_clause,[],[f400,f391,f404])).
% 1.58/0.59  fof(f400,plain,(
% 1.58/0.59    r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),sK0) | ~spl7_16),
% 1.58/0.59    inference(resolution,[],[f393,f98])).
% 1.58/0.59  fof(f98,plain,(
% 1.58/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.58/0.59    inference(equality_resolution,[],[f51])).
% 1.58/0.59  fof(f51,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.58/0.59    inference(cnf_transformation,[],[f33])).
% 1.58/0.59  fof(f398,plain,(
% 1.58/0.59    spl7_16 | spl7_17 | spl7_3),
% 1.58/0.59    inference(avatar_split_clause,[],[f368,f113,f395,f391])).
% 1.58/0.59  fof(f113,plain,(
% 1.58/0.59    spl7_3 <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.58/0.59  fof(f368,plain,(
% 1.58/0.59    sK3 = sK6(sK3,k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK3,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,sK2)) | spl7_3),
% 1.58/0.59    inference(equality_resolution,[],[f342])).
% 1.58/0.59  fof(f342,plain,(
% 1.58/0.59    ( ! [X1] : (k3_xboole_0(sK0,sK2) != X1 | sK3 = sK6(sK3,X1) | r2_hidden(sK6(sK3,X1),X1)) ) | spl7_3),
% 1.58/0.59    inference(superposition,[],[f115,f86])).
% 1.58/0.59  fof(f86,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f61,f72])).
% 1.58/0.59  fof(f61,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f38])).
% 1.58/0.59  fof(f115,plain,(
% 1.58/0.59    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | spl7_3),
% 1.58/0.59    inference(avatar_component_clause,[],[f113])).
% 1.58/0.59  fof(f143,plain,(
% 1.58/0.59    spl7_7 | ~spl7_6),
% 1.58/0.59    inference(avatar_split_clause,[],[f137,f131,f140])).
% 1.58/0.59  fof(f131,plain,(
% 1.58/0.59    spl7_6 <=> r2_hidden(sK3,k3_xboole_0(sK1,sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.58/0.59  fof(f137,plain,(
% 1.58/0.59    r2_hidden(sK3,sK2) | ~spl7_6),
% 1.58/0.59    inference(resolution,[],[f97,f133])).
% 1.58/0.59  fof(f133,plain,(
% 1.58/0.59    r2_hidden(sK3,k3_xboole_0(sK1,sK2)) | ~spl7_6),
% 1.58/0.59    inference(avatar_component_clause,[],[f131])).
% 1.58/0.59  fof(f134,plain,(
% 1.58/0.59    spl7_6 | ~spl7_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f129,f118,f131])).
% 1.58/0.59  fof(f129,plain,(
% 1.58/0.59    r2_hidden(sK3,k3_xboole_0(sK1,sK2)) | ~spl7_4),
% 1.58/0.59    inference(superposition,[],[f90,f120])).
% 1.58/0.59  fof(f90,plain,(
% 1.58/0.59    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 1.58/0.59    inference(equality_resolution,[],[f89])).
% 1.58/0.59  fof(f89,plain,(
% 1.58/0.59    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 1.58/0.59    inference(equality_resolution,[],[f79])).
% 1.58/0.59  fof(f79,plain,(
% 1.58/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.58/0.59    inference(definition_unfolding,[],[f46,f70])).
% 1.58/0.59  fof(f46,plain,(
% 1.58/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.58/0.59    inference(cnf_transformation,[],[f28])).
% 1.58/0.59  fof(f28,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 1.58/0.59  fof(f27,plain,(
% 1.58/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f26,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.59    inference(rectify,[],[f25])).
% 1.58/0.59  fof(f25,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.59    inference(flattening,[],[f24])).
% 1.58/0.59  fof(f24,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.59    inference(nnf_transformation,[],[f20])).
% 1.58/0.59  fof(f20,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.58/0.59    inference(ennf_transformation,[],[f6])).
% 1.58/0.59  fof(f6,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.58/0.59  fof(f127,plain,(
% 1.58/0.59    ~spl7_5 | spl7_3 | ~spl7_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f122,f118,f113,f124])).
% 1.58/0.59  fof(f122,plain,(
% 1.58/0.59    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2) | (spl7_3 | ~spl7_4)),
% 1.58/0.59    inference(superposition,[],[f115,f120])).
% 1.58/0.59  fof(f121,plain,(
% 1.58/0.59    spl7_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f74,f118])).
% 1.58/0.59  fof(f74,plain,(
% 1.58/0.59    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.58/0.59    inference(definition_unfolding,[],[f40,f72])).
% 1.58/0.59  fof(f40,plain,(
% 1.58/0.59    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f23])).
% 1.58/0.59  fof(f23,plain,(
% 1.58/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.58/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).
% 1.58/0.59  fof(f22,plain,(
% 1.58/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f19,plain,(
% 1.58/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.58/0.59    inference(flattening,[],[f18])).
% 1.58/0.59  fof(f18,plain,(
% 1.58/0.59    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.58/0.59    inference(ennf_transformation,[],[f17])).
% 1.58/0.59  fof(f17,negated_conjecture,(
% 1.58/0.59    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.58/0.59    inference(negated_conjecture,[],[f16])).
% 1.58/0.59  fof(f16,conjecture,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.58/0.59  fof(f116,plain,(
% 1.58/0.59    ~spl7_3),
% 1.58/0.59    inference(avatar_split_clause,[],[f73,f113])).
% 1.58/0.59  fof(f73,plain,(
% 1.58/0.59    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.58/0.59    inference(definition_unfolding,[],[f42,f72])).
% 1.58/0.59  fof(f42,plain,(
% 1.58/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f23])).
% 1.58/0.59  fof(f111,plain,(
% 1.58/0.59    spl7_2),
% 1.58/0.59    inference(avatar_split_clause,[],[f41,f108])).
% 1.58/0.59  fof(f41,plain,(
% 1.58/0.59    r2_hidden(sK3,sK0)),
% 1.58/0.59    inference(cnf_transformation,[],[f23])).
% 1.58/0.59  fof(f106,plain,(
% 1.58/0.59    spl7_1),
% 1.58/0.59    inference(avatar_split_clause,[],[f39,f103])).
% 1.58/0.59  fof(f39,plain,(
% 1.58/0.59    r1_tarski(sK0,sK1)),
% 1.58/0.59    inference(cnf_transformation,[],[f23])).
% 1.58/0.59  % SZS output end Proof for theBenchmark
% 1.58/0.59  % (7808)------------------------------
% 1.58/0.59  % (7808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (7808)Termination reason: Refutation
% 1.58/0.59  
% 1.58/0.59  % (7808)Memory used [KB]: 11129
% 1.58/0.59  % (7808)Time elapsed: 0.128 s
% 1.58/0.59  % (7808)------------------------------
% 1.58/0.59  % (7808)------------------------------
% 1.58/0.59  % (7784)Success in time 0.227 s
%------------------------------------------------------------------------------
