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
% DateTime   : Thu Dec  3 12:38:00 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  227 (2038 expanded)
%              Number of leaves         :   40 ( 672 expanded)
%              Depth                    :   22
%              Number of atoms          :  604 (3529 expanded)
%              Number of equality atoms :  181 (2470 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f134,f141,f153,f222,f315,f477,f479,f482,f592,f747,f783,f1270,f1465,f1474,f2397])).

fof(f2397,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(avatar_contradiction_clause,[],[f2396])).

fof(f2396,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f2386,f124])).

fof(f124,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2386,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(superposition,[],[f56,f2361])).

fof(f2361,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(superposition,[],[f2207,f2319])).

fof(f2319,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f2318,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f2318,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,sK1)
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f2309,f56])).

fof(f2309,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_52 ),
    inference(superposition,[],[f1589,f55])).

fof(f1589,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f1586,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1586,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0))
    | ~ spl5_52 ),
    inference(superposition,[],[f82,f1464])).

fof(f1464,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1462])).

fof(f1462,plain,
    ( spl5_52
  <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f2207,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X2))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(superposition,[],[f2054,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2054,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f2052,f1523])).

fof(f1523,plain,
    ( ! [X1] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(resolution,[],[f1481,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f69,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f85,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1481,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f1432,f1464])).

fof(f1432,plain,
    ( ! [X1] : r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),X1)
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f1316,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1316,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f1286,f62])).

fof(f1286,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f152,f119])).

fof(f119,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f152,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_7
  <=> ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2052,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(resolution,[],[f1522,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f61,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f65,f93])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1522,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_52 ),
    inference(resolution,[],[f1481,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1474,plain,
    ( ~ spl5_1
    | ~ spl5_7
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f1473])).

fof(f1473,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f1468,f114])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1468,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_51 ),
    inference(backward_demodulation,[],[f1429,f1460])).

fof(f1460,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f1458,plain,
    ( spl5_51
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1429,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f1316,f1360])).

fof(f1360,plain,
    ( ! [X2] :
        ( r2_hidden(sK0,X2)
        | ~ r1_tarski(sK1,X2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f112,f119])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f95])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f92])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1465,plain,
    ( spl5_51
    | spl5_52
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1455,f118,f1462,f1458])).

fof(f1455,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f1359,f1317])).

fof(f1317,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1287,f62])).

fof(f1287,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f154,f119])).

fof(f154,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f143,f82])).

fof(f143,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f103,f99])).

fof(f99,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f51,f95,f93])).

fof(f51,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f1359,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | k1_xboole_0 = X1
        | sK1 = X1 )
    | ~ spl5_1 ),
    inference(superposition,[],[f110,f119])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f76,f95,f95])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1270,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1269])).

fof(f1269,plain,
    ( $false
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1268,f133])).

fof(f133,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1268,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f593,f1267])).

fof(f1267,plain,
    ( sK2 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(resolution,[],[f1261,f107])).

fof(f1261,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f1259,f1137])).

fof(f1137,plain,
    ( k1_xboole_0 = k6_enumset1(k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f796,f1124])).

fof(f1124,plain,
    ( sK3(k1_xboole_0,sK2) = k3_tarski(k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(superposition,[],[f101,f796])).

fof(f101,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f93])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f796,plain,
    ( k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f314,f221])).

fof(f221,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_10
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f314,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl5_18
  <=> k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1259,plain,
    ( r1_tarski(k6_enumset1(k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0)),sK2)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(resolution,[],[f1226,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f80,f95])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1226,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),sK2)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(resolution,[],[f1144,f799])).

fof(f799,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_3
    | spl5_6 ),
    inference(forward_demodulation,[],[f149,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f149,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1144,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_xboole_0,X0)
        | r2_hidden(k3_tarski(k1_xboole_0),X0) )
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f1125,f1124])).

fof(f1125,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_xboole_0,X0)
        | r2_hidden(sK3(k1_xboole_0,sK2),X0) )
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(superposition,[],[f106,f796])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f95])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f593,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f99,f128])).

fof(f783,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | ~ spl5_3
    | spl5_4
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f776,f133])).

fof(f776,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f593,f768])).

fof(f768,plain,
    ( ! [X1] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f646,f221])).

fof(f646,plain,
    ( ! [X1] : k3_tarski(k6_enumset1(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X1)) = X1
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f620,f107])).

fof(f620,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f597,f74])).

fof(f597,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f152,f128])).

fof(f747,plain,
    ( ~ spl5_3
    | ~ spl5_7
    | spl5_9
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_7
    | spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f708,f217])).

fof(f217,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl5_9
  <=> r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f708,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3
    | ~ spl5_7
    | spl5_10 ),
    inference(superposition,[],[f116,f648])).

fof(f648,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ spl5_3
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f647,f220])).

fof(f220,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f647,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) )
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f620,f110])).

fof(f116,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f77,f95])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f592,plain,
    ( ~ spl5_1
    | spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl5_1
    | spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f590,f140])).

fof(f140,plain,
    ( sK1 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f590,plain,
    ( sK1 = sK2
    | ~ spl5_1
    | spl5_6 ),
    inference(forward_demodulation,[],[f588,f483])).

fof(f483,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f99,f119])).

fof(f588,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_1
    | spl5_6 ),
    inference(resolution,[],[f581,f107])).

fof(f581,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(forward_demodulation,[],[f579,f119])).

fof(f579,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(resolution,[],[f574,f111])).

fof(f574,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(resolution,[],[f515,f149])).

fof(f515,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f106,f119])).

fof(f482,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f158,f127,f118])).

fof(f158,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f144,f110])).

fof(f144,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f102,f99])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f93])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f479,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | spl5_17 ),
    inference(subsumption_resolution,[],[f470,f200])).

fof(f200,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f154,f128])).

fof(f470,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)
    | ~ spl5_3
    | spl5_6
    | spl5_17 ),
    inference(backward_demodulation,[],[f310,f462])).

fof(f462,plain,
    ( k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))
    | ~ spl5_3
    | spl5_6 ),
    inference(subsumption_resolution,[],[f460,f116])).

fof(f460,plain,
    ( k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)))
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f242,f72])).

fof(f242,plain,
    ( r1_tarski(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k1_xboole_0)
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f225,f111])).

fof(f225,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f224,f200])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)
        | r2_hidden(sK3(k1_xboole_0,sK2),X0) )
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f201,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f201,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3
    | spl5_6 ),
    inference(forward_demodulation,[],[f157,f128])).

fof(f157,plain,
    ( r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_6 ),
    inference(forward_demodulation,[],[f156,f99])).

fof(f156,plain,
    ( r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))
    | spl5_6 ),
    inference(forward_demodulation,[],[f155,f82])).

fof(f155,plain,
    ( r2_hidden(sK3(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | spl5_6 ),
    inference(resolution,[],[f149,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f66,f94])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f310,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl5_17
  <=> r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f477,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f463,f217])).

fof(f463,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3
    | spl5_6 ),
    inference(backward_demodulation,[],[f223,f462])).

fof(f223,plain,
    ( r1_tarski(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f201,f111])).

fof(f315,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f305,f147,f127,f312,f308])).

fof(f305,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))
    | ~ r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)))
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f223,f72])).

fof(f222,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f212,f127,f219,f215])).

fof(f212,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_3 ),
    inference(resolution,[],[f200,f72])).

fof(f153,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f145,f151,f147])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
      | ~ r1_xboole_0(sK1,sK2) ) ),
    inference(forward_demodulation,[],[f142,f82])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
      | ~ r1_xboole_0(sK1,sK2) ) ),
    inference(superposition,[],[f104,f99])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f94])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f141,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f136,f118,f138])).

fof(f136,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f135])).

fof(f135,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f98])).

fof(f98,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f52,f95,f95])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f134,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f97,f131,f127])).

fof(f97,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f53,f95])).

fof(f53,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f96,f122,f118])).

fof(f96,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f54,f95])).

fof(f54,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (855)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (864)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (854)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (850)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (848)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (851)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (849)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (873)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (846)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (847)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (865)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (865)Refutation not found, incomplete strategy% (865)------------------------------
% 0.22/0.53  % (865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (858)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (865)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (865)Memory used [KB]: 10618
% 0.22/0.53  % (865)Time elapsed: 0.123 s
% 0.22/0.53  % (865)------------------------------
% 0.22/0.53  % (865)------------------------------
% 0.22/0.53  % (856)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (852)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (874)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (853)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (857)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (856)Refutation not found, incomplete strategy% (856)------------------------------
% 0.22/0.56  % (856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (856)Memory used [KB]: 10618
% 0.22/0.56  % (856)Time elapsed: 0.152 s
% 0.22/0.56  % (856)------------------------------
% 0.22/0.56  % (856)------------------------------
% 0.22/0.56  % (857)Refutation not found, incomplete strategy% (857)------------------------------
% 0.22/0.56  % (857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (857)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (857)Memory used [KB]: 10746
% 0.22/0.56  % (857)Time elapsed: 0.152 s
% 0.22/0.56  % (857)------------------------------
% 0.22/0.56  % (857)------------------------------
% 2.07/0.69  % (854)Refutation found. Thanks to Tanya!
% 2.07/0.69  % SZS status Theorem for theBenchmark
% 2.07/0.69  % SZS output start Proof for theBenchmark
% 2.07/0.69  fof(f2406,plain,(
% 2.07/0.69    $false),
% 2.07/0.69    inference(avatar_sat_refutation,[],[f125,f134,f141,f153,f222,f315,f477,f479,f482,f592,f747,f783,f1270,f1465,f1474,f2397])).
% 2.07/0.69  fof(f2397,plain,(
% 2.07/0.69    ~spl5_1 | spl5_2 | ~spl5_7 | ~spl5_52),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f2396])).
% 2.07/0.69  fof(f2396,plain,(
% 2.07/0.69    $false | (~spl5_1 | spl5_2 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(subsumption_resolution,[],[f2386,f124])).
% 2.07/0.69  fof(f124,plain,(
% 2.07/0.69    k1_xboole_0 != sK2 | spl5_2),
% 2.07/0.69    inference(avatar_component_clause,[],[f122])).
% 2.07/0.69  fof(f122,plain,(
% 2.07/0.69    spl5_2 <=> k1_xboole_0 = sK2),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.07/0.69  fof(f2386,plain,(
% 2.07/0.69    k1_xboole_0 = sK2 | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(superposition,[],[f56,f2361])).
% 2.07/0.69  fof(f2361,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(superposition,[],[f2207,f2319])).
% 2.07/0.69  fof(f2319,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) | ~spl5_52),
% 2.07/0.69    inference(forward_demodulation,[],[f2318,f55])).
% 2.07/0.69  fof(f55,plain,(
% 2.07/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f13])).
% 2.07/0.69  fof(f13,axiom,(
% 2.07/0.69    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.07/0.69  fof(f2318,plain,(
% 2.07/0.69    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,sK1) | ~spl5_52),
% 2.07/0.69    inference(forward_demodulation,[],[f2309,f56])).
% 2.07/0.69  fof(f2309,plain,(
% 2.07/0.69    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)) | ~spl5_52),
% 2.07/0.69    inference(superposition,[],[f1589,f55])).
% 2.07/0.69  fof(f1589,plain,(
% 2.07/0.69    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl5_52),
% 2.07/0.69    inference(forward_demodulation,[],[f1586,f82])).
% 2.07/0.69  fof(f82,plain,(
% 2.07/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f12])).
% 2.07/0.69  fof(f12,axiom,(
% 2.07/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.07/0.69  fof(f1586,plain,(
% 2.07/0.69    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0))) ) | ~spl5_52),
% 2.07/0.69    inference(superposition,[],[f82,f1464])).
% 2.07/0.69  fof(f1464,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl5_52),
% 2.07/0.69    inference(avatar_component_clause,[],[f1462])).
% 2.07/0.69  fof(f1462,plain,(
% 2.07/0.69    spl5_52 <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.07/0.69  fof(f2207,plain,(
% 2.07/0.69    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X2))) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(superposition,[],[f2054,f62])).
% 2.07/0.69  fof(f62,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f1])).
% 2.07/0.69  fof(f1,axiom,(
% 2.07/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.07/0.69  fof(f2054,plain,(
% 2.07/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0)) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(forward_demodulation,[],[f2052,f1523])).
% 2.07/0.69  fof(f1523,plain,(
% 2.07/0.69    ( ! [X1] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(resolution,[],[f1481,f107])).
% 2.07/0.69  fof(f107,plain,(
% 2.07/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 2.07/0.69    inference(definition_unfolding,[],[f69,f93])).
% 2.07/0.69  fof(f93,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.07/0.69    inference(definition_unfolding,[],[f63,f92])).
% 2.07/0.69  fof(f92,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f64,f91])).
% 2.07/0.69  fof(f91,plain,(
% 2.07/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f81,f90])).
% 2.07/0.69  fof(f90,plain,(
% 2.07/0.69    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f84,f89])).
% 2.07/0.69  fof(f89,plain,(
% 2.07/0.69    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f85,f88])).
% 2.07/0.69  fof(f88,plain,(
% 2.07/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f86,f87])).
% 2.07/0.69  fof(f87,plain,(
% 2.07/0.69    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f21])).
% 2.07/0.69  fof(f21,axiom,(
% 2.07/0.69    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.07/0.69  fof(f86,plain,(
% 2.07/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f20])).
% 2.07/0.69  fof(f20,axiom,(
% 2.07/0.69    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.07/0.69  fof(f85,plain,(
% 2.07/0.69    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f19])).
% 2.07/0.69  fof(f19,axiom,(
% 2.07/0.69    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.07/0.69  fof(f84,plain,(
% 2.07/0.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f18])).
% 2.07/0.69  fof(f18,axiom,(
% 2.07/0.69    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.07/0.69  fof(f81,plain,(
% 2.07/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f17])).
% 2.07/0.69  fof(f17,axiom,(
% 2.07/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.07/0.69  fof(f64,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f16])).
% 2.07/0.69  fof(f16,axiom,(
% 2.07/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.07/0.69  fof(f63,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f25])).
% 2.07/0.69  fof(f25,axiom,(
% 2.07/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.07/0.69  fof(f69,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f34])).
% 2.07/0.69  fof(f34,plain,(
% 2.07/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.07/0.69    inference(ennf_transformation,[],[f7])).
% 2.07/0.69  fof(f7,axiom,(
% 2.07/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.07/0.69  fof(f1481,plain,(
% 2.07/0.69    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(backward_demodulation,[],[f1432,f1464])).
% 2.07/0.69  fof(f1432,plain,(
% 2.07/0.69    ( ! [X1] : (r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),X1)) ) | (~spl5_1 | ~spl5_7)),
% 2.07/0.69    inference(resolution,[],[f1316,f74])).
% 2.07/0.69  fof(f74,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f47])).
% 2.07/0.69  fof(f47,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 2.07/0.69  fof(f46,plain,(
% 2.07/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.07/0.69    introduced(choice_axiom,[])).
% 2.07/0.69  fof(f45,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.69    inference(rectify,[],[f44])).
% 2.07/0.69  fof(f44,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.69    inference(nnf_transformation,[],[f35])).
% 2.07/0.69  fof(f35,plain,(
% 2.07/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.07/0.69    inference(ennf_transformation,[],[f2])).
% 2.07/0.69  fof(f2,axiom,(
% 2.07/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.07/0.69  fof(f1316,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) ) | (~spl5_1 | ~spl5_7)),
% 2.07/0.69    inference(forward_demodulation,[],[f1286,f62])).
% 2.07/0.69  fof(f1286,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) ) | (~spl5_1 | ~spl5_7)),
% 2.07/0.69    inference(backward_demodulation,[],[f152,f119])).
% 2.07/0.69  fof(f119,plain,(
% 2.07/0.69    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 2.07/0.69    inference(avatar_component_clause,[],[f118])).
% 2.07/0.69  fof(f118,plain,(
% 2.07/0.69    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.07/0.69  fof(f152,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ) | ~spl5_7),
% 2.07/0.69    inference(avatar_component_clause,[],[f151])).
% 2.07/0.69  fof(f151,plain,(
% 2.07/0.69    spl5_7 <=> ! [X0] : ~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.07/0.69  fof(f2052,plain,(
% 2.07/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(resolution,[],[f1522,f103])).
% 2.07/0.69  fof(f103,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f61,f94])).
% 2.07/0.69  fof(f94,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.07/0.69    inference(definition_unfolding,[],[f65,f93])).
% 2.07/0.69  fof(f65,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f14])).
% 2.07/0.69  fof(f14,axiom,(
% 2.07/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.07/0.69  fof(f61,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f8])).
% 2.07/0.69  fof(f8,axiom,(
% 2.07/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.07/0.69  fof(f1522,plain,(
% 2.07/0.69    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | (~spl5_1 | ~spl5_7 | ~spl5_52)),
% 2.07/0.69    inference(resolution,[],[f1481,f72])).
% 2.07/0.69  fof(f72,plain,(
% 2.07/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f43])).
% 2.07/0.69  fof(f43,plain,(
% 2.07/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.69    inference(flattening,[],[f42])).
% 2.07/0.69  fof(f42,plain,(
% 2.07/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.69    inference(nnf_transformation,[],[f6])).
% 2.07/0.69  fof(f6,axiom,(
% 2.07/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.07/0.69  fof(f56,plain,(
% 2.07/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.07/0.69    inference(cnf_transformation,[],[f9])).
% 2.07/0.69  fof(f9,axiom,(
% 2.07/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.07/0.69  fof(f1474,plain,(
% 2.07/0.69    ~spl5_1 | ~spl5_7 | ~spl5_51),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f1473])).
% 2.07/0.69  fof(f1473,plain,(
% 2.07/0.69    $false | (~spl5_1 | ~spl5_7 | ~spl5_51)),
% 2.07/0.69    inference(subsumption_resolution,[],[f1468,f114])).
% 2.07/0.69  fof(f114,plain,(
% 2.07/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.07/0.69    inference(equality_resolution,[],[f70])).
% 2.07/0.69  fof(f70,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.07/0.69    inference(cnf_transformation,[],[f43])).
% 2.07/0.69  fof(f1468,plain,(
% 2.07/0.69    ~r1_tarski(sK1,sK1) | (~spl5_1 | ~spl5_7 | ~spl5_51)),
% 2.07/0.69    inference(backward_demodulation,[],[f1429,f1460])).
% 2.07/0.69  fof(f1460,plain,(
% 2.07/0.69    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl5_51),
% 2.07/0.69    inference(avatar_component_clause,[],[f1458])).
% 2.07/0.69  fof(f1458,plain,(
% 2.07/0.69    spl5_51 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.07/0.69  fof(f1429,plain,(
% 2.07/0.69    ~r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | (~spl5_1 | ~spl5_7)),
% 2.07/0.69    inference(resolution,[],[f1316,f1360])).
% 2.07/0.69  fof(f1360,plain,(
% 2.07/0.69    ( ! [X2] : (r2_hidden(sK0,X2) | ~r1_tarski(sK1,X2)) ) | ~spl5_1),
% 2.07/0.69    inference(superposition,[],[f112,f119])).
% 2.07/0.69  fof(f112,plain,(
% 2.07/0.69    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f79,f95])).
% 2.07/0.69  fof(f95,plain,(
% 2.07/0.69    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f57,f92])).
% 2.07/0.69  fof(f57,plain,(
% 2.07/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f15])).
% 2.07/0.69  fof(f15,axiom,(
% 2.07/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.07/0.69  fof(f79,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f50])).
% 2.07/0.69  fof(f50,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.07/0.69    inference(nnf_transformation,[],[f22])).
% 2.07/0.69  fof(f22,axiom,(
% 2.07/0.69    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.07/0.69  fof(f1465,plain,(
% 2.07/0.69    spl5_51 | spl5_52 | ~spl5_1),
% 2.07/0.69    inference(avatar_split_clause,[],[f1455,f118,f1462,f1458])).
% 2.07/0.69  fof(f1455,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl5_1),
% 2.07/0.69    inference(resolution,[],[f1359,f1317])).
% 2.07/0.69  fof(f1317,plain,(
% 2.07/0.69    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_1),
% 2.07/0.69    inference(forward_demodulation,[],[f1287,f62])).
% 2.07/0.69  fof(f1287,plain,(
% 2.07/0.69    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl5_1),
% 2.07/0.69    inference(backward_demodulation,[],[f154,f119])).
% 2.07/0.69  fof(f154,plain,(
% 2.07/0.69    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.07/0.69    inference(forward_demodulation,[],[f143,f82])).
% 2.07/0.69  fof(f143,plain,(
% 2.07/0.69    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 2.07/0.69    inference(superposition,[],[f103,f99])).
% 2.07/0.69  fof(f99,plain,(
% 2.07/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.07/0.69    inference(definition_unfolding,[],[f51,f95,f93])).
% 2.07/0.69  fof(f51,plain,(
% 2.07/0.69    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.07/0.69    inference(cnf_transformation,[],[f39])).
% 2.07/0.69  fof(f39,plain,(
% 2.07/0.69    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.07/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38])).
% 2.07/0.69  fof(f38,plain,(
% 2.07/0.69    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.07/0.69    introduced(choice_axiom,[])).
% 2.07/0.69  fof(f31,plain,(
% 2.07/0.69    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.07/0.69    inference(ennf_transformation,[],[f27])).
% 2.07/0.69  fof(f27,negated_conjecture,(
% 2.07/0.69    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.07/0.69    inference(negated_conjecture,[],[f26])).
% 2.07/0.69  fof(f26,conjecture,(
% 2.07/0.69    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.07/0.69  fof(f1359,plain,(
% 2.07/0.69    ( ! [X1] : (~r1_tarski(X1,sK1) | k1_xboole_0 = X1 | sK1 = X1) ) | ~spl5_1),
% 2.07/0.69    inference(superposition,[],[f110,f119])).
% 2.07/0.69  fof(f110,plain,(
% 2.07/0.69    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 2.07/0.69    inference(definition_unfolding,[],[f76,f95,f95])).
% 2.07/0.69  fof(f76,plain,(
% 2.07/0.69    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f49])).
% 2.07/0.69  fof(f49,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.07/0.69    inference(flattening,[],[f48])).
% 2.07/0.69  fof(f48,plain,(
% 2.07/0.69    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.07/0.69    inference(nnf_transformation,[],[f24])).
% 2.07/0.69  fof(f24,axiom,(
% 2.07/0.69    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.07/0.69  fof(f1270,plain,(
% 2.07/0.69    ~spl5_3 | spl5_4 | spl5_6 | ~spl5_10 | ~spl5_18),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f1269])).
% 2.07/0.69  fof(f1269,plain,(
% 2.07/0.69    $false | (~spl5_3 | spl5_4 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(subsumption_resolution,[],[f1268,f133])).
% 2.07/0.69  fof(f133,plain,(
% 2.07/0.69    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 2.07/0.69    inference(avatar_component_clause,[],[f131])).
% 2.07/0.69  fof(f131,plain,(
% 2.07/0.69    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.07/0.69  fof(f1268,plain,(
% 2.07/0.69    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(backward_demodulation,[],[f593,f1267])).
% 2.07/0.69  fof(f1267,plain,(
% 2.07/0.69    sK2 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(resolution,[],[f1261,f107])).
% 2.07/0.69  fof(f1261,plain,(
% 2.07/0.69    r1_tarski(k1_xboole_0,sK2) | (~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(forward_demodulation,[],[f1259,f1137])).
% 2.07/0.69  fof(f1137,plain,(
% 2.07/0.69    k1_xboole_0 = k6_enumset1(k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0)) | (~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(backward_demodulation,[],[f796,f1124])).
% 2.07/0.69  fof(f1124,plain,(
% 2.07/0.69    sK3(k1_xboole_0,sK2) = k3_tarski(k1_xboole_0) | (~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(superposition,[],[f101,f796])).
% 2.07/0.69  fof(f101,plain,(
% 2.07/0.69    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.07/0.69    inference(definition_unfolding,[],[f59,f93])).
% 2.07/0.69  fof(f59,plain,(
% 2.07/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.07/0.69    inference(cnf_transformation,[],[f29])).
% 2.07/0.69  fof(f29,plain,(
% 2.07/0.69    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.07/0.69    inference(rectify,[],[f3])).
% 2.07/0.69  fof(f3,axiom,(
% 2.07/0.69    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.07/0.69  fof(f796,plain,(
% 2.07/0.69    k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) | (~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(forward_demodulation,[],[f314,f221])).
% 2.07/0.69  fof(f221,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_10),
% 2.07/0.69    inference(avatar_component_clause,[],[f219])).
% 2.07/0.69  fof(f219,plain,(
% 2.07/0.69    spl5_10 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.07/0.69  fof(f314,plain,(
% 2.07/0.69    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) | ~spl5_18),
% 2.07/0.69    inference(avatar_component_clause,[],[f312])).
% 2.07/0.69  fof(f312,plain,(
% 2.07/0.69    spl5_18 <=> k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.07/0.69  fof(f1259,plain,(
% 2.07/0.69    r1_tarski(k6_enumset1(k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0),k3_tarski(k1_xboole_0)),sK2) | (~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(resolution,[],[f1226,f111])).
% 2.07/0.69  fof(f111,plain,(
% 2.07/0.69    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f80,f95])).
% 2.07/0.69  fof(f80,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f50])).
% 2.07/0.69  fof(f1226,plain,(
% 2.07/0.69    r2_hidden(k3_tarski(k1_xboole_0),sK2) | (~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(resolution,[],[f1144,f799])).
% 2.07/0.69  fof(f799,plain,(
% 2.07/0.69    ~r1_xboole_0(k1_xboole_0,sK2) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(forward_demodulation,[],[f149,f128])).
% 2.07/0.69  fof(f128,plain,(
% 2.07/0.69    k1_xboole_0 = sK1 | ~spl5_3),
% 2.07/0.69    inference(avatar_component_clause,[],[f127])).
% 2.07/0.69  fof(f127,plain,(
% 2.07/0.69    spl5_3 <=> k1_xboole_0 = sK1),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.07/0.69  fof(f149,plain,(
% 2.07/0.69    ~r1_xboole_0(sK1,sK2) | spl5_6),
% 2.07/0.69    inference(avatar_component_clause,[],[f147])).
% 2.07/0.69  fof(f147,plain,(
% 2.07/0.69    spl5_6 <=> r1_xboole_0(sK1,sK2)),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.07/0.69  fof(f1144,plain,(
% 2.07/0.69    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | r2_hidden(k3_tarski(k1_xboole_0),X0)) ) | (~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(forward_demodulation,[],[f1125,f1124])).
% 2.07/0.69  fof(f1125,plain,(
% 2.07/0.69    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | r2_hidden(sK3(k1_xboole_0,sK2),X0)) ) | (~spl5_10 | ~spl5_18)),
% 2.07/0.69    inference(superposition,[],[f106,f796])).
% 2.07/0.69  fof(f106,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f68,f95])).
% 2.07/0.69  fof(f68,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f33])).
% 2.07/0.69  fof(f33,plain,(
% 2.07/0.69    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.07/0.69    inference(ennf_transformation,[],[f23])).
% 2.07/0.69  fof(f23,axiom,(
% 2.07/0.69    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.07/0.69  fof(f593,plain,(
% 2.07/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl5_3),
% 2.07/0.69    inference(backward_demodulation,[],[f99,f128])).
% 2.07/0.69  fof(f783,plain,(
% 2.07/0.69    ~spl5_3 | spl5_4 | ~spl5_7 | ~spl5_10),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f782])).
% 2.07/0.69  fof(f782,plain,(
% 2.07/0.69    $false | (~spl5_3 | spl5_4 | ~spl5_7 | ~spl5_10)),
% 2.07/0.69    inference(subsumption_resolution,[],[f776,f133])).
% 2.07/0.69  fof(f776,plain,(
% 2.07/0.69    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl5_3 | ~spl5_7 | ~spl5_10)),
% 2.07/0.69    inference(backward_demodulation,[],[f593,f768])).
% 2.07/0.69  fof(f768,plain,(
% 2.07/0.69    ( ! [X1] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1) ) | (~spl5_3 | ~spl5_7 | ~spl5_10)),
% 2.07/0.69    inference(backward_demodulation,[],[f646,f221])).
% 2.07/0.69  fof(f646,plain,(
% 2.07/0.69    ( ! [X1] : (k3_tarski(k6_enumset1(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X1)) = X1) ) | (~spl5_3 | ~spl5_7)),
% 2.07/0.69    inference(resolution,[],[f620,f107])).
% 2.07/0.69  fof(f620,plain,(
% 2.07/0.69    ( ! [X0] : (r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) ) | (~spl5_3 | ~spl5_7)),
% 2.07/0.69    inference(resolution,[],[f597,f74])).
% 2.07/0.69  fof(f597,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ) | (~spl5_3 | ~spl5_7)),
% 2.07/0.69    inference(backward_demodulation,[],[f152,f128])).
% 2.07/0.69  fof(f747,plain,(
% 2.07/0.69    ~spl5_3 | ~spl5_7 | spl5_9 | spl5_10),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f746])).
% 2.07/0.69  fof(f746,plain,(
% 2.07/0.69    $false | (~spl5_3 | ~spl5_7 | spl5_9 | spl5_10)),
% 2.07/0.69    inference(subsumption_resolution,[],[f708,f217])).
% 2.07/0.69  fof(f217,plain,(
% 2.07/0.69    ~r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl5_9),
% 2.07/0.69    inference(avatar_component_clause,[],[f215])).
% 2.07/0.69  fof(f215,plain,(
% 2.07/0.69    spl5_9 <=> r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.07/0.69  fof(f708,plain,(
% 2.07/0.69    r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl5_3 | ~spl5_7 | spl5_10)),
% 2.07/0.69    inference(superposition,[],[f116,f648])).
% 2.07/0.69  fof(f648,plain,(
% 2.07/0.69    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ) | (~spl5_3 | ~spl5_7 | spl5_10)),
% 2.07/0.69    inference(subsumption_resolution,[],[f647,f220])).
% 2.07/0.69  fof(f220,plain,(
% 2.07/0.69    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl5_10),
% 2.07/0.69    inference(avatar_component_clause,[],[f219])).
% 2.07/0.69  fof(f647,plain,(
% 2.07/0.69    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ) | (~spl5_3 | ~spl5_7)),
% 2.07/0.69    inference(resolution,[],[f620,f110])).
% 2.07/0.69  fof(f116,plain,(
% 2.07/0.69    ( ! [X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.07/0.69    inference(equality_resolution,[],[f109])).
% 2.07/0.69  fof(f109,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 2.07/0.69    inference(definition_unfolding,[],[f77,f95])).
% 2.07/0.69  fof(f77,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 2.07/0.69    inference(cnf_transformation,[],[f49])).
% 2.07/0.69  fof(f592,plain,(
% 2.07/0.69    ~spl5_1 | spl5_5 | spl5_6),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f591])).
% 2.07/0.69  fof(f591,plain,(
% 2.07/0.69    $false | (~spl5_1 | spl5_5 | spl5_6)),
% 2.07/0.69    inference(subsumption_resolution,[],[f590,f140])).
% 2.07/0.69  fof(f140,plain,(
% 2.07/0.69    sK1 != sK2 | spl5_5),
% 2.07/0.69    inference(avatar_component_clause,[],[f138])).
% 2.07/0.69  fof(f138,plain,(
% 2.07/0.69    spl5_5 <=> sK1 = sK2),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.07/0.69  fof(f590,plain,(
% 2.07/0.69    sK1 = sK2 | (~spl5_1 | spl5_6)),
% 2.07/0.69    inference(forward_demodulation,[],[f588,f483])).
% 2.07/0.69  fof(f483,plain,(
% 2.07/0.69    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_1),
% 2.07/0.69    inference(backward_demodulation,[],[f99,f119])).
% 2.07/0.69  fof(f588,plain,(
% 2.07/0.69    sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (~spl5_1 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f581,f107])).
% 2.07/0.69  fof(f581,plain,(
% 2.07/0.69    r1_tarski(sK1,sK2) | (~spl5_1 | spl5_6)),
% 2.07/0.69    inference(forward_demodulation,[],[f579,f119])).
% 2.07/0.69  fof(f579,plain,(
% 2.07/0.69    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | (~spl5_1 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f574,f111])).
% 2.07/0.69  fof(f574,plain,(
% 2.07/0.69    r2_hidden(sK0,sK2) | (~spl5_1 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f515,f149])).
% 2.07/0.69  fof(f515,plain,(
% 2.07/0.69    ( ! [X0] : (r1_xboole_0(sK1,X0) | r2_hidden(sK0,X0)) ) | ~spl5_1),
% 2.07/0.69    inference(superposition,[],[f106,f119])).
% 2.07/0.69  fof(f482,plain,(
% 2.07/0.69    spl5_1 | spl5_3),
% 2.07/0.69    inference(avatar_split_clause,[],[f158,f127,f118])).
% 2.07/0.69  fof(f158,plain,(
% 2.07/0.69    k1_xboole_0 = sK1 | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.07/0.69    inference(resolution,[],[f144,f110])).
% 2.07/0.69  fof(f144,plain,(
% 2.07/0.69    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.07/0.69    inference(superposition,[],[f102,f99])).
% 2.07/0.69  fof(f102,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.07/0.69    inference(definition_unfolding,[],[f60,f93])).
% 2.07/0.69  fof(f60,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f11])).
% 2.07/0.69  fof(f11,axiom,(
% 2.07/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.07/0.69  fof(f479,plain,(
% 2.07/0.69    ~spl5_3 | spl5_6 | spl5_17),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f478])).
% 2.07/0.69  fof(f478,plain,(
% 2.07/0.69    $false | (~spl5_3 | spl5_6 | spl5_17)),
% 2.07/0.69    inference(subsumption_resolution,[],[f470,f200])).
% 2.07/0.69  fof(f200,plain,(
% 2.07/0.69    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) | ~spl5_3),
% 2.07/0.69    inference(forward_demodulation,[],[f154,f128])).
% 2.07/0.69  fof(f470,plain,(
% 2.07/0.69    ~r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) | (~spl5_3 | spl5_6 | spl5_17)),
% 2.07/0.69    inference(backward_demodulation,[],[f310,f462])).
% 2.07/0.69  fof(f462,plain,(
% 2.07/0.69    k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(subsumption_resolution,[],[f460,f116])).
% 2.07/0.69  fof(f460,plain,(
% 2.07/0.69    k1_xboole_0 = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) | ~r1_tarski(k1_xboole_0,k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f242,f72])).
% 2.07/0.69  fof(f242,plain,(
% 2.07/0.69    r1_tarski(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k1_xboole_0) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f225,f111])).
% 2.07/0.69  fof(f225,plain,(
% 2.07/0.69    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f224,f200])).
% 2.07/0.69  fof(f224,plain,(
% 2.07/0.69    ( ! [X0] : (~r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0) | r2_hidden(sK3(k1_xboole_0,sK2),X0)) ) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f201,f73])).
% 2.07/0.69  fof(f73,plain,(
% 2.07/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f47])).
% 2.07/0.69  fof(f201,plain,(
% 2.07/0.69    r2_hidden(sK3(k1_xboole_0,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(forward_demodulation,[],[f157,f128])).
% 2.07/0.69  fof(f157,plain,(
% 2.07/0.69    r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl5_6),
% 2.07/0.69    inference(forward_demodulation,[],[f156,f99])).
% 2.07/0.69  fof(f156,plain,(
% 2.07/0.69    r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) | spl5_6),
% 2.07/0.69    inference(forward_demodulation,[],[f155,f82])).
% 2.07/0.69  fof(f155,plain,(
% 2.07/0.69    r2_hidden(sK3(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | spl5_6),
% 2.07/0.69    inference(resolution,[],[f149,f105])).
% 2.07/0.69  fof(f105,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.07/0.69    inference(definition_unfolding,[],[f66,f94])).
% 2.07/0.69  fof(f66,plain,(
% 2.07/0.69    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.07/0.69    inference(cnf_transformation,[],[f41])).
% 2.07/0.69  fof(f41,plain,(
% 2.07/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.07/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f40])).
% 2.07/0.69  fof(f40,plain,(
% 2.07/0.69    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.07/0.69    introduced(choice_axiom,[])).
% 2.07/0.69  fof(f32,plain,(
% 2.07/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.07/0.69    inference(ennf_transformation,[],[f30])).
% 2.07/0.69  fof(f30,plain,(
% 2.07/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.07/0.69    inference(rectify,[],[f5])).
% 2.07/0.69  fof(f5,axiom,(
% 2.07/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.07/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.07/0.69  fof(f310,plain,(
% 2.07/0.69    ~r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))) | spl5_17),
% 2.07/0.69    inference(avatar_component_clause,[],[f308])).
% 2.07/0.69  fof(f308,plain,(
% 2.07/0.69    spl5_17 <=> r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)))),
% 2.07/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.07/0.69  fof(f477,plain,(
% 2.07/0.69    ~spl5_3 | spl5_6 | spl5_9),
% 2.07/0.69    inference(avatar_contradiction_clause,[],[f476])).
% 2.07/0.69  fof(f476,plain,(
% 2.07/0.69    $false | (~spl5_3 | spl5_6 | spl5_9)),
% 2.07/0.69    inference(subsumption_resolution,[],[f463,f217])).
% 2.07/0.69  fof(f463,plain,(
% 2.07/0.69    r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(backward_demodulation,[],[f223,f462])).
% 2.07/0.69  fof(f223,plain,(
% 2.07/0.69    r1_tarski(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f201,f111])).
% 2.07/0.69  fof(f315,plain,(
% 2.07/0.69    ~spl5_17 | spl5_18 | ~spl5_3 | spl5_6),
% 2.07/0.69    inference(avatar_split_clause,[],[f305,f147,f127,f312,f308])).
% 2.07/0.69  fof(f305,plain,(
% 2.07/0.69    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)) | ~r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2))) | (~spl5_3 | spl5_6)),
% 2.07/0.69    inference(resolution,[],[f223,f72])).
% 2.07/0.69  fof(f222,plain,(
% 2.07/0.69    ~spl5_9 | spl5_10 | ~spl5_3),
% 2.07/0.69    inference(avatar_split_clause,[],[f212,f127,f219,f215])).
% 2.07/0.69  fof(f212,plain,(
% 2.07/0.69    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl5_3),
% 2.07/0.69    inference(resolution,[],[f200,f72])).
% 2.07/0.69  fof(f153,plain,(
% 2.07/0.69    ~spl5_6 | spl5_7),
% 2.07/0.69    inference(avatar_split_clause,[],[f145,f151,f147])).
% 2.07/0.69  fof(f145,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(sK1,sK2)) )),
% 2.07/0.69    inference(forward_demodulation,[],[f142,f82])).
% 2.07/0.69  fof(f142,plain,(
% 2.07/0.69    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2)) )),
% 2.07/0.69    inference(superposition,[],[f104,f99])).
% 2.07/0.69  fof(f104,plain,(
% 2.07/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 2.07/0.69    inference(definition_unfolding,[],[f67,f94])).
% 2.07/0.69  fof(f67,plain,(
% 2.07/0.69    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.07/0.69    inference(cnf_transformation,[],[f41])).
% 2.07/0.69  fof(f141,plain,(
% 2.07/0.69    ~spl5_5 | ~spl5_1),
% 2.07/0.69    inference(avatar_split_clause,[],[f136,f118,f138])).
% 2.07/0.69  fof(f136,plain,(
% 2.07/0.69    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.07/0.69    inference(inner_rewriting,[],[f135])).
% 2.07/0.69  fof(f135,plain,(
% 2.07/0.69    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.07/0.69    inference(inner_rewriting,[],[f98])).
% 2.07/0.69  fof(f98,plain,(
% 2.07/0.69    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.07/0.69    inference(definition_unfolding,[],[f52,f95,f95])).
% 2.07/0.69  fof(f52,plain,(
% 2.07/0.69    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.07/0.69    inference(cnf_transformation,[],[f39])).
% 2.07/0.69  fof(f134,plain,(
% 2.07/0.69    ~spl5_3 | ~spl5_4),
% 2.07/0.69    inference(avatar_split_clause,[],[f97,f131,f127])).
% 2.07/0.69  fof(f97,plain,(
% 2.07/0.69    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.07/0.69    inference(definition_unfolding,[],[f53,f95])).
% 2.07/0.69  fof(f53,plain,(
% 2.07/0.69    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.07/0.69    inference(cnf_transformation,[],[f39])).
% 2.07/0.69  fof(f125,plain,(
% 2.07/0.69    ~spl5_1 | ~spl5_2),
% 2.07/0.69    inference(avatar_split_clause,[],[f96,f122,f118])).
% 2.07/0.69  fof(f96,plain,(
% 2.07/0.69    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.07/0.69    inference(definition_unfolding,[],[f54,f95])).
% 2.07/0.69  fof(f54,plain,(
% 2.07/0.69    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.07/0.69    inference(cnf_transformation,[],[f39])).
% 2.07/0.69  % SZS output end Proof for theBenchmark
% 2.07/0.69  % (854)------------------------------
% 2.07/0.69  % (854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.69  % (854)Termination reason: Refutation
% 2.07/0.69  
% 2.07/0.69  % (854)Memory used [KB]: 12025
% 2.07/0.69  % (854)Time elapsed: 0.293 s
% 2.07/0.69  % (854)------------------------------
% 2.07/0.69  % (854)------------------------------
% 2.07/0.70  % (844)Success in time 0.333 s
%------------------------------------------------------------------------------
