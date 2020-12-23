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
% DateTime   : Thu Dec  3 12:43:26 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 208 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 ( 554 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f965,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f91,f542,f547,f936,f945,f955,f964])).

fof(f964,plain,
    ( ~ spl5_6
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f962])).

fof(f962,plain,
    ( $false
    | ~ spl5_6
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f541,f114,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f114,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_6
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f541,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl5_18
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f955,plain,
    ( spl5_6
    | ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | spl5_6
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f115,f96,f935,f106])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X3)
      | r1_xboole_0(X5,X4)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f935,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f933])).

fof(f933,plain,
    ( spl5_23
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f96,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f115,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f945,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f69,f74,f546,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f546,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl5_19
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f74,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f936,plain,
    ( spl5_23
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f918,f497,f933])).

fof(f497,plain,
    ( spl5_15
  <=> ! [X14] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f918,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_15 ),
    inference(resolution,[],[f345,f549])).

fof(f549,plain,
    ( ! [X1] : r1_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_15 ),
    inference(resolution,[],[f498,f43])).

fof(f498,plain,
    ( ! [X14] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X14)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f497])).

fof(f345,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,k4_xboole_0(X4,X5))
      | r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f217,f41])).

fof(f217,plain,(
    ! [X12,X11] : r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11) ),
    inference(superposition,[],[f52,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f55,f54,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f547,plain,
    ( spl5_19
    | spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f483,f82,f497,f544])).

fof(f82,plain,
    ( spl5_4
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f483,plain,
    ( ! [X13] :
        ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X13)
        | r2_hidden(sK3,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f476,f302])).

fof(f302,plain,
    ( ! [X2,X3] :
        ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))
        | r2_hidden(sK3,X2) )
    | ~ spl5_4 ),
    inference(superposition,[],[f264,f63])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,X1))
        | r2_hidden(sK3,X0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f203,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f203,plain,
    ( ! [X8,X7] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(X7,k2_enumset1(sK3,sK3,sK3,sK3)),X8))
    | ~ spl5_4 ),
    inference(resolution,[],[f196,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] : r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(resolution,[],[f97,f43])).

fof(f97,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),X3) ),
    inference(resolution,[],[f40,f52])).

fof(f196,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X2)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f476,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f157,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK4(X2,X3),X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f46,f44])).

fof(f542,plain,
    ( ~ spl5_18
    | ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f526,f77,f88,f539])).

fof(f88,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f77,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f526,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f186,f79])).

fof(f79,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f186,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f36,f43])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f91,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f86,f72,f88])).

fof(f86,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f43,f74])).

fof(f85,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f60,f82])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f32,f54,f59])).

fof(f32,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f80,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:31:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1311)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (1311)Refutation not found, incomplete strategy% (1311)------------------------------
% 0.22/0.51  % (1311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1303)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (1307)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1311)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1311)Memory used [KB]: 10746
% 0.22/0.52  % (1311)Time elapsed: 0.074 s
% 0.22/0.52  % (1311)------------------------------
% 0.22/0.52  % (1311)------------------------------
% 0.22/0.52  % (1306)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (1308)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (1316)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (1304)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (1323)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (1320)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (1329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (1301)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (1329)Refutation not found, incomplete strategy% (1329)------------------------------
% 0.22/0.54  % (1329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1329)Memory used [KB]: 10746
% 0.22/0.54  % (1329)Time elapsed: 0.120 s
% 0.22/0.54  % (1329)------------------------------
% 0.22/0.54  % (1329)------------------------------
% 0.22/0.54  % (1305)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (1324)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (1302)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (1314)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (1328)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (1322)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (1325)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (1321)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (1327)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (1310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (1309)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (1330)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (1317)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (1312)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (1313)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (1317)Refutation not found, incomplete strategy% (1317)------------------------------
% 0.22/0.55  % (1317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1317)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1317)Memory used [KB]: 10618
% 0.22/0.55  % (1317)Time elapsed: 0.141 s
% 0.22/0.55  % (1317)------------------------------
% 0.22/0.55  % (1317)------------------------------
% 0.22/0.55  % (1319)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (1318)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (1315)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (1326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.72/0.62  % (1324)Refutation found. Thanks to Tanya!
% 1.72/0.62  % SZS status Theorem for theBenchmark
% 1.72/0.62  % SZS output start Proof for theBenchmark
% 1.72/0.62  fof(f965,plain,(
% 1.72/0.62    $false),
% 1.72/0.62    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f91,f542,f547,f936,f945,f955,f964])).
% 1.72/0.62  fof(f964,plain,(
% 1.72/0.62    ~spl5_6 | spl5_18),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f962])).
% 1.72/0.62  fof(f962,plain,(
% 1.72/0.62    $false | (~spl5_6 | spl5_18)),
% 1.72/0.62    inference(unit_resulting_resolution,[],[f541,f114,f43])).
% 1.72/0.62  fof(f43,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f22])).
% 1.72/0.62  fof(f22,plain,(
% 1.72/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.72/0.62    inference(ennf_transformation,[],[f3])).
% 1.72/0.62  fof(f3,axiom,(
% 1.72/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.72/0.62  fof(f114,plain,(
% 1.72/0.62    r1_xboole_0(sK0,sK1) | ~spl5_6),
% 1.72/0.62    inference(avatar_component_clause,[],[f113])).
% 1.72/0.62  fof(f113,plain,(
% 1.72/0.62    spl5_6 <=> r1_xboole_0(sK0,sK1)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.72/0.62  fof(f541,plain,(
% 1.72/0.62    ~r1_xboole_0(sK1,sK0) | spl5_18),
% 1.72/0.62    inference(avatar_component_clause,[],[f539])).
% 1.72/0.62  fof(f539,plain,(
% 1.72/0.62    spl5_18 <=> r1_xboole_0(sK1,sK0)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.72/0.62  fof(f955,plain,(
% 1.72/0.62    spl5_6 | ~spl5_23),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f947])).
% 1.72/0.62  fof(f947,plain,(
% 1.72/0.62    $false | (spl5_6 | ~spl5_23)),
% 1.72/0.62    inference(unit_resulting_resolution,[],[f115,f96,f935,f106])).
% 1.72/0.62  fof(f106,plain,(
% 1.72/0.62    ( ! [X4,X5,X3] : (~r1_tarski(X5,X3) | r1_xboole_0(X5,X4) | ~r1_xboole_0(X3,X4)) )),
% 1.72/0.62    inference(superposition,[],[f40,f41])).
% 1.72/0.62  fof(f41,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f26])).
% 1.72/0.62  fof(f26,plain,(
% 1.72/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.72/0.62    inference(nnf_transformation,[],[f10])).
% 1.72/0.62  fof(f10,axiom,(
% 1.72/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.72/0.62  fof(f40,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f21,plain,(
% 1.72/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.72/0.62    inference(ennf_transformation,[],[f6])).
% 1.72/0.62  fof(f6,axiom,(
% 1.72/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.72/0.62  fof(f935,plain,(
% 1.72/0.62    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_23),
% 1.72/0.62    inference(avatar_component_clause,[],[f933])).
% 1.72/0.62  fof(f933,plain,(
% 1.72/0.62    spl5_23 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.72/0.62  fof(f96,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.72/0.62    inference(resolution,[],[f40,f64])).
% 1.72/0.62  fof(f64,plain,(
% 1.72/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/0.62    inference(equality_resolution,[],[f50])).
% 1.72/0.62  fof(f50,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.72/0.62    inference(cnf_transformation,[],[f31])).
% 1.72/0.62  fof(f31,plain,(
% 1.72/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.62    inference(flattening,[],[f30])).
% 1.72/0.62  fof(f30,plain,(
% 1.72/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.62    inference(nnf_transformation,[],[f5])).
% 1.72/0.62  fof(f5,axiom,(
% 1.72/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.72/0.62  fof(f115,plain,(
% 1.72/0.62    ~r1_xboole_0(sK0,sK1) | spl5_6),
% 1.72/0.62    inference(avatar_component_clause,[],[f113])).
% 1.72/0.62  fof(f945,plain,(
% 1.72/0.62    ~spl5_1 | ~spl5_2 | ~spl5_19),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f939])).
% 1.72/0.62  fof(f939,plain,(
% 1.72/0.62    $false | (~spl5_1 | ~spl5_2 | ~spl5_19)),
% 1.72/0.62    inference(unit_resulting_resolution,[],[f69,f74,f546,f46])).
% 1.72/0.62  fof(f46,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f28])).
% 1.72/0.62  fof(f28,plain,(
% 1.72/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.72/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f27])).
% 1.72/0.62  fof(f27,plain,(
% 1.72/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.72/0.62    introduced(choice_axiom,[])).
% 1.72/0.62  fof(f23,plain,(
% 1.72/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.72/0.62    inference(ennf_transformation,[],[f17])).
% 1.72/0.62  fof(f17,plain,(
% 1.72/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.72/0.62    inference(rectify,[],[f4])).
% 1.72/0.62  fof(f4,axiom,(
% 1.72/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.72/0.62  fof(f546,plain,(
% 1.72/0.62    r2_hidden(sK3,sK1) | ~spl5_19),
% 1.72/0.62    inference(avatar_component_clause,[],[f544])).
% 1.72/0.62  fof(f544,plain,(
% 1.72/0.62    spl5_19 <=> r2_hidden(sK3,sK1)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.72/0.62  fof(f74,plain,(
% 1.72/0.62    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 1.72/0.62    inference(avatar_component_clause,[],[f72])).
% 1.72/0.62  fof(f72,plain,(
% 1.72/0.62    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.72/0.62  fof(f69,plain,(
% 1.72/0.62    r2_hidden(sK3,sK2) | ~spl5_1),
% 1.72/0.62    inference(avatar_component_clause,[],[f67])).
% 1.72/0.62  fof(f67,plain,(
% 1.72/0.62    spl5_1 <=> r2_hidden(sK3,sK2)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.72/0.62  fof(f936,plain,(
% 1.72/0.62    spl5_23 | ~spl5_15),
% 1.72/0.62    inference(avatar_split_clause,[],[f918,f497,f933])).
% 1.72/0.62  fof(f497,plain,(
% 1.72/0.62    spl5_15 <=> ! [X14] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X14)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.72/0.62  fof(f918,plain,(
% 1.72/0.62    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_15),
% 1.72/0.62    inference(resolution,[],[f345,f549])).
% 1.72/0.62  fof(f549,plain,(
% 1.72/0.62    ( ! [X1] : (r1_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_15),
% 1.72/0.62    inference(resolution,[],[f498,f43])).
% 1.72/0.62  fof(f498,plain,(
% 1.72/0.62    ( ! [X14] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X14)) ) | ~spl5_15),
% 1.72/0.62    inference(avatar_component_clause,[],[f497])).
% 1.72/0.62  fof(f345,plain,(
% 1.72/0.62    ( ! [X4,X5] : (~r1_xboole_0(X4,k4_xboole_0(X4,X5)) | r1_tarski(X4,X5)) )),
% 1.72/0.62    inference(superposition,[],[f217,f41])).
% 1.72/0.62  fof(f217,plain,(
% 1.72/0.62    ( ! [X12,X11] : (r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) )),
% 1.72/0.62    inference(superposition,[],[f52,f63])).
% 1.72/0.62  fof(f63,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.72/0.62    inference(definition_unfolding,[],[f55,f54,f54])).
% 1.72/0.62  fof(f54,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.62    inference(cnf_transformation,[],[f8])).
% 1.72/0.62  fof(f8,axiom,(
% 1.72/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.72/0.62  fof(f55,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f1])).
% 1.72/0.62  fof(f1,axiom,(
% 1.72/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.62  fof(f52,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f7])).
% 1.72/0.62  fof(f7,axiom,(
% 1.72/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.72/0.62  fof(f547,plain,(
% 1.72/0.62    spl5_19 | spl5_15 | ~spl5_4),
% 1.72/0.62    inference(avatar_split_clause,[],[f483,f82,f497,f544])).
% 1.72/0.62  fof(f82,plain,(
% 1.72/0.62    spl5_4 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.72/0.62  fof(f483,plain,(
% 1.72/0.62    ( ! [X13] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X13) | r2_hidden(sK3,sK1)) ) | ~spl5_4),
% 1.72/0.62    inference(resolution,[],[f476,f302])).
% 1.72/0.62  fof(f302,plain,(
% 1.72/0.62    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(X3,X2))) | r2_hidden(sK3,X2)) ) | ~spl5_4),
% 1.72/0.62    inference(superposition,[],[f264,f63])).
% 1.72/0.62  fof(f264,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,X1)) | r2_hidden(sK3,X0)) ) | ~spl5_4),
% 1.72/0.62    inference(superposition,[],[f203,f61])).
% 1.72/0.62  fof(f61,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f48,f59])).
% 1.72/0.62  fof(f59,plain,(
% 1.72/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f53,f58])).
% 1.72/0.62  fof(f58,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f56,f57])).
% 1.72/0.62  fof(f57,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f13])).
% 1.72/0.62  fof(f13,axiom,(
% 1.72/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.72/0.62  fof(f56,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f12])).
% 1.72/0.62  fof(f12,axiom,(
% 1.72/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.72/0.62  fof(f53,plain,(
% 1.72/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f11])).
% 1.72/0.62  fof(f11,axiom,(
% 1.72/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.72/0.62  fof(f48,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f29])).
% 1.72/0.62  fof(f29,plain,(
% 1.72/0.62    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.72/0.62    inference(nnf_transformation,[],[f14])).
% 1.72/0.62  fof(f14,axiom,(
% 1.72/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.72/0.62  fof(f203,plain,(
% 1.72/0.62    ( ! [X8,X7] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(X7,k2_enumset1(sK3,sK3,sK3,sK3)),X8))) ) | ~spl5_4),
% 1.72/0.62    inference(resolution,[],[f196,f132])).
% 1.72/0.62  fof(f132,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) )),
% 1.72/0.62    inference(resolution,[],[f97,f43])).
% 1.72/0.62  fof(f97,plain,(
% 1.72/0.62    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),X3)) )),
% 1.72/0.62    inference(resolution,[],[f40,f52])).
% 1.72/0.62  fof(f196,plain,(
% 1.72/0.62    ( ! [X2] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X2) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)) ) | ~spl5_4),
% 1.72/0.62    inference(resolution,[],[f106,f84])).
% 1.72/0.62  fof(f84,plain,(
% 1.72/0.62    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl5_4),
% 1.72/0.62    inference(avatar_component_clause,[],[f82])).
% 1.72/0.62  fof(f476,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 1.72/0.62    inference(duplicate_literal_removal,[],[f473])).
% 1.72/0.62  fof(f473,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.72/0.62    inference(resolution,[],[f157,f44])).
% 1.72/0.62  fof(f44,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f28])).
% 1.72/0.62  fof(f157,plain,(
% 1.72/0.62    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X2,X3),X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X2,X3)) )),
% 1.72/0.62    inference(resolution,[],[f46,f44])).
% 1.72/0.62  fof(f542,plain,(
% 1.72/0.62    ~spl5_18 | ~spl5_5 | spl5_3),
% 1.72/0.62    inference(avatar_split_clause,[],[f526,f77,f88,f539])).
% 1.72/0.62  fof(f88,plain,(
% 1.72/0.62    spl5_5 <=> r1_xboole_0(sK1,sK2)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.72/0.62  fof(f77,plain,(
% 1.72/0.62    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.72/0.62  fof(f526,plain,(
% 1.72/0.62    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl5_3),
% 1.72/0.62    inference(resolution,[],[f186,f79])).
% 1.72/0.62  fof(f79,plain,(
% 1.72/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 1.72/0.62    inference(avatar_component_clause,[],[f77])).
% 1.72/0.62  fof(f186,plain,(
% 1.72/0.62    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 1.72/0.62    inference(resolution,[],[f36,f43])).
% 1.72/0.62  fof(f36,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f20])).
% 1.72/0.62  fof(f20,plain,(
% 1.72/0.62    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.72/0.62    inference(ennf_transformation,[],[f9])).
% 1.72/0.62  fof(f9,axiom,(
% 1.72/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.72/0.62  fof(f91,plain,(
% 1.72/0.62    spl5_5 | ~spl5_2),
% 1.72/0.62    inference(avatar_split_clause,[],[f86,f72,f88])).
% 1.72/0.62  fof(f86,plain,(
% 1.72/0.62    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 1.72/0.62    inference(resolution,[],[f43,f74])).
% 1.72/0.62  fof(f85,plain,(
% 1.72/0.62    spl5_4),
% 1.72/0.62    inference(avatar_split_clause,[],[f60,f82])).
% 1.72/0.62  fof(f60,plain,(
% 1.72/0.62    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.72/0.62    inference(definition_unfolding,[],[f32,f54,f59])).
% 1.72/0.62  fof(f32,plain,(
% 1.72/0.62    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.72/0.62    inference(cnf_transformation,[],[f25])).
% 1.72/0.62  fof(f25,plain,(
% 1.72/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.72/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).
% 1.72/0.62  fof(f24,plain,(
% 1.72/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.72/0.62    introduced(choice_axiom,[])).
% 1.72/0.62  fof(f19,plain,(
% 1.72/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.72/0.62    inference(flattening,[],[f18])).
% 1.72/0.62  fof(f18,plain,(
% 1.72/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.72/0.62    inference(ennf_transformation,[],[f16])).
% 1.72/0.62  fof(f16,negated_conjecture,(
% 1.72/0.62    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.72/0.62    inference(negated_conjecture,[],[f15])).
% 1.72/0.62  fof(f15,conjecture,(
% 1.72/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.72/0.62  fof(f80,plain,(
% 1.72/0.62    ~spl5_3),
% 1.72/0.62    inference(avatar_split_clause,[],[f35,f77])).
% 1.72/0.62  fof(f35,plain,(
% 1.72/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.72/0.62    inference(cnf_transformation,[],[f25])).
% 1.72/0.62  fof(f75,plain,(
% 1.72/0.62    spl5_2),
% 1.72/0.62    inference(avatar_split_clause,[],[f34,f72])).
% 1.72/0.62  fof(f34,plain,(
% 1.72/0.62    r1_xboole_0(sK2,sK1)),
% 1.72/0.62    inference(cnf_transformation,[],[f25])).
% 1.72/0.62  fof(f70,plain,(
% 1.72/0.62    spl5_1),
% 1.72/0.62    inference(avatar_split_clause,[],[f33,f67])).
% 1.72/0.62  fof(f33,plain,(
% 1.72/0.62    r2_hidden(sK3,sK2)),
% 1.72/0.62    inference(cnf_transformation,[],[f25])).
% 1.72/0.62  % SZS output end Proof for theBenchmark
% 1.72/0.62  % (1324)------------------------------
% 1.72/0.62  % (1324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (1324)Termination reason: Refutation
% 1.72/0.62  
% 1.72/0.62  % (1324)Memory used [KB]: 11513
% 1.72/0.62  % (1324)Time elapsed: 0.179 s
% 1.72/0.62  % (1324)------------------------------
% 1.72/0.62  % (1324)------------------------------
% 1.72/0.63  % (1300)Success in time 0.254 s
%------------------------------------------------------------------------------
