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
% DateTime   : Thu Dec  3 12:41:29 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 764 expanded)
%              Number of leaves         :   47 ( 264 expanded)
%              Depth                    :   15
%              Number of atoms          :  651 (3056 expanded)
%              Number of equality atoms :  231 (1100 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f293,f334,f351,f374,f385,f445,f455,f460,f519,f578,f579,f591,f593,f597,f604,f605,f682,f693,f837,f1027,f1066,f1087,f1088,f1089,f1090,f1091,f1092,f1516,f1538])).

fof(f1538,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1516,plain,
    ( spl6_15
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1515])).

fof(f1515,plain,
    ( $false
    | spl6_15
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1492,f83])).

fof(f83,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1492,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_15
    | ~ spl6_28 ),
    inference(superposition,[],[f328,f471])).

fof(f471,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl6_28
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f328,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl6_15
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1092,plain,
    ( spl6_46
    | ~ spl6_27
    | spl6_30 ),
    inference(avatar_split_clause,[],[f1021,f515,f452,f1023])).

fof(f1023,plain,
    ( spl6_46
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f452,plain,
    ( spl6_27
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f515,plain,
    ( spl6_30
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1021,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_27
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1016,f516])).

fof(f516,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f515])).

fof(f1016,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_27 ),
    inference(resolution,[],[f454,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f454,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f452])).

fof(f1091,plain,
    ( spl6_24
    | ~ spl6_20
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f758,f571,f363,f397])).

fof(f397,plain,
    ( spl6_24
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f363,plain,
    ( spl6_20
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f571,plain,
    ( spl6_32
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f758,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_20
    | ~ spl6_32 ),
    inference(superposition,[],[f364,f573])).

fof(f573,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f571])).

fof(f364,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f363])).

fof(f1090,plain,
    ( ~ spl6_17
    | spl6_2
    | spl6_18
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f1082,f452,f348,f99,f344])).

fof(f344,plain,
    ( spl6_17
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f99,plain,
    ( spl6_2
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f348,plain,
    ( spl6_18
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1082,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2
    | spl6_18
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1081,f454])).

fof(f1081,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2
    | spl6_18 ),
    inference(subsumption_resolution,[],[f686,f350])).

fof(f350,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f348])).

fof(f686,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f239])).

fof(f239,plain,
    ( ! [X33] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X33
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),X33) )
    | spl6_2 ),
    inference(superposition,[],[f101,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f101,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f1089,plain,
    ( spl6_43
    | spl6_28
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f826,f442,f469,f833])).

fof(f833,plain,
    ( spl6_43
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f442,plain,
    ( spl6_26
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f826,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_26 ),
    inference(resolution,[],[f444,f92])).

fof(f444,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f442])).

fof(f1088,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1087,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1066,plain,
    ( spl6_17
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | spl6_17
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1045,f83])).

fof(f1045,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_17
    | ~ spl6_30 ),
    inference(superposition,[],[f345,f517])).

fof(f517,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f515])).

fof(f345,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f344])).

fof(f1027,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f837,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f693,plain,
    ( spl6_20
    | spl6_1
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f692,f359,f94,f363])).

fof(f94,plain,
    ( spl6_1
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f359,plain,
    ( spl6_19
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f692,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | spl6_1
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f691,f361])).

fof(f361,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f359])).

fof(f691,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(equality_resolution,[],[f240])).

fof(f240,plain,
    ( ! [X34] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X34
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),X34) )
    | spl6_1 ),
    inference(superposition,[],[f96,f70])).

fof(f96,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f682,plain,
    ( ~ spl6_15
    | ~ spl6_26
    | spl6_16
    | spl6_3 ),
    inference(avatar_split_clause,[],[f680,f104,f331,f442,f327])).

fof(f331,plain,
    ( spl6_16
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f104,plain,
    ( spl6_3
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f680,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,
    ( ! [X32] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X32
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),X32) )
    | spl6_3 ),
    inference(superposition,[],[f106,f70])).

fof(f106,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f605,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f604,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f597,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f179,f315])).

fof(f315,plain,(
    ! [X11] : sK3(X11,k1_xboole_0) = X11 ),
    inference(subsumption_resolution,[],[f313,f280])).

fof(f280,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f270,f277])).

fof(f277,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f144,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f87,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f270,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f143,f148])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(resolution,[],[f113,f63])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f63,f68])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f86,f68])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f313,plain,(
    ! [X11] :
      ( sK3(X11,k1_xboole_0) = X11
      | r2_hidden(X11,k1_xboole_0) ) ),
    inference(resolution,[],[f165,f280])).

fof(f165,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4),X4)
      | sK3(X3,X4) = X3
      | r2_hidden(X3,X4) ) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f179,plain,
    ( sK0 != sK3(sK0,k1_xboole_0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_11
  <=> sK0 = sK3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f593,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f288,f280])).

fof(f288,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl6_13
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f591,plain,
    ( spl6_28
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f461,f327,f469])).

fof(f461,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_15 ),
    inference(resolution,[],[f329,f84])).

fof(f84,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f329,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f327])).

fof(f579,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f578,plain,
    ( spl6_32
    | spl6_33
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f566,f359,f575,f571])).

fof(f575,plain,
    ( spl6_33
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f566,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_19 ),
    inference(resolution,[],[f361,f92])).

fof(f519,plain,
    ( spl6_30
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f513,f344,f515])).

fof(f513,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_17 ),
    inference(resolution,[],[f346,f92])).

fof(f346,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f344])).

fof(f460,plain,
    ( spl6_19
    | spl6_1 ),
    inference(avatar_split_clause,[],[f459,f94,f359])).

fof(f459,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,
    ( ! [X30] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X30
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X30),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X30),X30) )
    | spl6_1 ),
    inference(superposition,[],[f96,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f455,plain,
    ( spl6_17
    | spl6_27
    | spl6_2 ),
    inference(avatar_split_clause,[],[f449,f99,f452,f344])).

fof(f449,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,
    ( ! [X29] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X29
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X29),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X29),X29) )
    | spl6_2 ),
    inference(superposition,[],[f101,f72])).

fof(f445,plain,
    ( spl6_15
    | spl6_26
    | spl6_3 ),
    inference(avatar_split_clause,[],[f439,f104,f442,f327])).

fof(f439,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f206])).

fof(f206,plain,
    ( ! [X28] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X28
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X28),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X28),X28) )
    | spl6_3 ),
    inference(superposition,[],[f106,f72])).

fof(f385,plain,
    ( spl6_22
    | spl6_23
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f375,f371,f382,f378])).

fof(f378,plain,
    ( spl6_22
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f382,plain,
    ( spl6_23
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f371,plain,
    ( spl6_21
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f375,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl6_21 ),
    inference(resolution,[],[f373,f92])).

fof(f373,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f371])).

fof(f374,plain,
    ( spl6_21
    | spl6_4 ),
    inference(avatar_split_clause,[],[f369,f109,f371])).

fof(f109,plain,
    ( spl6_4
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f369,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f368,f280])).

fof(f368,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_4 ),
    inference(equality_resolution,[],[f209])).

fof(f209,plain,
    ( ! [X31] :
        ( k1_xboole_0 != X31
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X31),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X31),X31) )
    | spl6_4 ),
    inference(superposition,[],[f111,f72])).

fof(f111,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f351,plain,
    ( spl6_17
    | ~ spl6_18
    | spl6_2 ),
    inference(avatar_split_clause,[],[f341,f99,f348,f344])).

fof(f341,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,
    ( ! [X25] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X25
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X25),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X25),X25) )
    | spl6_2 ),
    inference(superposition,[],[f101,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f334,plain,
    ( spl6_15
    | ~ spl6_16
    | spl6_3 ),
    inference(avatar_split_clause,[],[f324,f104,f331,f327])).

fof(f324,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f191])).

fof(f191,plain,
    ( ! [X24] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X24
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X24),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X24),X24) )
    | spl6_3 ),
    inference(superposition,[],[f106,f71])).

fof(f293,plain,
    ( spl6_13
    | ~ spl6_14
    | spl6_4 ),
    inference(avatar_split_clause,[],[f284,f109,f290,f286])).

fof(f290,plain,
    ( spl6_14
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f284,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_4 ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,
    ( ! [X27] :
        ( k1_xboole_0 != X27
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X27),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X27),X27) )
    | spl6_4 ),
    inference(superposition,[],[f111,f71])).

fof(f112,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f62,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f30,f37,f57])).

fof(f30,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f107,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f61,f104])).

fof(f61,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f37,f57,f58])).

fof(f31,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f60,f99])).

fof(f60,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f32,f37,f57,f58])).

fof(f32,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f59,f94])).

fof(f59,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f57,f37,f57])).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:09:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (15243)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (15243)Refutation not found, incomplete strategy% (15243)------------------------------
% 0.21/0.52  % (15243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15243)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15243)Memory used [KB]: 1663
% 0.21/0.52  % (15243)Time elapsed: 0.106 s
% 0.21/0.52  % (15243)------------------------------
% 0.21/0.52  % (15243)------------------------------
% 0.21/0.53  % (15263)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (15268)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (15268)Refutation not found, incomplete strategy% (15268)------------------------------
% 0.21/0.54  % (15268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15268)Memory used [KB]: 10618
% 0.21/0.54  % (15268)Time elapsed: 0.120 s
% 0.21/0.54  % (15268)------------------------------
% 0.21/0.54  % (15268)------------------------------
% 0.21/0.55  % (15250)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (15260)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (15246)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (15257)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (15257)Refutation not found, incomplete strategy% (15257)------------------------------
% 0.21/0.56  % (15257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15257)Memory used [KB]: 1663
% 0.21/0.56  % (15257)Time elapsed: 0.136 s
% 0.21/0.56  % (15257)------------------------------
% 0.21/0.56  % (15257)------------------------------
% 0.21/0.56  % (15245)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (15244)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (15252)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (15269)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (15270)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (15242)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.57  % (15270)Refutation not found, incomplete strategy% (15270)------------------------------
% 0.21/0.57  % (15270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15270)Memory used [KB]: 6268
% 0.21/0.57  % (15270)Time elapsed: 0.151 s
% 0.21/0.57  % (15270)------------------------------
% 0.21/0.57  % (15270)------------------------------
% 0.21/0.57  % (15260)Refutation not found, incomplete strategy% (15260)------------------------------
% 0.21/0.57  % (15260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15260)Memory used [KB]: 10618
% 0.21/0.57  % (15260)Time elapsed: 0.104 s
% 0.21/0.57  % (15260)------------------------------
% 0.21/0.57  % (15260)------------------------------
% 0.21/0.57  % (15265)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (15266)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (15251)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (15253)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (15273)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (15254)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (15273)Refutation not found, incomplete strategy% (15273)------------------------------
% 0.21/0.58  % (15273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (15273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (15273)Memory used [KB]: 1663
% 0.21/0.58  % (15273)Time elapsed: 0.161 s
% 0.21/0.58  % (15273)------------------------------
% 0.21/0.58  % (15273)------------------------------
% 0.21/0.58  % (15261)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.58  % (15261)Refutation not found, incomplete strategy% (15261)------------------------------
% 0.21/0.58  % (15261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (15261)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (15261)Memory used [KB]: 1663
% 0.21/0.58  % (15261)Time elapsed: 0.160 s
% 0.21/0.58  % (15261)------------------------------
% 0.21/0.58  % (15261)------------------------------
% 0.21/0.58  % (15256)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.59  % (15248)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.59  % (15258)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.59  % (15262)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (15262)Refutation not found, incomplete strategy% (15262)------------------------------
% 0.21/0.59  % (15262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (15262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (15262)Memory used [KB]: 1663
% 0.21/0.59  % (15262)Time elapsed: 0.177 s
% 0.21/0.59  % (15262)------------------------------
% 0.21/0.59  % (15262)------------------------------
% 0.21/0.59  % (15271)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.59  % (15271)Refutation not found, incomplete strategy% (15271)------------------------------
% 0.21/0.59  % (15271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (15271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (15271)Memory used [KB]: 6140
% 0.21/0.59  % (15271)Time elapsed: 0.177 s
% 0.21/0.59  % (15271)------------------------------
% 0.21/0.59  % (15271)------------------------------
% 1.83/0.59  % (15267)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.83/0.60  % (15249)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.83/0.60  % (15264)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.83/0.60  % (15272)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.83/0.60  % (15255)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.04/0.64  % (15292)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.68  % (15293)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.69  % (15294)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.69/0.71  % (15297)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.69/0.72  % (15295)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.69/0.72  % (15245)Refutation not found, incomplete strategy% (15245)------------------------------
% 2.69/0.72  % (15245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.72  % (15245)Termination reason: Refutation not found, incomplete strategy
% 2.69/0.72  
% 2.69/0.72  % (15245)Memory used [KB]: 6140
% 2.69/0.72  % (15245)Time elapsed: 0.298 s
% 2.69/0.72  % (15245)------------------------------
% 2.69/0.72  % (15245)------------------------------
% 2.69/0.73  % (15300)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.69/0.73  % (15298)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.69/0.75  % (15296)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.69/0.75  % (15296)Refutation not found, incomplete strategy% (15296)------------------------------
% 2.69/0.75  % (15296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.75  % (15296)Termination reason: Refutation not found, incomplete strategy
% 2.69/0.75  
% 2.69/0.75  % (15296)Memory used [KB]: 10618
% 2.69/0.75  % (15296)Time elapsed: 0.145 s
% 2.69/0.75  % (15296)------------------------------
% 2.69/0.75  % (15296)------------------------------
% 2.69/0.76  % (15301)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.17/0.85  % (15244)Time limit reached!
% 3.17/0.85  % (15244)------------------------------
% 3.17/0.85  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.85  % (15244)Termination reason: Time limit
% 3.17/0.85  
% 3.17/0.85  % (15244)Memory used [KB]: 6396
% 3.17/0.85  % (15244)Time elapsed: 0.401 s
% 3.17/0.85  % (15244)------------------------------
% 3.17/0.85  % (15244)------------------------------
% 3.17/0.86  % (15303)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.77/0.87  % (15293)Refutation found. Thanks to Tanya!
% 3.77/0.87  % SZS status Theorem for theBenchmark
% 3.77/0.87  % SZS output start Proof for theBenchmark
% 3.77/0.87  fof(f1539,plain,(
% 3.77/0.87    $false),
% 3.77/0.87    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f293,f334,f351,f374,f385,f445,f455,f460,f519,f578,f579,f591,f593,f597,f604,f605,f682,f693,f837,f1027,f1066,f1087,f1088,f1089,f1090,f1091,f1092,f1516,f1538])).
% 3.77/0.87  fof(f1538,plain,(
% 3.77/0.87    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f1516,plain,(
% 3.77/0.87    spl6_15 | ~spl6_28),
% 3.77/0.87    inference(avatar_contradiction_clause,[],[f1515])).
% 3.77/0.87  fof(f1515,plain,(
% 3.77/0.87    $false | (spl6_15 | ~spl6_28)),
% 3.77/0.87    inference(subsumption_resolution,[],[f1492,f83])).
% 3.77/0.87  fof(f83,plain,(
% 3.77/0.87    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.77/0.87    inference(equality_resolution,[],[f82])).
% 3.77/0.87  fof(f82,plain,(
% 3.77/0.87    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.77/0.87    inference(equality_resolution,[],[f66])).
% 3.77/0.87  fof(f66,plain,(
% 3.77/0.87    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.77/0.87    inference(definition_unfolding,[],[f39,f58])).
% 3.77/0.87  fof(f58,plain,(
% 3.77/0.87    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.77/0.87    inference(definition_unfolding,[],[f34,f57])).
% 3.77/0.87  fof(f57,plain,(
% 3.77/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.77/0.87    inference(definition_unfolding,[],[f36,f44])).
% 3.77/0.87  fof(f44,plain,(
% 3.77/0.87    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.77/0.87    inference(cnf_transformation,[],[f9])).
% 3.77/0.87  fof(f9,axiom,(
% 3.77/0.87    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.77/0.87  fof(f36,plain,(
% 3.77/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.77/0.87    inference(cnf_transformation,[],[f8])).
% 3.77/0.87  fof(f8,axiom,(
% 3.77/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.77/0.87  fof(f34,plain,(
% 3.77/0.87    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.77/0.87    inference(cnf_transformation,[],[f7])).
% 3.77/0.87  fof(f7,axiom,(
% 3.77/0.87    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.77/0.87  fof(f39,plain,(
% 3.77/0.87    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.77/0.87    inference(cnf_transformation,[],[f18])).
% 3.77/0.87  fof(f18,plain,(
% 3.77/0.87    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.77/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 3.77/0.87  fof(f17,plain,(
% 3.77/0.87    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.77/0.87    introduced(choice_axiom,[])).
% 3.77/0.87  fof(f16,plain,(
% 3.77/0.87    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.77/0.87    inference(rectify,[],[f15])).
% 3.77/0.87  fof(f15,plain,(
% 3.77/0.87    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.77/0.87    inference(nnf_transformation,[],[f5])).
% 3.77/0.87  fof(f5,axiom,(
% 3.77/0.87    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 3.77/0.87  fof(f1492,plain,(
% 3.77/0.87    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl6_15 | ~spl6_28)),
% 3.77/0.87    inference(superposition,[],[f328,f471])).
% 3.77/0.87  fof(f471,plain,(
% 3.77/0.87    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_28),
% 3.77/0.87    inference(avatar_component_clause,[],[f469])).
% 3.77/0.87  fof(f469,plain,(
% 3.77/0.87    spl6_28 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 3.77/0.87  fof(f328,plain,(
% 3.77/0.87    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_15),
% 3.77/0.87    inference(avatar_component_clause,[],[f327])).
% 3.77/0.87  fof(f327,plain,(
% 3.77/0.87    spl6_15 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.77/0.87  fof(f1092,plain,(
% 3.77/0.87    spl6_46 | ~spl6_27 | spl6_30),
% 3.77/0.87    inference(avatar_split_clause,[],[f1021,f515,f452,f1023])).
% 3.77/0.87  fof(f1023,plain,(
% 3.77/0.87    spl6_46 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 3.77/0.87  fof(f452,plain,(
% 3.77/0.87    spl6_27 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 3.77/0.87  fof(f515,plain,(
% 3.77/0.87    spl6_30 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 3.77/0.87  fof(f1021,plain,(
% 3.77/0.87    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (~spl6_27 | spl6_30)),
% 3.77/0.87    inference(subsumption_resolution,[],[f1016,f516])).
% 3.77/0.87  fof(f516,plain,(
% 3.77/0.87    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_30),
% 3.77/0.87    inference(avatar_component_clause,[],[f515])).
% 3.77/0.87  fof(f1016,plain,(
% 3.77/0.87    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_27),
% 3.77/0.87    inference(resolution,[],[f454,f92])).
% 3.77/0.87  fof(f92,plain,(
% 3.77/0.87    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 3.77/0.87    inference(equality_resolution,[],[f81])).
% 3.77/0.87  fof(f81,plain,(
% 3.77/0.87    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.77/0.87    inference(definition_unfolding,[],[f51,f57])).
% 3.77/0.87  fof(f51,plain,(
% 3.77/0.87    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.77/0.87    inference(cnf_transformation,[],[f29])).
% 3.77/0.87  fof(f29,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.77/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 3.77/0.87  fof(f28,plain,(
% 3.77/0.87    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 3.77/0.87    introduced(choice_axiom,[])).
% 3.77/0.87  fof(f27,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.77/0.87    inference(rectify,[],[f26])).
% 3.77/0.87  fof(f26,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.77/0.87    inference(flattening,[],[f25])).
% 3.77/0.87  fof(f25,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.77/0.87    inference(nnf_transformation,[],[f6])).
% 3.77/0.87  fof(f6,axiom,(
% 3.77/0.87    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.77/0.87  fof(f454,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_27),
% 3.77/0.87    inference(avatar_component_clause,[],[f452])).
% 3.77/0.87  fof(f1091,plain,(
% 3.77/0.87    spl6_24 | ~spl6_20 | ~spl6_32),
% 3.77/0.87    inference(avatar_split_clause,[],[f758,f571,f363,f397])).
% 3.77/0.87  fof(f397,plain,(
% 3.77/0.87    spl6_24 <=> r2_hidden(sK1,sK2)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 3.77/0.87  fof(f363,plain,(
% 3.77/0.87    spl6_20 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 3.77/0.87  fof(f571,plain,(
% 3.77/0.87    spl6_32 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 3.77/0.87  fof(f758,plain,(
% 3.77/0.87    r2_hidden(sK1,sK2) | (~spl6_20 | ~spl6_32)),
% 3.77/0.87    inference(superposition,[],[f364,f573])).
% 3.77/0.87  fof(f573,plain,(
% 3.77/0.87    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_32),
% 3.77/0.87    inference(avatar_component_clause,[],[f571])).
% 3.77/0.87  fof(f364,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~spl6_20),
% 3.77/0.87    inference(avatar_component_clause,[],[f363])).
% 3.77/0.87  fof(f1090,plain,(
% 3.77/0.87    ~spl6_17 | spl6_2 | spl6_18 | ~spl6_27),
% 3.77/0.87    inference(avatar_split_clause,[],[f1082,f452,f348,f99,f344])).
% 3.77/0.87  fof(f344,plain,(
% 3.77/0.87    spl6_17 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.77/0.87  fof(f99,plain,(
% 3.77/0.87    spl6_2 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.77/0.87  fof(f348,plain,(
% 3.77/0.87    spl6_18 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 3.77/0.87  fof(f1082,plain,(
% 3.77/0.87    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl6_2 | spl6_18 | ~spl6_27)),
% 3.77/0.87    inference(subsumption_resolution,[],[f1081,f454])).
% 3.77/0.87  fof(f1081,plain,(
% 3.77/0.87    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl6_2 | spl6_18)),
% 3.77/0.87    inference(subsumption_resolution,[],[f686,f350])).
% 3.77/0.87  fof(f350,plain,(
% 3.77/0.87    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | spl6_18),
% 3.77/0.87    inference(avatar_component_clause,[],[f348])).
% 3.77/0.87  fof(f686,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 3.77/0.87    inference(equality_resolution,[],[f239])).
% 3.77/0.87  fof(f239,plain,(
% 3.77/0.87    ( ! [X33] : (k2_enumset1(sK1,sK1,sK1,sK1) != X33 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X33),X33)) ) | spl6_2),
% 3.77/0.87    inference(superposition,[],[f101,f70])).
% 3.77/0.87  fof(f70,plain,(
% 3.77/0.87    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.77/0.87    inference(definition_unfolding,[],[f50,f37])).
% 3.77/0.87  fof(f37,plain,(
% 3.77/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.77/0.87    inference(cnf_transformation,[],[f3])).
% 3.77/0.87  fof(f3,axiom,(
% 3.77/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.77/0.87  fof(f50,plain,(
% 3.77/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.77/0.87    inference(cnf_transformation,[],[f24])).
% 3.77/0.87  fof(f24,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.77/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 3.77/0.87  fof(f23,plain,(
% 3.77/0.87    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.77/0.87    introduced(choice_axiom,[])).
% 3.77/0.87  fof(f22,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.77/0.87    inference(rectify,[],[f21])).
% 3.77/0.87  fof(f21,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.77/0.87    inference(flattening,[],[f20])).
% 3.77/0.87  fof(f20,plain,(
% 3.77/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.77/0.87    inference(nnf_transformation,[],[f1])).
% 3.77/0.87  fof(f1,axiom,(
% 3.77/0.87    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.77/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.77/0.87  fof(f101,plain,(
% 3.77/0.87    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_2),
% 3.77/0.87    inference(avatar_component_clause,[],[f99])).
% 3.77/0.87  fof(f1089,plain,(
% 3.77/0.87    spl6_43 | spl6_28 | ~spl6_26),
% 3.77/0.87    inference(avatar_split_clause,[],[f826,f442,f469,f833])).
% 3.77/0.87  fof(f833,plain,(
% 3.77/0.87    spl6_43 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 3.77/0.87  fof(f442,plain,(
% 3.77/0.87    spl6_26 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 3.77/0.87  fof(f826,plain,(
% 3.77/0.87    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_26),
% 3.77/0.87    inference(resolution,[],[f444,f92])).
% 3.77/0.87  fof(f444,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_26),
% 3.77/0.87    inference(avatar_component_clause,[],[f442])).
% 3.77/0.87  fof(f1088,plain,(
% 3.77/0.87    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f1087,plain,(
% 3.77/0.87    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f1066,plain,(
% 3.77/0.87    spl6_17 | ~spl6_30),
% 3.77/0.87    inference(avatar_contradiction_clause,[],[f1065])).
% 3.77/0.87  fof(f1065,plain,(
% 3.77/0.87    $false | (spl6_17 | ~spl6_30)),
% 3.77/0.87    inference(subsumption_resolution,[],[f1045,f83])).
% 3.77/0.87  fof(f1045,plain,(
% 3.77/0.87    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl6_17 | ~spl6_30)),
% 3.77/0.87    inference(superposition,[],[f345,f517])).
% 3.77/0.87  fof(f517,plain,(
% 3.77/0.87    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_30),
% 3.77/0.87    inference(avatar_component_clause,[],[f515])).
% 3.77/0.87  fof(f345,plain,(
% 3.77/0.87    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_17),
% 3.77/0.87    inference(avatar_component_clause,[],[f344])).
% 3.77/0.87  fof(f1027,plain,(
% 3.77/0.87    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f837,plain,(
% 3.77/0.87    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f693,plain,(
% 3.77/0.87    spl6_20 | spl6_1 | ~spl6_19),
% 3.77/0.87    inference(avatar_split_clause,[],[f692,f359,f94,f363])).
% 3.77/0.87  fof(f94,plain,(
% 3.77/0.87    spl6_1 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.77/0.87  fof(f359,plain,(
% 3.77/0.87    spl6_19 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 3.77/0.87  fof(f692,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | (spl6_1 | ~spl6_19)),
% 3.77/0.87    inference(subsumption_resolution,[],[f691,f361])).
% 3.77/0.87  fof(f361,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_19),
% 3.77/0.87    inference(avatar_component_clause,[],[f359])).
% 3.77/0.87  fof(f691,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 3.77/0.87    inference(duplicate_literal_removal,[],[f690])).
% 3.77/0.87  fof(f690,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 3.77/0.87    inference(equality_resolution,[],[f240])).
% 3.77/0.87  fof(f240,plain,(
% 3.77/0.87    ( ! [X34] : (k2_enumset1(sK0,sK0,sK0,sK1) != X34 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X34),X34)) ) | spl6_1),
% 3.77/0.87    inference(superposition,[],[f96,f70])).
% 3.77/0.87  fof(f96,plain,(
% 3.77/0.87    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl6_1),
% 3.77/0.87    inference(avatar_component_clause,[],[f94])).
% 3.77/0.87  fof(f682,plain,(
% 3.77/0.87    ~spl6_15 | ~spl6_26 | spl6_16 | spl6_3),
% 3.77/0.87    inference(avatar_split_clause,[],[f680,f104,f331,f442,f327])).
% 3.77/0.87  fof(f331,plain,(
% 3.77/0.87    spl6_16 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 3.77/0.87  fof(f104,plain,(
% 3.77/0.87    spl6_3 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.77/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.77/0.87  fof(f680,plain,(
% 3.77/0.87    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 3.77/0.87    inference(equality_resolution,[],[f238])).
% 3.77/0.87  fof(f238,plain,(
% 3.77/0.87    ( ! [X32] : (k2_enumset1(sK0,sK0,sK0,sK0) != X32 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X32),X32)) ) | spl6_3),
% 3.77/0.87    inference(superposition,[],[f106,f70])).
% 3.77/0.87  fof(f106,plain,(
% 3.77/0.87    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_3),
% 3.77/0.87    inference(avatar_component_clause,[],[f104])).
% 3.77/0.87  fof(f605,plain,(
% 3.77/0.87    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f604,plain,(
% 3.77/0.87    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.77/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.77/0.87  fof(f597,plain,(
% 3.77/0.87    spl6_11),
% 3.77/0.87    inference(avatar_contradiction_clause,[],[f596])).
% 3.77/0.87  fof(f596,plain,(
% 3.77/0.87    $false | spl6_11),
% 3.77/0.87    inference(subsumption_resolution,[],[f179,f315])).
% 3.77/0.87  fof(f315,plain,(
% 3.77/0.87    ( ! [X11] : (sK3(X11,k1_xboole_0) = X11) )),
% 3.77/0.87    inference(subsumption_resolution,[],[f313,f280])).
% 3.89/0.89  fof(f280,plain,(
% 3.89/0.89    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.89/0.89    inference(global_subsumption,[],[f270,f277])).
% 3.89/0.89  fof(f277,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r2_hidden(X0,k1_xboole_0)) )),
% 3.89/0.89    inference(resolution,[],[f144,f63])).
% 3.89/0.89  fof(f63,plain,(
% 3.89/0.89    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.89/0.89    inference(definition_unfolding,[],[f35,f37])).
% 3.89/0.89  fof(f35,plain,(
% 3.89/0.89    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.89/0.89    inference(cnf_transformation,[],[f4])).
% 3.89/0.89  fof(f4,axiom,(
% 3.89/0.89    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.89/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.89/0.89  fof(f144,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 3.89/0.89    inference(superposition,[],[f87,f68])).
% 3.89/0.89  fof(f68,plain,(
% 3.89/0.89    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.89/0.89    inference(definition_unfolding,[],[f43,f37])).
% 3.89/0.89  fof(f43,plain,(
% 3.89/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.89/0.89    inference(cnf_transformation,[],[f19])).
% 3.89/0.89  fof(f19,plain,(
% 3.89/0.89    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.89/0.89    inference(nnf_transformation,[],[f2])).
% 3.89/0.89  fof(f2,axiom,(
% 3.89/0.89    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.89/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.89/0.89  fof(f87,plain,(
% 3.89/0.89    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 3.89/0.89    inference(equality_resolution,[],[f75])).
% 3.89/0.89  fof(f75,plain,(
% 3.89/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.89/0.89    inference(definition_unfolding,[],[f45,f37])).
% 3.89/0.89  fof(f45,plain,(
% 3.89/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.89/0.89    inference(cnf_transformation,[],[f24])).
% 3.89/0.89  fof(f270,plain,(
% 3.89/0.89    ( ! [X4,X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) | ~r2_hidden(X2,k1_xboole_0)) )),
% 3.89/0.89    inference(resolution,[],[f143,f148])).
% 3.89/0.89  fof(f148,plain,(
% 3.89/0.89    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.89/0.89    inference(resolution,[],[f113,f63])).
% 3.89/0.89  fof(f113,plain,(
% 3.89/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_xboole_0,X0)) )),
% 3.89/0.89    inference(superposition,[],[f63,f68])).
% 3.89/0.89  fof(f143,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 3.89/0.89    inference(superposition,[],[f86,f68])).
% 3.89/0.89  fof(f86,plain,(
% 3.89/0.89    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.89/0.89    inference(equality_resolution,[],[f74])).
% 3.89/0.89  fof(f74,plain,(
% 3.89/0.89    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.89/0.89    inference(definition_unfolding,[],[f46,f37])).
% 3.89/0.89  fof(f46,plain,(
% 3.89/0.89    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.89/0.89    inference(cnf_transformation,[],[f24])).
% 3.89/0.89  fof(f313,plain,(
% 3.89/0.89    ( ! [X11] : (sK3(X11,k1_xboole_0) = X11 | r2_hidden(X11,k1_xboole_0)) )),
% 3.89/0.89    inference(resolution,[],[f165,f280])).
% 3.89/0.89  fof(f165,plain,(
% 3.89/0.89    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4),X4) | sK3(X3,X4) = X3 | r2_hidden(X3,X4)) )),
% 3.89/0.89    inference(superposition,[],[f83,f65])).
% 3.89/0.89  fof(f65,plain,(
% 3.89/0.89    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 3.89/0.89    inference(definition_unfolding,[],[f40,f58])).
% 3.89/0.89  fof(f40,plain,(
% 3.89/0.89    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 3.89/0.89    inference(cnf_transformation,[],[f18])).
% 3.89/0.89  fof(f179,plain,(
% 3.89/0.89    sK0 != sK3(sK0,k1_xboole_0) | spl6_11),
% 3.89/0.89    inference(avatar_component_clause,[],[f178])).
% 3.89/0.89  fof(f178,plain,(
% 3.89/0.89    spl6_11 <=> sK0 = sK3(sK0,k1_xboole_0)),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.89/0.89  fof(f593,plain,(
% 3.89/0.89    ~spl6_13),
% 3.89/0.89    inference(avatar_contradiction_clause,[],[f592])).
% 3.89/0.89  fof(f592,plain,(
% 3.89/0.89    $false | ~spl6_13),
% 3.89/0.89    inference(subsumption_resolution,[],[f288,f280])).
% 3.89/0.89  fof(f288,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl6_13),
% 3.89/0.89    inference(avatar_component_clause,[],[f286])).
% 3.89/0.89  fof(f286,plain,(
% 3.89/0.89    spl6_13 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 3.89/0.89  fof(f591,plain,(
% 3.89/0.89    spl6_28 | ~spl6_15),
% 3.89/0.89    inference(avatar_split_clause,[],[f461,f327,f469])).
% 3.89/0.89  fof(f461,plain,(
% 3.89/0.89    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_15),
% 3.89/0.89    inference(resolution,[],[f329,f84])).
% 3.89/0.89  fof(f84,plain,(
% 3.89/0.89    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 3.89/0.89    inference(equality_resolution,[],[f67])).
% 3.89/0.89  fof(f67,plain,(
% 3.89/0.89    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.89/0.89    inference(definition_unfolding,[],[f38,f58])).
% 3.89/0.89  fof(f38,plain,(
% 3.89/0.89    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.89/0.89    inference(cnf_transformation,[],[f18])).
% 3.89/0.89  fof(f329,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_15),
% 3.89/0.89    inference(avatar_component_clause,[],[f327])).
% 3.89/0.89  fof(f579,plain,(
% 3.89/0.89    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.89/0.89    introduced(theory_tautology_sat_conflict,[])).
% 3.89/0.89  fof(f578,plain,(
% 3.89/0.89    spl6_32 | spl6_33 | ~spl6_19),
% 3.89/0.89    inference(avatar_split_clause,[],[f566,f359,f575,f571])).
% 3.89/0.89  fof(f575,plain,(
% 3.89/0.89    spl6_33 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 3.89/0.89  fof(f566,plain,(
% 3.89/0.89    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_19),
% 3.89/0.89    inference(resolution,[],[f361,f92])).
% 3.89/0.89  fof(f519,plain,(
% 3.89/0.89    spl6_30 | ~spl6_17),
% 3.89/0.89    inference(avatar_split_clause,[],[f513,f344,f515])).
% 3.89/0.89  fof(f513,plain,(
% 3.89/0.89    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_17),
% 3.89/0.89    inference(duplicate_literal_removal,[],[f508])).
% 3.89/0.89  fof(f508,plain,(
% 3.89/0.89    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_17),
% 3.89/0.89    inference(resolution,[],[f346,f92])).
% 3.89/0.89  fof(f346,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_17),
% 3.89/0.89    inference(avatar_component_clause,[],[f344])).
% 3.89/0.89  fof(f460,plain,(
% 3.89/0.89    spl6_19 | spl6_1),
% 3.89/0.89    inference(avatar_split_clause,[],[f459,f94,f359])).
% 3.89/0.89  fof(f459,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 3.89/0.89    inference(duplicate_literal_removal,[],[f458])).
% 3.89/0.89  fof(f458,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 3.89/0.89    inference(equality_resolution,[],[f208])).
% 3.89/0.89  fof(f208,plain,(
% 3.89/0.89    ( ! [X30] : (k2_enumset1(sK0,sK0,sK0,sK1) != X30 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X30),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X30),X30)) ) | spl6_1),
% 3.89/0.89    inference(superposition,[],[f96,f72])).
% 3.89/0.89  fof(f72,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.89/0.89    inference(definition_unfolding,[],[f48,f37])).
% 3.89/0.89  fof(f48,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.89/0.89    inference(cnf_transformation,[],[f24])).
% 3.89/0.89  fof(f455,plain,(
% 3.89/0.89    spl6_17 | spl6_27 | spl6_2),
% 3.89/0.89    inference(avatar_split_clause,[],[f449,f99,f452,f344])).
% 3.89/0.89  fof(f449,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 3.89/0.89    inference(equality_resolution,[],[f207])).
% 3.89/0.89  fof(f207,plain,(
% 3.89/0.89    ( ! [X29] : (k2_enumset1(sK1,sK1,sK1,sK1) != X29 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X29),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X29),X29)) ) | spl6_2),
% 3.89/0.89    inference(superposition,[],[f101,f72])).
% 3.89/0.89  fof(f445,plain,(
% 3.89/0.89    spl6_15 | spl6_26 | spl6_3),
% 3.89/0.89    inference(avatar_split_clause,[],[f439,f104,f442,f327])).
% 3.89/0.89  fof(f439,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 3.89/0.89    inference(equality_resolution,[],[f206])).
% 3.89/0.89  fof(f206,plain,(
% 3.89/0.89    ( ! [X28] : (k2_enumset1(sK0,sK0,sK0,sK0) != X28 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X28),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X28),X28)) ) | spl6_3),
% 3.89/0.89    inference(superposition,[],[f106,f72])).
% 3.89/0.89  fof(f385,plain,(
% 3.89/0.89    spl6_22 | spl6_23 | ~spl6_21),
% 3.89/0.89    inference(avatar_split_clause,[],[f375,f371,f382,f378])).
% 3.89/0.89  fof(f378,plain,(
% 3.89/0.89    spl6_22 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 3.89/0.89  fof(f382,plain,(
% 3.89/0.89    spl6_23 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 3.89/0.89  fof(f371,plain,(
% 3.89/0.89    spl6_21 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 3.89/0.89  fof(f375,plain,(
% 3.89/0.89    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl6_21),
% 3.89/0.89    inference(resolution,[],[f373,f92])).
% 3.89/0.89  fof(f373,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_21),
% 3.89/0.89    inference(avatar_component_clause,[],[f371])).
% 3.89/0.89  fof(f374,plain,(
% 3.89/0.89    spl6_21 | spl6_4),
% 3.89/0.89    inference(avatar_split_clause,[],[f369,f109,f371])).
% 3.89/0.89  fof(f109,plain,(
% 3.89/0.89    spl6_4 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.89/0.89  fof(f369,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_4),
% 3.89/0.89    inference(subsumption_resolution,[],[f368,f280])).
% 3.89/0.89  fof(f368,plain,(
% 3.89/0.89    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_4),
% 3.89/0.89    inference(equality_resolution,[],[f209])).
% 3.89/0.89  fof(f209,plain,(
% 3.89/0.89    ( ! [X31] : (k1_xboole_0 != X31 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X31),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X31),X31)) ) | spl6_4),
% 3.89/0.89    inference(superposition,[],[f111,f72])).
% 3.89/0.89  fof(f111,plain,(
% 3.89/0.89    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl6_4),
% 3.89/0.89    inference(avatar_component_clause,[],[f109])).
% 3.89/0.89  fof(f351,plain,(
% 3.89/0.89    spl6_17 | ~spl6_18 | spl6_2),
% 3.89/0.89    inference(avatar_split_clause,[],[f341,f99,f348,f344])).
% 3.89/0.89  fof(f341,plain,(
% 3.89/0.89    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 3.89/0.89    inference(equality_resolution,[],[f192])).
% 3.89/0.89  fof(f192,plain,(
% 3.89/0.89    ( ! [X25] : (k2_enumset1(sK1,sK1,sK1,sK1) != X25 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X25),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X25),X25)) ) | spl6_2),
% 3.89/0.89    inference(superposition,[],[f101,f71])).
% 3.89/0.89  fof(f71,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.89/0.89    inference(definition_unfolding,[],[f49,f37])).
% 3.89/0.89  fof(f49,plain,(
% 3.89/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.89/0.89    inference(cnf_transformation,[],[f24])).
% 3.89/0.89  fof(f334,plain,(
% 3.89/0.89    spl6_15 | ~spl6_16 | spl6_3),
% 3.89/0.89    inference(avatar_split_clause,[],[f324,f104,f331,f327])).
% 3.89/0.89  fof(f324,plain,(
% 3.89/0.89    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 3.89/0.89    inference(equality_resolution,[],[f191])).
% 3.89/0.89  fof(f191,plain,(
% 3.89/0.89    ( ! [X24] : (k2_enumset1(sK0,sK0,sK0,sK0) != X24 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X24),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X24),X24)) ) | spl6_3),
% 3.89/0.89    inference(superposition,[],[f106,f71])).
% 3.89/0.89  fof(f293,plain,(
% 3.89/0.89    spl6_13 | ~spl6_14 | spl6_4),
% 3.89/0.89    inference(avatar_split_clause,[],[f284,f109,f290,f286])).
% 3.89/0.89  fof(f290,plain,(
% 3.89/0.89    spl6_14 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.89/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 3.89/0.89  fof(f284,plain,(
% 3.89/0.89    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_4),
% 3.89/0.89    inference(equality_resolution,[],[f194])).
% 3.89/0.89  fof(f194,plain,(
% 3.89/0.89    ( ! [X27] : (k1_xboole_0 != X27 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X27),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X27),X27)) ) | spl6_4),
% 3.89/0.89    inference(superposition,[],[f111,f71])).
% 3.89/0.89  fof(f112,plain,(
% 3.89/0.89    ~spl6_4),
% 3.89/0.89    inference(avatar_split_clause,[],[f62,f109])).
% 3.89/0.89  fof(f62,plain,(
% 3.89/0.89    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.89/0.89    inference(definition_unfolding,[],[f30,f37,f57])).
% 3.89/0.89  fof(f30,plain,(
% 3.89/0.89    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.89/0.89    inference(cnf_transformation,[],[f14])).
% 3.89/0.89  fof(f14,plain,(
% 3.89/0.89    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.89/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.89/0.89  fof(f13,plain,(
% 3.89/0.89    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 3.89/0.89    introduced(choice_axiom,[])).
% 3.89/0.89  fof(f12,plain,(
% 3.89/0.89    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 3.89/0.89    inference(ennf_transformation,[],[f11])).
% 3.89/0.89  fof(f11,negated_conjecture,(
% 3.89/0.89    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 3.89/0.89    inference(negated_conjecture,[],[f10])).
% 3.89/0.89  fof(f10,conjecture,(
% 3.89/0.89    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 3.89/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 3.89/0.89  fof(f107,plain,(
% 3.89/0.89    ~spl6_3),
% 3.89/0.89    inference(avatar_split_clause,[],[f61,f104])).
% 3.89/0.89  fof(f61,plain,(
% 3.89/0.89    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.89/0.89    inference(definition_unfolding,[],[f31,f37,f57,f58])).
% 3.89/0.89  fof(f31,plain,(
% 3.89/0.89    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 3.89/0.89    inference(cnf_transformation,[],[f14])).
% 3.89/0.89  fof(f102,plain,(
% 3.89/0.89    ~spl6_2),
% 3.89/0.89    inference(avatar_split_clause,[],[f60,f99])).
% 3.89/0.89  fof(f60,plain,(
% 3.89/0.89    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.89/0.89    inference(definition_unfolding,[],[f32,f37,f57,f58])).
% 3.89/0.89  fof(f32,plain,(
% 3.89/0.89    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 3.89/0.89    inference(cnf_transformation,[],[f14])).
% 3.89/0.89  fof(f97,plain,(
% 3.89/0.89    ~spl6_1),
% 3.89/0.89    inference(avatar_split_clause,[],[f59,f94])).
% 3.89/0.89  fof(f59,plain,(
% 3.89/0.89    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.89/0.89    inference(definition_unfolding,[],[f33,f57,f37,f57])).
% 3.89/0.89  fof(f33,plain,(
% 3.89/0.89    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.89/0.89    inference(cnf_transformation,[],[f14])).
% 3.89/0.89  % SZS output end Proof for theBenchmark
% 3.89/0.89  % (15293)------------------------------
% 3.89/0.89  % (15293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.89  % (15293)Termination reason: Refutation
% 3.89/0.89  
% 3.89/0.89  % (15293)Memory used [KB]: 11897
% 3.89/0.89  % (15293)Time elapsed: 0.280 s
% 3.89/0.89  % (15293)------------------------------
% 3.89/0.89  % (15293)------------------------------
% 3.89/0.89  % (15303)Refutation not found, incomplete strategy% (15303)------------------------------
% 3.89/0.89  % (15303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.89  % (15303)Termination reason: Refutation not found, incomplete strategy
% 3.89/0.89  
% 3.89/0.89  % (15303)Memory used [KB]: 10746
% 3.89/0.89  % (15303)Time elapsed: 0.140 s
% 3.89/0.89  % (15303)------------------------------
% 3.89/0.89  % (15303)------------------------------
% 3.89/0.89  % (15235)Success in time 0.52 s
%------------------------------------------------------------------------------
