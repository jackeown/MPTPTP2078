%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:20 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 298 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  413 (1273 expanded)
%              Number of equality atoms :   55 ( 213 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f726,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f106,f115,f189,f250,f262,f290,f446,f469,f538,f553,f681])).

fof(f681,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f123,f185])).

fof(f185,plain,
    ( ! [X3,X1] : ~ r2_hidden(X1,X3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_7
  <=> ! [X1,X3] : ~ r2_hidden(X1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f123,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f72,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f553,plain,
    ( spl6_1
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f550,f444,f187,f79])).

fof(f79,plain,
    ( spl6_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f187,plain,
    ( spl6_8
  <=> ! [X0,X2] :
        ( X0 = X2
        | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f444,plain,
    ( spl6_17
  <=> ! [X2] :
        ( ~ r2_hidden(sK2,X2)
        | r2_hidden(k1_mcart_1(sK0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f550,plain,
    ( sK2 = k1_mcart_1(sK0)
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(resolution,[],[f547,f188])).

fof(f188,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))
        | X0 = X2 )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f547,plain,
    ( ! [X1] : r2_hidden(k1_mcart_1(sK0),k2_enumset1(X1,X1,X1,sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f445,f120])).

fof(f120,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(resolution,[],[f71,f73])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f445,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,X2)
        | r2_hidden(k1_mcart_1(sK0),X2) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f444])).

fof(f538,plain,
    ( spl6_3
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f535,f285,f187,f86])).

fof(f86,plain,
    ( spl6_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f285,plain,
    ( spl6_12
  <=> ! [X5] :
        ( r2_hidden(k1_mcart_1(sK0),X5)
        | ~ r2_hidden(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f535,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f511,f188])).

fof(f511,plain,
    ( ! [X0] : r2_hidden(k1_mcart_1(sK0),k2_enumset1(X0,X0,X0,sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f286,f120])).

fof(f286,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK1,X5)
        | r2_hidden(k1_mcart_1(sK0),X5) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f285])).

fof(f469,plain,
    ( ~ spl6_5
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f105,f442])).

fof(f442,plain,
    ( ! [X3] : ~ r2_hidden(k1_mcart_1(sK0),X3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl6_16
  <=> ! [X3] : ~ r2_hidden(k1_mcart_1(sK0),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f105,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_5
  <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f446,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f439,f288,f444,f441])).

fof(f288,plain,
    ( spl6_13
  <=> ! [X4] :
        ( r2_hidden(sK2,X4)
        | ~ r2_hidden(k1_mcart_1(sK0),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f439,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK2,X2)
        | r2_hidden(k1_mcart_1(sK0),X2)
        | ~ r2_hidden(k1_mcart_1(sK0),X3) )
    | ~ spl6_13 ),
    inference(resolution,[],[f431,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f431,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X5,X6))
        | ~ r2_hidden(sK2,X6) )
    | ~ spl6_13 ),
    inference(resolution,[],[f289,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f289,plain,
    ( ! [X4] :
        ( r2_hidden(sK2,X4)
        | ~ r2_hidden(k1_mcart_1(sK0),X4) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f282,f248,f288,f285])).

fof(f248,plain,
    ( spl6_11
  <=> ! [X2] :
        ( r2_hidden(sK2,X2)
        | ~ r2_hidden(k1_mcart_1(sK0),X2)
        | r2_hidden(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f282,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK2,X4)
        | r2_hidden(k1_mcart_1(sK0),X5)
        | ~ r2_hidden(k1_mcart_1(sK0),X4)
        | ~ r2_hidden(sK1,X5) )
    | ~ spl6_11 ),
    inference(resolution,[],[f275,f76])).

fof(f275,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK1,k4_xboole_0(X2,X3))
        | r2_hidden(sK2,X2)
        | r2_hidden(k1_mcart_1(sK0),X3)
        | ~ r2_hidden(k1_mcart_1(sK0),X2) )
    | ~ spl6_11 ),
    inference(resolution,[],[f264,f75])).

fof(f264,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X1,X2))
        | r2_hidden(sK1,k4_xboole_0(X1,X2))
        | r2_hidden(sK2,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f249,f77])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f249,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,X2)
        | ~ r2_hidden(k1_mcart_1(sK0),X2)
        | r2_hidden(sK1,X2) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f248])).

fof(f262,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl6_10 ),
    inference(resolution,[],[f258,f123])).

fof(f258,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK2))
    | ~ spl6_10 ),
    inference(resolution,[],[f246,f120])).

fof(f246,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl6_10
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f250,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f242,f104,f248,f245])).

fof(f242,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK2,X2)
        | ~ r2_hidden(sK2,X3)
        | r2_hidden(sK1,X2)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(k1_mcart_1(sK0),X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f228,f76])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X0,X1))
        | r2_hidden(sK2,X1)
        | ~ r2_hidden(sK2,X0)
        | r2_hidden(sK1,X1)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f225,f75])).

fof(f225,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK1,k4_xboole_0(X2,X3))
        | r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X2,X3))
        | r2_hidden(sK2,X3)
        | ~ r2_hidden(sK2,X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f218,f75])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ r2_hidden(sK1,X0)
        | r2_hidden(k1_mcart_1(sK0),X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),X0)
        | r2_hidden(k1_mcart_1(sK0),X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f105,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f189,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f182,f187,f184])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(forward_demodulation,[],[f180,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f115,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f112,f90,f82])).

fof(f82,plain,
    ( spl6_2
  <=> r2_hidden(k2_mcart_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f112,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f50,f91])).

fof(f91,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f106,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f101,f90,f104])).

fof(f101,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl6_4 ),
    inference(resolution,[],[f49,f91])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f67,f90])).

fof(f67,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f35,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f88,plain,
    ( ~ spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f36,f82,f86])).

fof(f36,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f37,f82,f79])).

fof(f37,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3697)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (3682)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (3689)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (3686)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (3705)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.52  % (3683)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (3681)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.52  % (3681)Refutation not found, incomplete strategy% (3681)------------------------------
% 1.25/0.52  % (3681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3681)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3681)Memory used [KB]: 1663
% 1.25/0.52  % (3681)Time elapsed: 0.102 s
% 1.25/0.52  % (3681)------------------------------
% 1.25/0.52  % (3681)------------------------------
% 1.25/0.52  % (3698)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.52  % (3698)Refutation not found, incomplete strategy% (3698)------------------------------
% 1.25/0.52  % (3698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3710)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.52  % (3693)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.52  % (3685)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (3690)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (3698)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3698)Memory used [KB]: 10618
% 1.25/0.52  % (3698)Time elapsed: 0.117 s
% 1.25/0.52  % (3698)------------------------------
% 1.25/0.52  % (3698)------------------------------
% 1.25/0.52  % (3703)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (3684)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.52  % (3695)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (3699)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.53  % (3687)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (3708)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (3707)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.53  % (3690)Refutation not found, incomplete strategy% (3690)------------------------------
% 1.41/0.53  % (3690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.53  % (3690)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.53  
% 1.41/0.53  % (3690)Memory used [KB]: 10618
% 1.41/0.53  % (3690)Time elapsed: 0.124 s
% 1.41/0.53  % (3690)------------------------------
% 1.41/0.53  % (3690)------------------------------
% 1.41/0.53  % (3696)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (3691)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (3709)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (3703)Refutation not found, incomplete strategy% (3703)------------------------------
% 1.41/0.54  % (3703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3703)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3703)Memory used [KB]: 10746
% 1.41/0.54  % (3703)Time elapsed: 0.094 s
% 1.41/0.54  % (3703)------------------------------
% 1.41/0.54  % (3703)------------------------------
% 1.41/0.54  % (3691)Refutation not found, incomplete strategy% (3691)------------------------------
% 1.41/0.54  % (3691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3691)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3691)Memory used [KB]: 10618
% 1.41/0.54  % (3691)Time elapsed: 0.128 s
% 1.41/0.54  % (3691)------------------------------
% 1.41/0.54  % (3691)------------------------------
% 1.41/0.54  % (3700)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % (3701)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (3701)Refutation not found, incomplete strategy% (3701)------------------------------
% 1.41/0.54  % (3701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3701)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3701)Memory used [KB]: 10746
% 1.41/0.54  % (3701)Time elapsed: 0.138 s
% 1.41/0.54  % (3701)------------------------------
% 1.41/0.54  % (3701)------------------------------
% 1.41/0.54  % (3702)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.54  % (3702)Refutation not found, incomplete strategy% (3702)------------------------------
% 1.41/0.54  % (3702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3702)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3702)Memory used [KB]: 1663
% 1.41/0.54  % (3702)Time elapsed: 0.139 s
% 1.41/0.54  % (3702)------------------------------
% 1.41/0.54  % (3702)------------------------------
% 1.41/0.54  % (3692)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (3694)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.54  % (3692)Refutation not found, incomplete strategy% (3692)------------------------------
% 1.41/0.54  % (3692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3692)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3692)Memory used [KB]: 10618
% 1.41/0.54  % (3692)Time elapsed: 0.138 s
% 1.41/0.54  % (3692)------------------------------
% 1.41/0.54  % (3692)------------------------------
% 1.41/0.55  % (3688)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (3706)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (3704)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.60  % (3700)Refutation found. Thanks to Tanya!
% 1.41/0.60  % SZS status Theorem for theBenchmark
% 1.41/0.61  % SZS output start Proof for theBenchmark
% 1.41/0.61  fof(f726,plain,(
% 1.41/0.61    $false),
% 1.41/0.61    inference(avatar_sat_refutation,[],[f84,f88,f92,f106,f115,f189,f250,f262,f290,f446,f469,f538,f553,f681])).
% 1.41/0.61  fof(f681,plain,(
% 1.41/0.61    ~spl6_7),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f565])).
% 1.41/0.61  fof(f565,plain,(
% 1.41/0.61    $false | ~spl6_7),
% 1.41/0.61    inference(subsumption_resolution,[],[f123,f185])).
% 1.41/0.61  fof(f185,plain,(
% 1.41/0.61    ( ! [X3,X1] : (~r2_hidden(X1,X3)) ) | ~spl6_7),
% 1.41/0.61    inference(avatar_component_clause,[],[f184])).
% 1.41/0.61  fof(f184,plain,(
% 1.41/0.61    spl6_7 <=> ! [X1,X3] : ~r2_hidden(X1,X3)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.41/0.61  fof(f123,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.41/0.61    inference(resolution,[],[f72,f73])).
% 1.41/0.61  fof(f73,plain,(
% 1.41/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.61    inference(equality_resolution,[],[f43])).
% 1.41/0.61  fof(f43,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.61    inference(cnf_transformation,[],[f21])).
% 1.41/0.61  fof(f21,plain,(
% 1.41/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.61    inference(flattening,[],[f20])).
% 1.41/0.61  fof(f20,plain,(
% 1.41/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.61    inference(nnf_transformation,[],[f3])).
% 1.41/0.61  fof(f3,axiom,(
% 1.41/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.61  fof(f72,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f59,f65])).
% 1.41/0.61  fof(f65,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f39,f48])).
% 1.41/0.61  fof(f48,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f6])).
% 1.41/0.61  fof(f6,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.61  fof(f39,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f5])).
% 1.41/0.61  fof(f5,axiom,(
% 1.41/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.61  fof(f59,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f32])).
% 1.41/0.61  fof(f32,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.41/0.61    inference(flattening,[],[f31])).
% 1.41/0.61  fof(f31,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.41/0.61    inference(nnf_transformation,[],[f8])).
% 1.41/0.61  fof(f8,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.41/0.61  fof(f553,plain,(
% 1.41/0.61    spl6_1 | ~spl6_8 | ~spl6_17),
% 1.41/0.61    inference(avatar_split_clause,[],[f550,f444,f187,f79])).
% 1.41/0.61  fof(f79,plain,(
% 1.41/0.61    spl6_1 <=> sK2 = k1_mcart_1(sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.61  fof(f187,plain,(
% 1.41/0.61    spl6_8 <=> ! [X0,X2] : (X0 = X2 | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.41/0.61  fof(f444,plain,(
% 1.41/0.61    spl6_17 <=> ! [X2] : (~r2_hidden(sK2,X2) | r2_hidden(k1_mcart_1(sK0),X2))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.41/0.61  fof(f550,plain,(
% 1.41/0.61    sK2 = k1_mcart_1(sK0) | (~spl6_8 | ~spl6_17)),
% 1.41/0.61    inference(resolution,[],[f547,f188])).
% 1.41/0.61  fof(f188,plain,(
% 1.41/0.61    ( ! [X2,X0] : (~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) | X0 = X2) ) | ~spl6_8),
% 1.41/0.61    inference(avatar_component_clause,[],[f187])).
% 1.41/0.61  fof(f547,plain,(
% 1.41/0.61    ( ! [X1] : (r2_hidden(k1_mcart_1(sK0),k2_enumset1(X1,X1,X1,sK2))) ) | ~spl6_17),
% 1.41/0.61    inference(resolution,[],[f445,f120])).
% 1.41/0.61  fof(f120,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 1.41/0.61    inference(resolution,[],[f71,f73])).
% 1.41/0.61  fof(f71,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f60,f65])).
% 1.41/0.61  fof(f60,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f32])).
% 1.41/0.61  fof(f445,plain,(
% 1.41/0.61    ( ! [X2] : (~r2_hidden(sK2,X2) | r2_hidden(k1_mcart_1(sK0),X2)) ) | ~spl6_17),
% 1.41/0.61    inference(avatar_component_clause,[],[f444])).
% 1.41/0.61  fof(f538,plain,(
% 1.41/0.61    spl6_3 | ~spl6_8 | ~spl6_12),
% 1.41/0.61    inference(avatar_split_clause,[],[f535,f285,f187,f86])).
% 1.41/0.61  fof(f86,plain,(
% 1.41/0.61    spl6_3 <=> sK1 = k1_mcart_1(sK0)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.61  fof(f285,plain,(
% 1.41/0.61    spl6_12 <=> ! [X5] : (r2_hidden(k1_mcart_1(sK0),X5) | ~r2_hidden(sK1,X5))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.41/0.61  fof(f535,plain,(
% 1.41/0.61    sK1 = k1_mcart_1(sK0) | (~spl6_8 | ~spl6_12)),
% 1.41/0.61    inference(resolution,[],[f511,f188])).
% 1.41/0.61  fof(f511,plain,(
% 1.41/0.61    ( ! [X0] : (r2_hidden(k1_mcart_1(sK0),k2_enumset1(X0,X0,X0,sK1))) ) | ~spl6_12),
% 1.41/0.61    inference(resolution,[],[f286,f120])).
% 1.41/0.61  fof(f286,plain,(
% 1.41/0.61    ( ! [X5] : (~r2_hidden(sK1,X5) | r2_hidden(k1_mcart_1(sK0),X5)) ) | ~spl6_12),
% 1.41/0.61    inference(avatar_component_clause,[],[f285])).
% 1.41/0.61  fof(f469,plain,(
% 1.41/0.61    ~spl6_5 | ~spl6_16),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f463])).
% 1.41/0.61  fof(f463,plain,(
% 1.41/0.61    $false | (~spl6_5 | ~spl6_16)),
% 1.41/0.61    inference(subsumption_resolution,[],[f105,f442])).
% 1.41/0.61  fof(f442,plain,(
% 1.41/0.61    ( ! [X3] : (~r2_hidden(k1_mcart_1(sK0),X3)) ) | ~spl6_16),
% 1.41/0.61    inference(avatar_component_clause,[],[f441])).
% 1.41/0.61  fof(f441,plain,(
% 1.41/0.61    spl6_16 <=> ! [X3] : ~r2_hidden(k1_mcart_1(sK0),X3)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.41/0.61  fof(f105,plain,(
% 1.41/0.61    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl6_5),
% 1.41/0.61    inference(avatar_component_clause,[],[f104])).
% 1.41/0.61  fof(f104,plain,(
% 1.41/0.61    spl6_5 <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.41/0.61  fof(f446,plain,(
% 1.41/0.61    spl6_16 | spl6_17 | ~spl6_13),
% 1.41/0.61    inference(avatar_split_clause,[],[f439,f288,f444,f441])).
% 1.41/0.61  fof(f288,plain,(
% 1.41/0.61    spl6_13 <=> ! [X4] : (r2_hidden(sK2,X4) | ~r2_hidden(k1_mcart_1(sK0),X4))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.41/0.61  fof(f439,plain,(
% 1.41/0.61    ( ! [X2,X3] : (~r2_hidden(sK2,X2) | r2_hidden(k1_mcart_1(sK0),X2) | ~r2_hidden(k1_mcart_1(sK0),X3)) ) | ~spl6_13),
% 1.41/0.61    inference(resolution,[],[f431,f75])).
% 1.41/0.61  fof(f75,plain,(
% 1.41/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.41/0.61    inference(equality_resolution,[],[f55])).
% 1.41/0.61  fof(f55,plain,(
% 1.41/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.61    inference(cnf_transformation,[],[f30])).
% 1.41/0.61  fof(f30,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 1.41/0.61  fof(f29,plain,(
% 1.41/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f28,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.61    inference(rectify,[],[f27])).
% 1.41/0.61  fof(f27,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.61    inference(flattening,[],[f26])).
% 1.41/0.61  fof(f26,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.61    inference(nnf_transformation,[],[f2])).
% 1.41/0.61  fof(f2,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.61  fof(f431,plain,(
% 1.41/0.61    ( ! [X6,X5] : (~r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X5,X6)) | ~r2_hidden(sK2,X6)) ) | ~spl6_13),
% 1.41/0.61    inference(resolution,[],[f289,f76])).
% 1.41/0.61  fof(f76,plain,(
% 1.41/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.41/0.61    inference(equality_resolution,[],[f54])).
% 1.41/0.61  fof(f54,plain,(
% 1.41/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.61    inference(cnf_transformation,[],[f30])).
% 1.41/0.61  fof(f289,plain,(
% 1.41/0.61    ( ! [X4] : (r2_hidden(sK2,X4) | ~r2_hidden(k1_mcart_1(sK0),X4)) ) | ~spl6_13),
% 1.41/0.61    inference(avatar_component_clause,[],[f288])).
% 1.41/0.61  fof(f290,plain,(
% 1.41/0.61    spl6_12 | spl6_13 | ~spl6_11),
% 1.41/0.61    inference(avatar_split_clause,[],[f282,f248,f288,f285])).
% 1.41/0.61  fof(f248,plain,(
% 1.41/0.61    spl6_11 <=> ! [X2] : (r2_hidden(sK2,X2) | ~r2_hidden(k1_mcart_1(sK0),X2) | r2_hidden(sK1,X2))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.41/0.61  fof(f282,plain,(
% 1.41/0.61    ( ! [X4,X5] : (r2_hidden(sK2,X4) | r2_hidden(k1_mcart_1(sK0),X5) | ~r2_hidden(k1_mcart_1(sK0),X4) | ~r2_hidden(sK1,X5)) ) | ~spl6_11),
% 1.41/0.61    inference(resolution,[],[f275,f76])).
% 1.41/0.61  fof(f275,plain,(
% 1.41/0.61    ( ! [X2,X3] : (r2_hidden(sK1,k4_xboole_0(X2,X3)) | r2_hidden(sK2,X2) | r2_hidden(k1_mcart_1(sK0),X3) | ~r2_hidden(k1_mcart_1(sK0),X2)) ) | ~spl6_11),
% 1.41/0.61    inference(resolution,[],[f264,f75])).
% 1.41/0.61  fof(f264,plain,(
% 1.41/0.61    ( ! [X2,X1] : (~r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X1,X2)) | r2_hidden(sK1,k4_xboole_0(X1,X2)) | r2_hidden(sK2,X1)) ) | ~spl6_11),
% 1.41/0.61    inference(resolution,[],[f249,f77])).
% 1.41/0.61  fof(f77,plain,(
% 1.41/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.41/0.61    inference(equality_resolution,[],[f53])).
% 1.41/0.61  fof(f53,plain,(
% 1.41/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.61    inference(cnf_transformation,[],[f30])).
% 1.41/0.61  fof(f249,plain,(
% 1.41/0.61    ( ! [X2] : (r2_hidden(sK2,X2) | ~r2_hidden(k1_mcart_1(sK0),X2) | r2_hidden(sK1,X2)) ) | ~spl6_11),
% 1.41/0.61    inference(avatar_component_clause,[],[f248])).
% 1.41/0.61  fof(f262,plain,(
% 1.41/0.61    ~spl6_10),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f261])).
% 1.41/0.61  fof(f261,plain,(
% 1.41/0.61    $false | ~spl6_10),
% 1.41/0.61    inference(resolution,[],[f258,f123])).
% 1.41/0.61  fof(f258,plain,(
% 1.41/0.61    ( ! [X0] : (~r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK2))) ) | ~spl6_10),
% 1.41/0.61    inference(resolution,[],[f246,f120])).
% 1.41/0.61  fof(f246,plain,(
% 1.41/0.61    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3)) ) | ~spl6_10),
% 1.41/0.61    inference(avatar_component_clause,[],[f245])).
% 1.41/0.61  fof(f245,plain,(
% 1.41/0.61    spl6_10 <=> ! [X3] : (~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.41/0.61  fof(f250,plain,(
% 1.41/0.61    spl6_10 | spl6_11 | ~spl6_5),
% 1.41/0.61    inference(avatar_split_clause,[],[f242,f104,f248,f245])).
% 1.41/0.61  fof(f242,plain,(
% 1.41/0.61    ( ! [X2,X3] : (r2_hidden(sK2,X2) | ~r2_hidden(sK2,X3) | r2_hidden(sK1,X2) | ~r2_hidden(sK1,X3) | ~r2_hidden(k1_mcart_1(sK0),X2)) ) | ~spl6_5),
% 1.41/0.61    inference(resolution,[],[f228,f76])).
% 1.41/0.61  fof(f228,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X0,X1)) | r2_hidden(sK2,X1) | ~r2_hidden(sK2,X0) | r2_hidden(sK1,X1) | ~r2_hidden(sK1,X0)) ) | ~spl6_5),
% 1.41/0.61    inference(resolution,[],[f225,f75])).
% 1.41/0.61  fof(f225,plain,(
% 1.41/0.61    ( ! [X2,X3] : (~r2_hidden(sK1,k4_xboole_0(X2,X3)) | r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X2,X3)) | r2_hidden(sK2,X3) | ~r2_hidden(sK2,X2)) ) | ~spl6_5),
% 1.41/0.61    inference(resolution,[],[f218,f75])).
% 1.41/0.61  fof(f218,plain,(
% 1.41/0.61    ( ! [X0] : (~r2_hidden(sK2,X0) | ~r2_hidden(sK1,X0) | r2_hidden(k1_mcart_1(sK0),X0)) ) | ~spl6_5),
% 1.41/0.61    inference(resolution,[],[f70,f107])).
% 1.41/0.61  fof(f107,plain,(
% 1.41/0.61    ( ! [X0] : (~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),X0) | r2_hidden(k1_mcart_1(sK0),X0)) ) | ~spl6_5),
% 1.41/0.61    inference(resolution,[],[f105,f45])).
% 1.41/0.61  fof(f45,plain,(
% 1.41/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f25])).
% 1.41/0.61  fof(f25,plain,(
% 1.41/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.41/0.61  fof(f24,plain,(
% 1.41/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f23,plain,(
% 1.41/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.61    inference(rectify,[],[f22])).
% 1.41/0.61  fof(f22,plain,(
% 1.41/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.61    inference(nnf_transformation,[],[f15])).
% 1.41/0.61  fof(f15,plain,(
% 1.41/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.61    inference(ennf_transformation,[],[f1])).
% 1.41/0.61  fof(f1,axiom,(
% 1.41/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.61  fof(f70,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f61,f65])).
% 1.41/0.61  fof(f61,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f32])).
% 1.41/0.61  fof(f189,plain,(
% 1.41/0.61    spl6_7 | spl6_8),
% 1.41/0.61    inference(avatar_split_clause,[],[f182,f187,f184])).
% 1.41/0.61  fof(f182,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.41/0.61    inference(forward_demodulation,[],[f180,f40])).
% 1.41/0.61  fof(f40,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.41/0.61    inference(cnf_transformation,[],[f11])).
% 1.41/0.61  fof(f11,axiom,(
% 1.41/0.61    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.41/0.61  fof(f180,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.41/0.61    inference(resolution,[],[f69,f64])).
% 1.41/0.61  fof(f64,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f34])).
% 1.41/0.61  fof(f34,plain,(
% 1.41/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.41/0.61    inference(flattening,[],[f33])).
% 1.41/0.61  fof(f33,plain,(
% 1.41/0.61    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.41/0.61    inference(nnf_transformation,[],[f7])).
% 1.41/0.61  fof(f7,axiom,(
% 1.41/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.41/0.61  fof(f69,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.41/0.61    inference(definition_unfolding,[],[f51,f66])).
% 1.41/0.61  fof(f66,plain,(
% 1.41/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f38,f65])).
% 1.41/0.61  fof(f38,plain,(
% 1.41/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f4])).
% 1.41/0.61  fof(f4,axiom,(
% 1.41/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.61  fof(f51,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f17])).
% 1.41/0.61  fof(f17,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.41/0.61    inference(ennf_transformation,[],[f10])).
% 1.41/0.61  fof(f10,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.41/0.61  fof(f115,plain,(
% 1.41/0.61    spl6_2 | ~spl6_4),
% 1.41/0.61    inference(avatar_split_clause,[],[f112,f90,f82])).
% 1.41/0.61  fof(f82,plain,(
% 1.41/0.61    spl6_2 <=> r2_hidden(k2_mcart_1(sK0),sK3)),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.61  fof(f90,plain,(
% 1.41/0.61    spl6_4 <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.41/0.61  fof(f112,plain,(
% 1.41/0.61    r2_hidden(k2_mcart_1(sK0),sK3) | ~spl6_4),
% 1.41/0.61    inference(resolution,[],[f50,f91])).
% 1.41/0.61  fof(f91,plain,(
% 1.41/0.61    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) | ~spl6_4),
% 1.41/0.61    inference(avatar_component_clause,[],[f90])).
% 1.41/0.61  fof(f50,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f16])).
% 1.41/0.61  fof(f16,plain,(
% 1.41/0.61    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.41/0.61    inference(ennf_transformation,[],[f9])).
% 1.41/0.61  fof(f9,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.41/0.61  fof(f106,plain,(
% 1.41/0.61    spl6_5 | ~spl6_4),
% 1.41/0.61    inference(avatar_split_clause,[],[f101,f90,f104])).
% 1.41/0.61  fof(f101,plain,(
% 1.41/0.61    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl6_4),
% 1.41/0.61    inference(resolution,[],[f49,f91])).
% 1.41/0.61  fof(f49,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f16])).
% 1.41/0.61  fof(f92,plain,(
% 1.41/0.61    spl6_4),
% 1.41/0.61    inference(avatar_split_clause,[],[f67,f90])).
% 1.41/0.61  fof(f67,plain,(
% 1.41/0.61    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))),
% 1.41/0.61    inference(definition_unfolding,[],[f35,f65])).
% 1.41/0.61  fof(f35,plain,(
% 1.41/0.61    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 1.41/0.61    inference(cnf_transformation,[],[f19])).
% 1.41/0.61  fof(f19,plain,(
% 1.41/0.61    (~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 1.41/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).
% 1.41/0.61  fof(f18,plain,(
% 1.41/0.61    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f14,plain,(
% 1.41/0.61    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 1.41/0.61    inference(ennf_transformation,[],[f13])).
% 1.41/0.61  fof(f13,negated_conjecture,(
% 1.41/0.61    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.41/0.61    inference(negated_conjecture,[],[f12])).
% 1.41/0.61  fof(f12,conjecture,(
% 1.41/0.61    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 1.41/0.61  fof(f88,plain,(
% 1.41/0.61    ~spl6_3 | ~spl6_2),
% 1.41/0.61    inference(avatar_split_clause,[],[f36,f82,f86])).
% 1.41/0.61  fof(f36,plain,(
% 1.41/0.61    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f19])).
% 1.41/0.61  fof(f84,plain,(
% 1.41/0.61    ~spl6_1 | ~spl6_2),
% 1.41/0.61    inference(avatar_split_clause,[],[f37,f82,f79])).
% 1.41/0.61  fof(f37,plain,(
% 1.41/0.61    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 1.41/0.61    inference(cnf_transformation,[],[f19])).
% 1.41/0.61  % SZS output end Proof for theBenchmark
% 1.41/0.61  % (3700)------------------------------
% 1.41/0.61  % (3700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.61  % (3700)Termination reason: Refutation
% 1.41/0.61  
% 1.41/0.61  % (3700)Memory used [KB]: 11129
% 1.41/0.61  % (3700)Time elapsed: 0.184 s
% 1.41/0.61  % (3700)------------------------------
% 1.41/0.61  % (3700)------------------------------
% 1.41/0.61  % (3680)Success in time 0.258 s
%------------------------------------------------------------------------------
