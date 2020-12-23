%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 332 expanded)
%              Number of leaves         :   27 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  341 ( 806 expanded)
%              Number of equality atoms :  162 ( 512 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f936,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f183,f199,f200,f207,f213,f253,f264,f345,f888,f923,f931,f935])).

fof(f935,plain,
    ( ~ spl5_2
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f133,f922])).

fof(f922,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f133,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_2
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f931,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f91,f887])).

fof(f887,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f886])).

fof(f886,plain,
    ( spl5_16
  <=> ! [X0] : ~ r2_hidden(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f91,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f923,plain,
    ( spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f896,f882,f920])).

fof(f882,plain,
    ( spl5_15
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f896,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f95,f884])).

fof(f884,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f882])).

fof(f95,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f888,plain,
    ( spl5_15
    | spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f880,f250,f886,f882])).

fof(f250,plain,
    ( spl5_10
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f880,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) )
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f871])).

fof(f871,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f227,f306])).

fof(f306,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f289,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(forward_demodulation,[],[f103,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f97,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f97,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f72,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f289,plain,
    ( ! [X0] :
        ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_10 ),
    inference(superposition,[],[f237,f252])).

fof(f252,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f250])).

fof(f237,plain,(
    ! [X15,X16] :
      ( r1_xboole_0(k5_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X16,X16,X16,X16)),X15)
      | ~ r2_hidden(X16,X15) ) ),
    inference(superposition,[],[f97,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f69,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f227,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,k2_enumset1(X5,X5,X5,X5))
      | ~ r2_hidden(X5,X4)
      | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5) ) ),
    inference(superposition,[],[f77,f53])).

fof(f345,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f110,f130])).

fof(f130,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_1
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f110,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(resolution,[],[f107,f97])).

fof(f264,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f91,f248])).

fof(f248,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl5_9
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f253,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f244,f210,f250,f246])).

fof(f210,plain,
    ( spl5_7
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f244,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_7 ),
    inference(superposition,[],[f212,f77])).

fof(f212,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f213,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f208,f180,f176,f210])).

fof(f176,plain,
    ( spl5_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f180,plain,
    ( spl5_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f208,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f177,f182])).

fof(f182,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f180])).

fof(f177,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f207,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl5_4
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f181,f198,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f50,f69,f69])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f198,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_6
  <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f181,plain,
    ( sK0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f180])).

fof(f200,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f71,f180,f176])).

fof(f71,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f41,f69,f43,f69,f69])).

fof(f41,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f199,plain,
    ( ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f187,f176,f196])).

fof(f187,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(forward_demodulation,[],[f184,f52])).

fof(f184,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(superposition,[],[f178,f101])).

fof(f101,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f53,f57])).

fof(f178,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f183,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f70,f180,f176])).

fof(f70,plain,
    ( sK0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f42,f69,f43,f69,f69])).

fof(f42,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f127,f132,f129])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f56,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (4881)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.44  % (4881)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f936,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f134,f183,f199,f200,f207,f213,f253,f264,f345,f888,f923,f931,f935])).
% 0.20/0.44  fof(f935,plain,(
% 0.20/0.44    ~spl5_2 | ~spl5_17),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f932])).
% 0.20/0.44  fof(f932,plain,(
% 0.20/0.44    $false | (~spl5_2 | ~spl5_17)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f133,f922])).
% 0.20/0.44  fof(f922,plain,(
% 0.20/0.44    r2_hidden(sK0,k1_xboole_0) | ~spl5_17),
% 0.20/0.44    inference(avatar_component_clause,[],[f920])).
% 0.20/0.44  fof(f920,plain,(
% 0.20/0.44    spl5_17 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl5_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f132])).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    spl5_2 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.44  fof(f931,plain,(
% 0.20/0.44    ~spl5_16),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f924])).
% 0.20/0.44  fof(f924,plain,(
% 0.20/0.44    $false | ~spl5_16),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f91,f887])).
% 0.20/0.44  fof(f887,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | ~spl5_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f886])).
% 0.20/0.44  fof(f886,plain,(
% 0.20/0.44    spl5_16 <=> ! [X0] : ~r2_hidden(sK0,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 0.20/0.44    inference(equality_resolution,[],[f90])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 0.20/0.44    inference(equality_resolution,[],[f83])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.44    inference(definition_unfolding,[],[f61,f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.44    inference(cnf_transformation,[],[f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.44    inference(rectify,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.44    inference(flattening,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.44    inference(nnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.44  fof(f923,plain,(
% 0.20/0.44    spl5_17 | ~spl5_15),
% 0.20/0.44    inference(avatar_split_clause,[],[f896,f882,f920])).
% 0.20/0.44  fof(f882,plain,(
% 0.20/0.44    spl5_15 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.44  fof(f896,plain,(
% 0.20/0.44    r2_hidden(sK0,k1_xboole_0) | ~spl5_15),
% 0.20/0.44    inference(superposition,[],[f95,f884])).
% 0.20/0.44  fof(f884,plain,(
% 0.20/0.44    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_15),
% 0.20/0.44    inference(avatar_component_clause,[],[f882])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 0.20/0.44    inference(equality_resolution,[],[f94])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 0.20/0.44    inference(equality_resolution,[],[f85])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.44    inference(definition_unfolding,[],[f59,f67])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.44    inference(cnf_transformation,[],[f40])).
% 0.20/0.44  fof(f888,plain,(
% 0.20/0.44    spl5_15 | spl5_16 | ~spl5_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f880,f250,f886,f882])).
% 0.20/0.44  fof(f250,plain,(
% 0.20/0.44    spl5_10 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.44  fof(f880,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK0,X0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)) ) | ~spl5_10),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f871])).
% 0.20/0.44  fof(f871,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK0,X0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,X0)) ) | ~spl5_10),
% 0.20/0.44    inference(resolution,[],[f227,f306])).
% 0.20/0.44  fof(f306,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,X0)) ) | ~spl5_10),
% 0.20/0.44    inference(resolution,[],[f289,f107])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f103,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(superposition,[],[f97,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) )),
% 0.20/0.44    inference(superposition,[],[f72,f57])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f44,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.44  fof(f289,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) | ~r2_hidden(sK0,X0)) ) | ~spl5_10),
% 0.20/0.44    inference(superposition,[],[f237,f252])).
% 0.20/0.44  fof(f252,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f250])).
% 0.20/0.44  fof(f237,plain,(
% 0.20/0.44    ( ! [X15,X16] : (r1_xboole_0(k5_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X16,X16,X16,X16)),X15) | ~r2_hidden(X16,X15)) )),
% 0.20/0.44    inference(superposition,[],[f97,f77])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f49,f69,f69])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f51,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f66,f67])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,axiom,(
% 0.20/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.20/0.44  fof(f227,plain,(
% 0.20/0.44    ( ! [X4,X5] : (~r1_xboole_0(X4,k2_enumset1(X5,X5,X5,X5)) | ~r2_hidden(X5,X4) | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5)) )),
% 0.20/0.44    inference(superposition,[],[f77,f53])).
% 0.20/0.44  fof(f345,plain,(
% 0.20/0.44    ~spl5_1),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f337])).
% 0.20/0.44  fof(f337,plain,(
% 0.20/0.44    $false | ~spl5_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f110,f130])).
% 0.20/0.44  fof(f130,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl5_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f129])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl5_1 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X2,X3] : (r1_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 0.20/0.44    inference(resolution,[],[f107,f97])).
% 0.20/0.44  fof(f264,plain,(
% 0.20/0.44    spl5_9),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f257])).
% 0.20/0.44  fof(f257,plain,(
% 0.20/0.44    $false | spl5_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f91,f248])).
% 0.20/0.44  fof(f248,plain,(
% 0.20/0.44    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f246])).
% 0.20/0.44  fof(f246,plain,(
% 0.20/0.44    spl5_9 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.44  fof(f253,plain,(
% 0.20/0.44    ~spl5_9 | spl5_10 | ~spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f244,f210,f250,f246])).
% 0.20/0.44  fof(f210,plain,(
% 0.20/0.44    spl5_7 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.44  fof(f244,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_7),
% 0.20/0.44    inference(superposition,[],[f212,f77])).
% 0.20/0.44  fof(f212,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f210])).
% 0.20/0.44  fof(f213,plain,(
% 0.20/0.44    spl5_7 | ~spl5_3 | ~spl5_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f208,f180,f176,f210])).
% 0.20/0.44  fof(f176,plain,(
% 0.20/0.44    spl5_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.44  fof(f180,plain,(
% 0.20/0.44    spl5_4 <=> sK0 = sK1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.44  fof(f208,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) | (~spl5_3 | ~spl5_4)),
% 0.20/0.44    inference(forward_demodulation,[],[f177,f182])).
% 0.20/0.44  fof(f182,plain,(
% 0.20/0.44    sK0 = sK1 | ~spl5_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f180])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f176])).
% 0.20/0.44  fof(f207,plain,(
% 0.20/0.44    spl5_4 | spl5_6),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.44  fof(f202,plain,(
% 0.20/0.44    $false | (spl5_4 | spl5_6)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f181,f198,f78])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.20/0.44    inference(definition_unfolding,[],[f50,f69,f69])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.20/0.44    inference(ennf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,axiom,(
% 0.20/0.44    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.20/0.44  fof(f198,plain,(
% 0.20/0.44    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f196])).
% 0.20/0.44  fof(f196,plain,(
% 0.20/0.44    spl5_6 <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.44  fof(f181,plain,(
% 0.20/0.44    sK0 != sK1 | spl5_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f180])).
% 0.20/0.44  fof(f200,plain,(
% 0.20/0.44    spl5_3 | ~spl5_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f71,f180,f176])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    inference(definition_unfolding,[],[f41,f69,f43,f69,f69])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.44    inference(nnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.20/0.44    inference(ennf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.44    inference(negated_conjecture,[],[f18])).
% 0.20/0.44  fof(f18,conjecture,(
% 0.20/0.44    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.44  fof(f199,plain,(
% 0.20/0.44    ~spl5_6 | spl5_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f187,f176,f196])).
% 0.20/0.44  fof(f187,plain,(
% 0.20/0.44    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f186])).
% 0.20/0.44  fof(f186,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 0.20/0.44    inference(forward_demodulation,[],[f184,f52])).
% 0.20/0.44  fof(f184,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 0.20/0.44    inference(superposition,[],[f178,f101])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.44    inference(superposition,[],[f53,f57])).
% 0.20/0.44  fof(f178,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f176])).
% 0.20/0.44  fof(f183,plain,(
% 0.20/0.44    ~spl5_3 | spl5_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f70,f180,f176])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    sK0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    inference(definition_unfolding,[],[f42,f69,f43,f69,f69])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f134,plain,(
% 0.20/0.44    spl5_1 | spl5_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f127,f132,f129])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f124])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(superposition,[],[f56,f53])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(rectify,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (4881)------------------------------
% 0.20/0.44  % (4881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (4881)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (4881)Memory used [KB]: 11129
% 0.20/0.44  % (4881)Time elapsed: 0.032 s
% 0.20/0.44  % (4881)------------------------------
% 0.20/0.44  % (4881)------------------------------
% 0.20/0.45  % (4848)Success in time 0.09 s
%------------------------------------------------------------------------------
