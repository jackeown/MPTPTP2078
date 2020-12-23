%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:23 EST 2020

% Result     : Theorem 13.58s
% Output     : Refutation 13.58s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 289 expanded)
%              Number of leaves         :   28 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  409 (1175 expanded)
%              Number of equality atoms :  127 ( 419 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18078,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f172,f173,f16366,f17186,f17187,f17188,f17198,f17629,f17636,f18077])).

fof(f18077,plain,
    ( spl8_3
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f18076])).

fof(f18076,plain,
    ( $false
    | spl8_3
    | spl8_43 ),
    inference(subsumption_resolution,[],[f18075,f198])).

fof(f198,plain,(
    ! [X4,X5] : r2_hidden(X5,k2_tarski(X4,X5)) ),
    inference(superposition,[],[f153,f115])).

fof(f115,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f153,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
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

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f18075,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | spl8_3
    | spl8_43 ),
    inference(subsumption_resolution,[],[f18072,f169])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f18072,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | spl8_43 ),
    inference(resolution,[],[f17628,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f17628,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl8_43 ),
    inference(avatar_component_clause,[],[f17626])).

fof(f17626,plain,
    ( spl8_43
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f17636,plain,
    ( spl8_2
    | spl8_42 ),
    inference(avatar_contradiction_clause,[],[f17635])).

fof(f17635,plain,
    ( $false
    | spl8_2
    | spl8_42 ),
    inference(subsumption_resolution,[],[f17634,f196])).

fof(f196,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f157,f115])).

fof(f157,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f17634,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl8_2
    | spl8_42 ),
    inference(subsumption_resolution,[],[f17631,f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f17631,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl8_42 ),
    inference(resolution,[],[f17624,f101])).

fof(f17624,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f17622])).

fof(f17622,plain,
    ( spl8_42
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f17629,plain,
    ( ~ spl8_42
    | ~ spl8_43
    | spl8_8 ),
    inference(avatar_split_clause,[],[f17601,f1212,f17626,f17622])).

fof(f1212,plain,
    ( spl8_8
  <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f17601,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl8_8 ),
    inference(resolution,[],[f372,f1213])).

fof(f1213,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f372,plain,(
    ! [X39,X38,X40] :
      ( r1_tarski(k2_tarski(X38,X39),X40)
      | ~ r2_hidden(X39,X40)
      | ~ r2_hidden(X38,X40) ) ),
    inference(superposition,[],[f174,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f174,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f128,f116])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f128,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f17198,plain,
    ( ~ spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f17194,f160,f1217])).

fof(f1217,plain,
    ( spl8_9
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f160,plain,
    ( spl8_1
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f17194,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f17193])).

fof(f17193,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl8_1 ),
    inference(superposition,[],[f162,f518])).

fof(f518,plain,(
    ! [X17,X18] :
      ( k4_xboole_0(X17,X18) = X17
      | ~ r1_xboole_0(X17,X18) ) ),
    inference(forward_demodulation,[],[f501,f125])).

fof(f125,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f501,plain,(
    ! [X17,X18] :
      ( k4_xboole_0(X17,X18) = k5_xboole_0(X17,k1_xboole_0)
      | ~ r1_xboole_0(X17,X18) ) ),
    inference(superposition,[],[f114,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f107,f108])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f114,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f162,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f17188,plain,
    ( ~ spl8_3
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f17161,f1212,f168])).

fof(f17161,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f17159,f198])).

fof(f17159,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f17152])).

fof(f17152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,k2_tarski(sK0,sK1)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f16423,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f16423,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
        | ~ r2_hidden(X6,k2_tarski(sK0,sK1)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f1214,f1967])).

fof(f1967,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f1952,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f105,f119])).

fof(f119,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1952,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | r2_hidden(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f264,f199])).

fof(f199,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f127,f116])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f264,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
      | r2_hidden(X10,X8)
      | r2_hidden(X10,k4_xboole_0(X8,X9)) ) ),
    inference(superposition,[],[f101,f114])).

fof(f1214,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f17187,plain,
    ( spl8_9
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f17183,f1212,f1217])).

fof(f17183,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f17176])).

fof(f17176,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f17164,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f17164,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),X1),sK2)
        | r1_xboole_0(k2_tarski(sK0,sK1),X1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f17159,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f17186,plain,
    ( ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f17160,f1212,f164])).

fof(f17160,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f17159,f196])).

fof(f16366,plain,
    ( spl8_8
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f16294,f160,f1212])).

fof(f16294,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl8_1 ),
    inference(superposition,[],[f182,f161])).

fof(f161,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f182,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f118,f117])).

fof(f117,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f173,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f67,f164,f160])).

fof(f67,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f172,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f68,f168,f160])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f171,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f69,f168,f164,f160])).

fof(f69,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (18139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (18137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (18135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (18157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18143)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (18147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (18141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18137)Refutation not found, incomplete strategy% (18137)------------------------------
% 0.21/0.53  % (18137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18137)Memory used [KB]: 10874
% 0.21/0.53  % (18137)Time elapsed: 0.117 s
% 0.21/0.53  % (18137)------------------------------
% 0.21/0.53  % (18137)------------------------------
% 0.21/0.53  % (18148)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.53  % (18159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.53  % (18151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.53  % (18150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.53  % (18146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.53  % (18145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.53  % (18163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (18162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (18152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (18152)Refutation not found, incomplete strategy% (18152)------------------------------
% 1.31/0.54  % (18152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (18152)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (18152)Memory used [KB]: 10618
% 1.31/0.54  % (18152)Time elapsed: 0.129 s
% 1.31/0.54  % (18152)------------------------------
% 1.31/0.54  % (18152)------------------------------
% 1.31/0.54  % (18164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (18142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (18144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.54  % (18154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.54  % (18156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (18143)Refutation not found, incomplete strategy% (18143)------------------------------
% 1.31/0.55  % (18143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (18143)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (18143)Memory used [KB]: 10874
% 1.31/0.55  % (18143)Time elapsed: 0.144 s
% 1.31/0.55  % (18143)------------------------------
% 1.31/0.55  % (18143)------------------------------
% 1.31/0.55  % (18153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % (18155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.55  % (18161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.55  % (18158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.16/0.69  % (18167)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.45/0.71  % (18165)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.45/0.72  % (18166)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.26/0.81  % (18140)Time limit reached!
% 3.26/0.81  % (18140)------------------------------
% 3.26/0.81  % (18140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (18140)Termination reason: Time limit
% 3.26/0.81  
% 3.26/0.81  % (18140)Memory used [KB]: 9083
% 3.26/0.81  % (18140)Time elapsed: 0.407 s
% 3.26/0.81  % (18140)------------------------------
% 3.26/0.81  % (18140)------------------------------
% 3.63/0.91  % (18147)Time limit reached!
% 3.63/0.91  % (18147)------------------------------
% 3.63/0.91  % (18147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.91  % (18136)Time limit reached!
% 3.63/0.91  % (18136)------------------------------
% 3.63/0.91  % (18136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.91  % (18136)Termination reason: Time limit
% 3.63/0.91  % (18136)Termination phase: Saturation
% 3.63/0.91  
% 3.63/0.91  % (18136)Memory used [KB]: 9850
% 3.63/0.91  % (18136)Time elapsed: 0.500 s
% 3.63/0.91  % (18136)------------------------------
% 3.63/0.91  % (18136)------------------------------
% 3.63/0.92  % (18147)Termination reason: Time limit
% 3.63/0.92  
% 3.63/0.92  % (18147)Memory used [KB]: 9083
% 3.63/0.92  % (18147)Time elapsed: 0.505 s
% 3.63/0.92  % (18147)------------------------------
% 3.63/0.92  % (18147)------------------------------
% 3.63/0.93  % (18145)Time limit reached!
% 3.63/0.93  % (18145)------------------------------
% 3.63/0.93  % (18145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.93  % (18145)Termination reason: Time limit
% 3.63/0.93  % (18145)Termination phase: Saturation
% 3.63/0.93  
% 3.63/0.93  % (18145)Memory used [KB]: 14583
% 3.63/0.93  % (18145)Time elapsed: 0.500 s
% 3.63/0.93  % (18145)------------------------------
% 3.63/0.93  % (18145)------------------------------
% 3.63/0.94  % (18135)Time limit reached!
% 3.63/0.94  % (18135)------------------------------
% 3.63/0.94  % (18135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.94  % (18135)Termination reason: Time limit
% 3.63/0.94  
% 3.63/0.94  % (18135)Memory used [KB]: 2302
% 3.63/0.94  % (18135)Time elapsed: 0.515 s
% 3.63/0.94  % (18135)------------------------------
% 3.63/0.94  % (18135)------------------------------
% 4.28/0.95  % (18168)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.50/1.01  % (18142)Time limit reached!
% 4.50/1.01  % (18142)------------------------------
% 4.50/1.01  % (18142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.01  % (18142)Termination reason: Time limit
% 4.50/1.01  
% 4.50/1.01  % (18142)Memory used [KB]: 11129
% 4.50/1.01  % (18142)Time elapsed: 0.609 s
% 4.50/1.01  % (18142)------------------------------
% 4.50/1.01  % (18142)------------------------------
% 4.50/1.02  % (18163)Time limit reached!
% 4.50/1.02  % (18163)------------------------------
% 4.50/1.02  % (18163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (18151)Time limit reached!
% 4.50/1.02  % (18151)------------------------------
% 4.50/1.02  % (18151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (18151)Termination reason: Time limit
% 4.50/1.02  
% 4.50/1.02  % (18151)Memory used [KB]: 17910
% 4.50/1.02  % (18151)Time elapsed: 0.623 s
% 4.50/1.02  % (18151)------------------------------
% 4.50/1.02  % (18151)------------------------------
% 4.50/1.03  % (18193)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.50/1.03  % (18195)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.79/1.04  % (18163)Termination reason: Time limit
% 4.79/1.04  % (18163)Termination phase: Saturation
% 4.79/1.04  
% 4.79/1.04  % (18163)Memory used [KB]: 9722
% 4.79/1.04  % (18163)Time elapsed: 0.600 s
% 4.79/1.04  % (18163)------------------------------
% 4.79/1.04  % (18163)------------------------------
% 5.48/1.07  % (18201)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.48/1.08  % (18207)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.91/1.15  % (18235)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.91/1.16  % (18247)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.91/1.16  % (18235)Refutation not found, incomplete strategy% (18235)------------------------------
% 5.91/1.16  % (18235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.31/1.17  % (18258)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.31/1.17  % (18235)Termination reason: Refutation not found, incomplete strategy
% 6.31/1.17  
% 6.31/1.17  % (18235)Memory used [KB]: 1791
% 6.31/1.17  % (18235)Time elapsed: 0.124 s
% 6.31/1.17  % (18235)------------------------------
% 6.31/1.17  % (18235)------------------------------
% 6.31/1.23  % (18156)Time limit reached!
% 6.31/1.23  % (18156)------------------------------
% 6.31/1.23  % (18156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.31/1.24  % (18156)Termination reason: Time limit
% 6.31/1.24  
% 6.31/1.24  % (18156)Memory used [KB]: 3709
% 6.31/1.24  % (18156)Time elapsed: 0.820 s
% 6.31/1.24  % (18156)------------------------------
% 6.31/1.24  % (18156)------------------------------
% 6.98/1.28  % (18168)Time limit reached!
% 6.98/1.28  % (18168)------------------------------
% 6.98/1.28  % (18168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.98/1.28  % (18168)Termination reason: Time limit
% 6.98/1.28  
% 6.98/1.28  % (18168)Memory used [KB]: 8443
% 6.98/1.28  % (18168)Time elapsed: 0.434 s
% 6.98/1.28  % (18168)------------------------------
% 6.98/1.28  % (18168)------------------------------
% 7.17/1.31  % (18325)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.70/1.37  % (18338)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.70/1.37  % (18193)Time limit reached!
% 7.70/1.37  % (18193)------------------------------
% 7.70/1.37  % (18193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.70/1.37  % (18193)Termination reason: Time limit
% 7.70/1.37  
% 7.70/1.37  % (18193)Memory used [KB]: 14967
% 7.70/1.37  % (18193)Time elapsed: 0.408 s
% 7.70/1.37  % (18193)------------------------------
% 7.70/1.37  % (18193)------------------------------
% 7.70/1.41  % (18350)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.70/1.41  % (18350)Refutation not found, incomplete strategy% (18350)------------------------------
% 7.70/1.41  % (18350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.70/1.41  % (18350)Termination reason: Refutation not found, incomplete strategy
% 7.70/1.41  
% 7.70/1.41  % (18350)Memory used [KB]: 1791
% 7.70/1.41  % (18350)Time elapsed: 0.102 s
% 7.70/1.41  % (18350)------------------------------
% 7.70/1.41  % (18350)------------------------------
% 8.61/1.47  % (18384)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.16/1.55  % (18404)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 10.12/1.64  % (18157)Time limit reached!
% 10.12/1.64  % (18157)------------------------------
% 10.12/1.64  % (18157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.64  % (18157)Termination reason: Time limit
% 10.12/1.64  
% 10.12/1.64  % (18157)Memory used [KB]: 16119
% 10.12/1.64  % (18157)Time elapsed: 1.200 s
% 10.12/1.64  % (18157)------------------------------
% 10.12/1.64  % (18157)------------------------------
% 10.12/1.65  % (18161)Time limit reached!
% 10.12/1.65  % (18161)------------------------------
% 10.12/1.65  % (18161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.27/1.66  % (18161)Termination reason: Time limit
% 10.27/1.66  
% 10.27/1.66  % (18161)Memory used [KB]: 19829
% 10.27/1.66  % (18161)Time elapsed: 1.229 s
% 10.27/1.66  % (18161)------------------------------
% 10.27/1.66  % (18161)------------------------------
% 10.27/1.70  % (18159)Time limit reached!
% 10.27/1.70  % (18159)------------------------------
% 10.27/1.70  % (18159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.27/1.70  % (18159)Termination reason: Time limit
% 10.27/1.70  
% 10.27/1.70  % (18159)Memory used [KB]: 17142
% 10.27/1.70  % (18159)Time elapsed: 1.303 s
% 10.27/1.70  % (18159)------------------------------
% 10.27/1.70  % (18159)------------------------------
% 10.27/1.72  % (18150)Time limit reached!
% 10.27/1.72  % (18150)------------------------------
% 10.27/1.72  % (18150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.27/1.72  % (18150)Termination reason: Time limit
% 10.27/1.72  
% 10.27/1.72  % (18150)Memory used [KB]: 11001
% 10.27/1.72  % (18150)Time elapsed: 1.319 s
% 10.27/1.72  % (18150)------------------------------
% 10.27/1.72  % (18150)------------------------------
% 10.83/1.73  % (18409)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.83/1.76  % (18410)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.05/1.79  % (18338)Time limit reached!
% 11.05/1.79  % (18338)------------------------------
% 11.05/1.79  % (18338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.05/1.79  % (18338)Termination reason: Time limit
% 11.05/1.79  
% 11.05/1.79  % (18338)Memory used [KB]: 4733
% 11.05/1.79  % (18338)Time elapsed: 0.533 s
% 11.05/1.79  % (18338)------------------------------
% 11.05/1.79  % (18338)------------------------------
% 11.52/1.84  % (18411)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 11.52/1.86  % (18412)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 11.73/1.90  % (18413)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 11.73/1.92  % (18139)Time limit reached!
% 11.73/1.92  % (18139)------------------------------
% 11.73/1.92  % (18139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.92  % (18139)Termination reason: Time limit
% 11.73/1.92  
% 11.73/1.92  % (18139)Memory used [KB]: 13816
% 11.73/1.92  % (18139)Time elapsed: 1.520 s
% 11.73/1.92  % (18139)------------------------------
% 11.73/1.92  % (18139)------------------------------
% 11.73/1.93  % (18162)Time limit reached!
% 11.73/1.93  % (18162)------------------------------
% 11.73/1.93  % (18162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.93  % (18162)Termination reason: Time limit
% 11.73/1.93  
% 11.73/1.93  % (18162)Memory used [KB]: 14456
% 11.73/1.93  % (18162)Time elapsed: 1.522 s
% 11.73/1.93  % (18162)------------------------------
% 11.73/1.93  % (18162)------------------------------
% 12.79/2.03  % (18146)Time limit reached!
% 12.79/2.03  % (18146)------------------------------
% 12.79/2.03  % (18146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.79/2.03  % (18146)Termination reason: Time limit
% 12.79/2.03  
% 12.79/2.03  % (18146)Memory used [KB]: 29551
% 12.79/2.03  % (18146)Time elapsed: 1.616 s
% 12.79/2.03  % (18146)------------------------------
% 12.79/2.03  % (18146)------------------------------
% 12.99/2.07  % (18414)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 12.99/2.08  % (18409)Time limit reached!
% 12.99/2.08  % (18409)------------------------------
% 12.99/2.08  % (18409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.99/2.09  % (18415)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 12.99/2.09  % (18409)Termination reason: Time limit
% 12.99/2.09  
% 12.99/2.09  % (18409)Memory used [KB]: 5117
% 12.99/2.09  % (18409)Time elapsed: 0.421 s
% 12.99/2.09  % (18409)------------------------------
% 12.99/2.09  % (18409)------------------------------
% 12.99/2.13  % (18416)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 13.58/2.14  % (18167)Refutation found. Thanks to Tanya!
% 13.58/2.14  % SZS status Theorem for theBenchmark
% 13.58/2.14  % SZS output start Proof for theBenchmark
% 13.58/2.14  fof(f18078,plain,(
% 13.58/2.14    $false),
% 13.58/2.14    inference(avatar_sat_refutation,[],[f171,f172,f173,f16366,f17186,f17187,f17188,f17198,f17629,f17636,f18077])).
% 13.58/2.14  fof(f18077,plain,(
% 13.58/2.14    spl8_3 | spl8_43),
% 13.58/2.14    inference(avatar_contradiction_clause,[],[f18076])).
% 13.58/2.14  fof(f18076,plain,(
% 13.58/2.14    $false | (spl8_3 | spl8_43)),
% 13.58/2.14    inference(subsumption_resolution,[],[f18075,f198])).
% 13.58/2.14  fof(f198,plain,(
% 13.58/2.14    ( ! [X4,X5] : (r2_hidden(X5,k2_tarski(X4,X5))) )),
% 13.58/2.14    inference(superposition,[],[f153,f115])).
% 13.58/2.14  fof(f115,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f24])).
% 13.58/2.14  fof(f24,axiom,(
% 13.58/2.14    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 13.58/2.14  fof(f153,plain,(
% 13.58/2.14    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 13.58/2.14    inference(equality_resolution,[],[f152])).
% 13.58/2.14  fof(f152,plain,(
% 13.58/2.14    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 13.58/2.14    inference(equality_resolution,[],[f93])).
% 13.58/2.14  fof(f93,plain,(
% 13.58/2.14    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 13.58/2.14    inference(cnf_transformation,[],[f59])).
% 13.58/2.14  fof(f59,plain,(
% 13.58/2.14    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.58/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 13.58/2.14  fof(f58,plain,(
% 13.58/2.14    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 13.58/2.14    introduced(choice_axiom,[])).
% 13.58/2.14  fof(f57,plain,(
% 13.58/2.14    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.58/2.14    inference(rectify,[],[f56])).
% 13.58/2.14  fof(f56,plain,(
% 13.58/2.14    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.58/2.14    inference(flattening,[],[f55])).
% 13.58/2.14  fof(f55,plain,(
% 13.58/2.14    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 13.58/2.14    inference(nnf_transformation,[],[f38])).
% 13.58/2.14  fof(f38,plain,(
% 13.58/2.14    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 13.58/2.14    inference(ennf_transformation,[],[f19])).
% 13.58/2.14  fof(f19,axiom,(
% 13.58/2.14    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 13.58/2.14  fof(f18075,plain,(
% 13.58/2.14    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | (spl8_3 | spl8_43)),
% 13.58/2.14    inference(subsumption_resolution,[],[f18072,f169])).
% 13.58/2.14  fof(f169,plain,(
% 13.58/2.14    ~r2_hidden(sK1,sK2) | spl8_3),
% 13.58/2.14    inference(avatar_component_clause,[],[f168])).
% 13.58/2.14  fof(f168,plain,(
% 13.58/2.14    spl8_3 <=> r2_hidden(sK1,sK2)),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 13.58/2.14  fof(f18072,plain,(
% 13.58/2.14    r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | spl8_43),
% 13.58/2.14    inference(resolution,[],[f17628,f101])).
% 13.58/2.14  fof(f101,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f60])).
% 13.58/2.14  fof(f60,plain,(
% 13.58/2.14    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 13.58/2.14    inference(nnf_transformation,[],[f39])).
% 13.58/2.14  fof(f39,plain,(
% 13.58/2.14    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 13.58/2.14    inference(ennf_transformation,[],[f3])).
% 13.58/2.14  fof(f3,axiom,(
% 13.58/2.14    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 13.58/2.14  fof(f17628,plain,(
% 13.58/2.14    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl8_43),
% 13.58/2.14    inference(avatar_component_clause,[],[f17626])).
% 13.58/2.14  fof(f17626,plain,(
% 13.58/2.14    spl8_43 <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 13.58/2.14  fof(f17636,plain,(
% 13.58/2.14    spl8_2 | spl8_42),
% 13.58/2.14    inference(avatar_contradiction_clause,[],[f17635])).
% 13.58/2.14  fof(f17635,plain,(
% 13.58/2.14    $false | (spl8_2 | spl8_42)),
% 13.58/2.14    inference(subsumption_resolution,[],[f17634,f196])).
% 13.58/2.14  fof(f196,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 13.58/2.14    inference(superposition,[],[f157,f115])).
% 13.58/2.14  fof(f157,plain,(
% 13.58/2.14    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 13.58/2.14    inference(equality_resolution,[],[f156])).
% 13.58/2.14  fof(f156,plain,(
% 13.58/2.14    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 13.58/2.14    inference(equality_resolution,[],[f91])).
% 13.58/2.14  fof(f91,plain,(
% 13.58/2.14    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 13.58/2.14    inference(cnf_transformation,[],[f59])).
% 13.58/2.14  fof(f17634,plain,(
% 13.58/2.14    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (spl8_2 | spl8_42)),
% 13.58/2.14    inference(subsumption_resolution,[],[f17631,f165])).
% 13.58/2.14  fof(f165,plain,(
% 13.58/2.14    ~r2_hidden(sK0,sK2) | spl8_2),
% 13.58/2.14    inference(avatar_component_clause,[],[f164])).
% 13.58/2.14  fof(f164,plain,(
% 13.58/2.14    spl8_2 <=> r2_hidden(sK0,sK2)),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 13.58/2.14  fof(f17631,plain,(
% 13.58/2.14    r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | spl8_42),
% 13.58/2.14    inference(resolution,[],[f17624,f101])).
% 13.58/2.14  fof(f17624,plain,(
% 13.58/2.14    ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl8_42),
% 13.58/2.14    inference(avatar_component_clause,[],[f17622])).
% 13.58/2.14  fof(f17622,plain,(
% 13.58/2.14    spl8_42 <=> r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 13.58/2.14  fof(f17629,plain,(
% 13.58/2.14    ~spl8_42 | ~spl8_43 | spl8_8),
% 13.58/2.14    inference(avatar_split_clause,[],[f17601,f1212,f17626,f17622])).
% 13.58/2.14  fof(f1212,plain,(
% 13.58/2.14    spl8_8 <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 13.58/2.14  fof(f17601,plain,(
% 13.58/2.14    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl8_8),
% 13.58/2.14    inference(resolution,[],[f372,f1213])).
% 13.58/2.14  fof(f1213,plain,(
% 13.58/2.14    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl8_8),
% 13.58/2.14    inference(avatar_component_clause,[],[f1212])).
% 13.58/2.14  fof(f372,plain,(
% 13.58/2.14    ( ! [X39,X38,X40] : (r1_tarski(k2_tarski(X38,X39),X40) | ~r2_hidden(X39,X40) | ~r2_hidden(X38,X40)) )),
% 13.58/2.14    inference(superposition,[],[f174,f102])).
% 13.58/2.14  fof(f102,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f41])).
% 13.58/2.14  fof(f41,plain,(
% 13.58/2.14    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 13.58/2.14    inference(flattening,[],[f40])).
% 13.58/2.14  fof(f40,plain,(
% 13.58/2.14    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 13.58/2.14    inference(ennf_transformation,[],[f31])).
% 13.58/2.14  fof(f31,axiom,(
% 13.58/2.14    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 13.58/2.14  fof(f174,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 13.58/2.14    inference(superposition,[],[f128,f116])).
% 13.58/2.14  fof(f116,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f1])).
% 13.58/2.14  fof(f1,axiom,(
% 13.58/2.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 13.58/2.14  fof(f128,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f10])).
% 13.58/2.14  fof(f10,axiom,(
% 13.58/2.14    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 13.58/2.14  fof(f17198,plain,(
% 13.58/2.14    ~spl8_9 | spl8_1),
% 13.58/2.14    inference(avatar_split_clause,[],[f17194,f160,f1217])).
% 13.58/2.14  fof(f1217,plain,(
% 13.58/2.14    spl8_9 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 13.58/2.14  fof(f160,plain,(
% 13.58/2.14    spl8_1 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.58/2.14    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 13.58/2.14  fof(f17194,plain,(
% 13.58/2.14    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | spl8_1),
% 13.58/2.14    inference(trivial_inequality_removal,[],[f17193])).
% 13.58/2.14  fof(f17193,plain,(
% 13.58/2.14    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | spl8_1),
% 13.58/2.14    inference(superposition,[],[f162,f518])).
% 13.58/2.14  fof(f518,plain,(
% 13.58/2.14    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = X17 | ~r1_xboole_0(X17,X18)) )),
% 13.58/2.14    inference(forward_demodulation,[],[f501,f125])).
% 13.58/2.14  fof(f125,plain,(
% 13.58/2.14    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 13.58/2.14    inference(cnf_transformation,[],[f14])).
% 13.58/2.14  fof(f14,axiom,(
% 13.58/2.14    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 13.58/2.14  fof(f501,plain,(
% 13.58/2.14    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k5_xboole_0(X17,k1_xboole_0) | ~r1_xboole_0(X17,X18)) )),
% 13.58/2.14    inference(superposition,[],[f114,f186])).
% 13.58/2.14  fof(f186,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 13.58/2.14    inference(resolution,[],[f107,f108])).
% 13.58/2.14  fof(f108,plain,(
% 13.58/2.14    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 13.58/2.14    inference(cnf_transformation,[],[f66])).
% 13.58/2.14  fof(f66,plain,(
% 13.58/2.14    ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0)),
% 13.58/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f65])).
% 13.58/2.14  fof(f65,plain,(
% 13.58/2.14    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 13.58/2.14    introduced(choice_axiom,[])).
% 13.58/2.14  fof(f44,plain,(
% 13.58/2.14    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 13.58/2.14    inference(ennf_transformation,[],[f6])).
% 13.58/2.14  fof(f6,axiom,(
% 13.58/2.14    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 13.58/2.14  fof(f107,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f64])).
% 13.58/2.14  fof(f64,plain,(
% 13.58/2.14    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f63])).
% 13.58/2.14  fof(f63,plain,(
% 13.58/2.14    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 13.58/2.14    introduced(choice_axiom,[])).
% 13.58/2.14  fof(f43,plain,(
% 13.58/2.14    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(ennf_transformation,[],[f35])).
% 13.58/2.14  fof(f35,plain,(
% 13.58/2.14    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(rectify,[],[f5])).
% 13.58/2.14  fof(f5,axiom,(
% 13.58/2.14    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 13.58/2.14  fof(f114,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.58/2.14    inference(cnf_transformation,[],[f7])).
% 13.58/2.14  fof(f7,axiom,(
% 13.58/2.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 13.58/2.14  fof(f162,plain,(
% 13.58/2.14    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl8_1),
% 13.58/2.14    inference(avatar_component_clause,[],[f160])).
% 13.58/2.14  fof(f17188,plain,(
% 13.58/2.14    ~spl8_3 | ~spl8_8),
% 13.58/2.14    inference(avatar_split_clause,[],[f17161,f1212,f168])).
% 13.58/2.14  fof(f17161,plain,(
% 13.58/2.14    ~r2_hidden(sK1,sK2) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f17159,f198])).
% 13.58/2.14  fof(f17159,plain,(
% 13.58/2.14    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl8_8),
% 13.58/2.14    inference(duplicate_literal_removal,[],[f17152])).
% 13.58/2.14  fof(f17152,plain,(
% 13.58/2.14    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK1)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,k2_tarski(sK0,sK1))) ) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f16423,f99])).
% 13.58/2.14  fof(f99,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f60])).
% 13.58/2.14  fof(f16423,plain,(
% 13.58/2.14    ( ! [X6] : (r2_hidden(X6,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(X6,k2_tarski(sK0,sK1))) ) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f1214,f1967])).
% 13.58/2.14  fof(f1967,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r1_tarski(X1,X0) | r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) )),
% 13.58/2.14    inference(subsumption_resolution,[],[f1952,f207])).
% 13.58/2.14  fof(f207,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 13.58/2.14    inference(resolution,[],[f105,f119])).
% 13.58/2.14  fof(f119,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f15])).
% 13.58/2.14  fof(f15,axiom,(
% 13.58/2.14    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 13.58/2.14  fof(f105,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f62])).
% 13.58/2.14  fof(f62,plain,(
% 13.58/2.14    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f61])).
% 13.58/2.14  fof(f61,plain,(
% 13.58/2.14    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 13.58/2.14    introduced(choice_axiom,[])).
% 13.58/2.14  fof(f42,plain,(
% 13.58/2.14    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(ennf_transformation,[],[f34])).
% 13.58/2.14  fof(f34,plain,(
% 13.58/2.14    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 13.58/2.14    inference(rectify,[],[f4])).
% 13.58/2.14  fof(f4,axiom,(
% 13.58/2.14    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 13.58/2.14  fof(f1952,plain,(
% 13.58/2.14    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | r2_hidden(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,X0)) )),
% 13.58/2.14    inference(superposition,[],[f264,f199])).
% 13.58/2.14  fof(f199,plain,(
% 13.58/2.14    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 13.58/2.14    inference(superposition,[],[f127,f116])).
% 13.58/2.14  fof(f127,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f45])).
% 13.58/2.14  fof(f45,plain,(
% 13.58/2.14    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 13.58/2.14    inference(ennf_transformation,[],[f11])).
% 13.58/2.14  fof(f11,axiom,(
% 13.58/2.14    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 13.58/2.14  fof(f264,plain,(
% 13.58/2.14    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,X9)) | r2_hidden(X10,X8) | r2_hidden(X10,k4_xboole_0(X8,X9))) )),
% 13.58/2.14    inference(superposition,[],[f101,f114])).
% 13.58/2.14  fof(f1214,plain,(
% 13.58/2.14    r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl8_8),
% 13.58/2.14    inference(avatar_component_clause,[],[f1212])).
% 13.58/2.14  fof(f17187,plain,(
% 13.58/2.14    spl8_9 | ~spl8_8),
% 13.58/2.14    inference(avatar_split_clause,[],[f17183,f1212,f1217])).
% 13.58/2.14  fof(f17183,plain,(
% 13.58/2.14    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl8_8),
% 13.58/2.14    inference(duplicate_literal_removal,[],[f17176])).
% 13.58/2.14  fof(f17176,plain,(
% 13.58/2.14    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f17164,f104])).
% 13.58/2.14  fof(f104,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f62])).
% 13.58/2.14  fof(f17164,plain,(
% 13.58/2.14    ( ! [X1] : (~r2_hidden(sK5(k2_tarski(sK0,sK1),X1),sK2) | r1_xboole_0(k2_tarski(sK0,sK1),X1)) ) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f17159,f103])).
% 13.58/2.14  fof(f103,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f62])).
% 13.58/2.14  fof(f17186,plain,(
% 13.58/2.14    ~spl8_2 | ~spl8_8),
% 13.58/2.14    inference(avatar_split_clause,[],[f17160,f1212,f164])).
% 13.58/2.14  fof(f17160,plain,(
% 13.58/2.14    ~r2_hidden(sK0,sK2) | ~spl8_8),
% 13.58/2.14    inference(resolution,[],[f17159,f196])).
% 13.58/2.14  fof(f16366,plain,(
% 13.58/2.14    spl8_8 | ~spl8_1),
% 13.58/2.14    inference(avatar_split_clause,[],[f16294,f160,f1212])).
% 13.58/2.14  fof(f16294,plain,(
% 13.58/2.14    r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl8_1),
% 13.58/2.14    inference(superposition,[],[f182,f161])).
% 13.58/2.14  fof(f161,plain,(
% 13.58/2.14    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl8_1),
% 13.58/2.14    inference(avatar_component_clause,[],[f160])).
% 13.58/2.14  fof(f182,plain,(
% 13.58/2.14    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 13.58/2.14    inference(superposition,[],[f118,f117])).
% 13.58/2.14  fof(f117,plain,(
% 13.58/2.14    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 13.58/2.14    inference(cnf_transformation,[],[f2])).
% 13.58/2.14  fof(f2,axiom,(
% 13.58/2.14    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 13.58/2.14  fof(f118,plain,(
% 13.58/2.14    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 13.58/2.14    inference(cnf_transformation,[],[f18])).
% 13.58/2.14  fof(f18,axiom,(
% 13.58/2.14    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 13.58/2.14  fof(f173,plain,(
% 13.58/2.14    spl8_1 | ~spl8_2),
% 13.58/2.14    inference(avatar_split_clause,[],[f67,f164,f160])).
% 13.58/2.14  fof(f67,plain,(
% 13.58/2.14    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.58/2.14    inference(cnf_transformation,[],[f49])).
% 13.58/2.14  fof(f49,plain,(
% 13.58/2.14    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 13.58/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f48])).
% 13.58/2.14  fof(f48,plain,(
% 13.58/2.14    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 13.58/2.14    introduced(choice_axiom,[])).
% 13.58/2.14  fof(f47,plain,(
% 13.58/2.14    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 13.58/2.14    inference(flattening,[],[f46])).
% 13.58/2.14  fof(f46,plain,(
% 13.58/2.14    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 13.58/2.14    inference(nnf_transformation,[],[f36])).
% 13.58/2.14  fof(f36,plain,(
% 13.58/2.14    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 13.58/2.14    inference(ennf_transformation,[],[f33])).
% 13.58/2.14  fof(f33,negated_conjecture,(
% 13.58/2.14    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 13.58/2.14    inference(negated_conjecture,[],[f32])).
% 13.58/2.14  fof(f32,conjecture,(
% 13.58/2.14    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 13.58/2.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 13.58/2.14  fof(f172,plain,(
% 13.58/2.14    spl8_1 | ~spl8_3),
% 13.58/2.14    inference(avatar_split_clause,[],[f68,f168,f160])).
% 13.58/2.14  fof(f68,plain,(
% 13.58/2.14    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.58/2.14    inference(cnf_transformation,[],[f49])).
% 13.58/2.14  fof(f171,plain,(
% 13.58/2.14    ~spl8_1 | spl8_2 | spl8_3),
% 13.58/2.14    inference(avatar_split_clause,[],[f69,f168,f164,f160])).
% 13.58/2.14  fof(f69,plain,(
% 13.58/2.14    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 13.58/2.14    inference(cnf_transformation,[],[f49])).
% 13.58/2.14  % SZS output end Proof for theBenchmark
% 13.58/2.14  % (18167)------------------------------
% 13.58/2.14  % (18167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.58/2.14  % (18167)Termination reason: Refutation
% 13.58/2.14  
% 13.58/2.14  % (18167)Memory used [KB]: 17142
% 13.58/2.14  % (18167)Time elapsed: 1.544 s
% 13.58/2.14  % (18167)------------------------------
% 13.58/2.14  % (18167)------------------------------
% 13.58/2.14  % (18134)Success in time 1.794 s
%------------------------------------------------------------------------------
