%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:25 EST 2020

% Result     : Theorem 5.73s
% Output     : Refutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 193 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 436 expanded)
%              Number of equality atoms :  152 ( 344 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f312,f3635,f4171,f4188])).

fof(f4188,plain,
    ( spl4_1
    | ~ spl4_76 ),
    inference(avatar_contradiction_clause,[],[f4187])).

fof(f4187,plain,
    ( $false
    | spl4_1
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f4182,f117])).

fof(f117,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4182,plain,
    ( sK0 = sK1
    | ~ spl4_76 ),
    inference(duplicate_literal_removal,[],[f4178])).

fof(f4178,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl4_76 ),
    inference(resolution,[],[f4170,f113])).

fof(f113,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f4170,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f4168])).

fof(f4168,plain,
    ( spl4_76
  <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f4171,plain,
    ( spl4_76
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f4157,f3630,f4168])).

fof(f3630,plain,
    ( spl4_71
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f4157,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_71 ),
    inference(superposition,[],[f108,f3632])).

fof(f3632,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f3630])).

fof(f108,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3635,plain,
    ( spl4_71
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f3598,f309,f3630])).

fof(f309,plain,
    ( spl4_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3598,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f311,f461])).

fof(f461,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1) = k5_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(superposition,[],[f85,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f77,f78,f76,f84])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f311,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f309])).

fof(f312,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f307,f120,f309])).

fof(f120,plain,
    ( spl4_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f307,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f122,f49])).

fof(f122,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f123,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f86,f120])).

fof(f86,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f42,f84,f78,f84,f84])).

fof(f42,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f118,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f43,f115])).

fof(f43,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n001.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 18:51:45 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.35  % (23836)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.11/0.35  % (23856)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.11/0.35  % (23844)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.11/0.36  % (23848)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.11/0.36  % (23835)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.11/0.36  % (23839)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.36  % (23838)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.11/0.36  % (23841)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.11/0.36  % (23837)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.11/0.37  % (23855)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.11/0.37  % (23840)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.11/0.37  % (23842)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.11/0.37  % (23852)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.11/0.37  % (23833)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.11/0.37  % (23859)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.11/0.39  % (23846)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.11/0.39  % (23851)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.11/0.39  % (23850)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.11/0.39  % (23853)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.11/0.39  % (23851)Refutation not found, incomplete strategy% (23851)------------------------------
% 0.11/0.39  % (23851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (23851)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (23851)Memory used [KB]: 1663
% 0.11/0.39  % (23851)Time elapsed: 0.097 s
% 0.11/0.39  % (23851)------------------------------
% 0.11/0.39  % (23851)------------------------------
% 0.11/0.40  % (23834)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.11/0.40  % (23859)Refutation not found, incomplete strategy% (23859)------------------------------
% 0.11/0.40  % (23859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (23859)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (23859)Memory used [KB]: 6268
% 0.11/0.40  % (23859)Time elapsed: 0.078 s
% 0.11/0.40  % (23859)------------------------------
% 0.11/0.40  % (23859)------------------------------
% 0.11/0.40  % (23847)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.11/0.40  % (23843)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.11/0.40  % (23860)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.11/0.40  % (23847)Refutation not found, incomplete strategy% (23847)------------------------------
% 0.11/0.40  % (23847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (23847)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (23847)Memory used [KB]: 1663
% 0.11/0.40  % (23847)Time elapsed: 0.107 s
% 0.11/0.40  % (23847)------------------------------
% 0.11/0.40  % (23847)------------------------------
% 0.11/0.40  % (23845)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.11/0.41  % (23854)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.11/0.41  % (23845)Refutation not found, incomplete strategy% (23845)------------------------------
% 0.11/0.41  % (23845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.41  % (23861)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.11/0.41  % (23858)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.11/0.42  % (23862)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.11/0.42  % (23862)Refutation not found, incomplete strategy% (23862)------------------------------
% 0.11/0.42  % (23862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.42  % (23862)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.42  
% 0.11/0.42  % (23862)Memory used [KB]: 1663
% 0.11/0.42  % (23862)Time elapsed: 0.002 s
% 0.11/0.42  % (23862)------------------------------
% 0.11/0.42  % (23862)------------------------------
% 0.11/0.42  % (23845)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.42  
% 0.11/0.42  % (23845)Memory used [KB]: 10618
% 0.11/0.42  % (23845)Time elapsed: 0.115 s
% 0.11/0.42  % (23845)------------------------------
% 0.11/0.42  % (23845)------------------------------
% 0.11/0.43  % (23849)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.11/0.43  % (23849)Refutation not found, incomplete strategy% (23849)------------------------------
% 0.11/0.43  % (23849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.43  % (23849)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.43  
% 0.11/0.43  % (23849)Memory used [KB]: 10618
% 0.11/0.43  % (23849)Time elapsed: 0.134 s
% 0.11/0.43  % (23849)------------------------------
% 0.11/0.43  % (23849)------------------------------
% 0.11/0.43  % (23857)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.11/0.49  % (23836)Refutation not found, incomplete strategy% (23836)------------------------------
% 0.11/0.49  % (23836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.50  % (23836)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.50  
% 0.11/0.50  % (23836)Memory used [KB]: 6140
% 0.11/0.50  % (23836)Time elapsed: 0.190 s
% 0.11/0.50  % (23836)------------------------------
% 0.11/0.50  % (23836)------------------------------
% 0.11/0.52  % (23875)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.86/0.53  % (23874)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.56  % (23881)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.96/0.57  % (23877)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.96/0.57  % (23880)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.96/0.58  % (23882)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.96/0.59  % (23877)Refutation not found, incomplete strategy% (23877)------------------------------
% 1.96/0.59  % (23877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.59  % (23877)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.59  
% 1.96/0.59  % (23877)Memory used [KB]: 6140
% 1.96/0.59  % (23877)Time elapsed: 0.161 s
% 1.96/0.59  % (23877)------------------------------
% 1.96/0.59  % (23877)------------------------------
% 1.96/0.60  % (23880)Refutation not found, incomplete strategy% (23880)------------------------------
% 1.96/0.60  % (23880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.60  % (23880)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.60  
% 1.96/0.60  % (23880)Memory used [KB]: 10746
% 1.96/0.60  % (23880)Time elapsed: 0.146 s
% 1.96/0.60  % (23880)------------------------------
% 1.96/0.60  % (23880)------------------------------
% 1.96/0.61  % (23890)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.09/0.70  % (23835)Time limit reached!
% 3.09/0.70  % (23835)------------------------------
% 3.09/0.70  % (23835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.70  % (23835)Termination reason: Time limit
% 3.09/0.70  % (23835)Termination phase: Saturation
% 3.09/0.70  
% 3.09/0.70  % (23835)Memory used [KB]: 7675
% 3.09/0.70  % (23835)Time elapsed: 0.400 s
% 3.09/0.70  % (23835)------------------------------
% 3.09/0.70  % (23835)------------------------------
% 3.09/0.70  % (23857)Time limit reached!
% 3.09/0.70  % (23857)------------------------------
% 3.09/0.70  % (23857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.70  % (23857)Termination reason: Time limit
% 3.09/0.70  
% 3.09/0.70  % (23857)Memory used [KB]: 14583
% 3.09/0.70  % (23857)Time elapsed: 0.404 s
% 3.09/0.70  % (23857)------------------------------
% 3.09/0.70  % (23857)------------------------------
% 3.09/0.72  % (23892)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.09/0.75  % (23891)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.12/0.84  % (23839)Time limit reached!
% 4.12/0.84  % (23839)------------------------------
% 4.12/0.84  % (23839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.84  % (23839)Termination reason: Time limit
% 4.12/0.84  
% 4.12/0.84  % (23839)Memory used [KB]: 15863
% 4.12/0.84  % (23839)Time elapsed: 0.547 s
% 4.12/0.84  % (23839)------------------------------
% 4.12/0.84  % (23839)------------------------------
% 4.12/0.86  % (23893)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.12/0.88  % (23894)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.12/0.88  % (23893)Refutation not found, incomplete strategy% (23893)------------------------------
% 4.12/0.88  % (23893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.88  % (23893)Termination reason: Refutation not found, incomplete strategy
% 4.12/0.88  
% 4.12/0.88  % (23893)Memory used [KB]: 10746
% 4.12/0.88  % (23893)Time elapsed: 0.153 s
% 4.12/0.88  % (23893)------------------------------
% 4.12/0.88  % (23893)------------------------------
% 4.76/0.96  % (23840)Time limit reached!
% 4.76/0.96  % (23840)------------------------------
% 4.76/0.96  % (23840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/0.96  % (23840)Termination reason: Time limit
% 4.76/0.96  
% 4.76/0.96  % (23840)Memory used [KB]: 8059
% 4.76/0.96  % (23840)Time elapsed: 0.635 s
% 4.76/0.96  % (23840)------------------------------
% 4.76/0.96  % (23840)------------------------------
% 4.76/0.97  % (23895)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 5.23/0.99  % (23896)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.73/1.07  % (23875)Refutation found. Thanks to Tanya!
% 5.73/1.07  % SZS status Theorem for theBenchmark
% 5.73/1.07  % SZS output start Proof for theBenchmark
% 5.73/1.07  fof(f4189,plain,(
% 5.73/1.07    $false),
% 5.73/1.07    inference(avatar_sat_refutation,[],[f118,f123,f312,f3635,f4171,f4188])).
% 5.73/1.07  fof(f4188,plain,(
% 5.73/1.07    spl4_1 | ~spl4_76),
% 5.73/1.07    inference(avatar_contradiction_clause,[],[f4187])).
% 5.73/1.07  fof(f4187,plain,(
% 5.73/1.07    $false | (spl4_1 | ~spl4_76)),
% 5.73/1.07    inference(subsumption_resolution,[],[f4182,f117])).
% 5.73/1.07  fof(f117,plain,(
% 5.73/1.07    sK0 != sK1 | spl4_1),
% 5.73/1.07    inference(avatar_component_clause,[],[f115])).
% 5.73/1.07  fof(f115,plain,(
% 5.73/1.07    spl4_1 <=> sK0 = sK1),
% 5.73/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 5.73/1.07  fof(f4182,plain,(
% 5.73/1.07    sK0 = sK1 | ~spl4_76),
% 5.73/1.07    inference(duplicate_literal_removal,[],[f4178])).
% 5.73/1.07  fof(f4178,plain,(
% 5.73/1.07    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl4_76),
% 5.73/1.07    inference(resolution,[],[f4170,f113])).
% 5.73/1.07  fof(f113,plain,(
% 5.73/1.07    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 5.73/1.07    inference(equality_resolution,[],[f101])).
% 5.73/1.07  fof(f101,plain,(
% 5.73/1.07    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 5.73/1.07    inference(definition_unfolding,[],[f66,f82])).
% 5.73/1.07  fof(f82,plain,(
% 5.73/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f63,f81])).
% 5.73/1.07  fof(f81,plain,(
% 5.73/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f65,f80])).
% 5.73/1.07  fof(f80,plain,(
% 5.73/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f74,f79])).
% 5.73/1.07  fof(f79,plain,(
% 5.73/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f75,f76])).
% 5.73/1.07  fof(f76,plain,(
% 5.73/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f21])).
% 5.73/1.07  fof(f21,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 5.73/1.07  fof(f75,plain,(
% 5.73/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f20])).
% 5.73/1.07  fof(f20,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 5.73/1.07  fof(f74,plain,(
% 5.73/1.07    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f19])).
% 5.73/1.07  fof(f19,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 5.73/1.07  fof(f65,plain,(
% 5.73/1.07    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f18])).
% 5.73/1.07  fof(f18,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 5.73/1.07  fof(f63,plain,(
% 5.73/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f17])).
% 5.73/1.07  fof(f17,axiom,(
% 5.73/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 5.73/1.07  fof(f66,plain,(
% 5.73/1.07    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 5.73/1.07    inference(cnf_transformation,[],[f41])).
% 5.73/1.07  fof(f41,plain,(
% 5.73/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.73/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 5.73/1.07  fof(f40,plain,(
% 5.73/1.07    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 5.73/1.07    introduced(choice_axiom,[])).
% 5.73/1.07  fof(f39,plain,(
% 5.73/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.73/1.07    inference(rectify,[],[f38])).
% 5.73/1.07  fof(f38,plain,(
% 5.73/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.73/1.07    inference(flattening,[],[f37])).
% 5.73/1.07  fof(f37,plain,(
% 5.73/1.07    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.73/1.07    inference(nnf_transformation,[],[f27])).
% 5.73/1.07  fof(f27,plain,(
% 5.73/1.07    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 5.73/1.07    inference(ennf_transformation,[],[f12])).
% 5.73/1.07  fof(f12,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 5.73/1.07  fof(f4170,plain,(
% 5.73/1.07    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_76),
% 5.73/1.07    inference(avatar_component_clause,[],[f4168])).
% 5.73/1.07  fof(f4168,plain,(
% 5.73/1.07    spl4_76 <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 5.73/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 5.73/1.07  fof(f4171,plain,(
% 5.73/1.07    spl4_76 | ~spl4_71),
% 5.73/1.07    inference(avatar_split_clause,[],[f4157,f3630,f4168])).
% 5.73/1.07  fof(f3630,plain,(
% 5.73/1.07    spl4_71 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 5.73/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 5.73/1.07  fof(f4157,plain,(
% 5.73/1.07    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_71),
% 5.73/1.07    inference(superposition,[],[f108,f3632])).
% 5.73/1.07  fof(f3632,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl4_71),
% 5.73/1.07    inference(avatar_component_clause,[],[f3630])).
% 5.73/1.07  fof(f108,plain,(
% 5.73/1.07    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 5.73/1.07    inference(equality_resolution,[],[f107])).
% 5.73/1.07  fof(f107,plain,(
% 5.73/1.07    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 5.73/1.07    inference(equality_resolution,[],[f98])).
% 5.73/1.07  fof(f98,plain,(
% 5.73/1.07    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 5.73/1.07    inference(definition_unfolding,[],[f69,f82])).
% 5.73/1.07  fof(f69,plain,(
% 5.73/1.07    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.73/1.07    inference(cnf_transformation,[],[f41])).
% 5.73/1.07  fof(f3635,plain,(
% 5.73/1.07    spl4_71 | ~spl4_3),
% 5.73/1.07    inference(avatar_split_clause,[],[f3598,f309,f3630])).
% 5.73/1.07  fof(f309,plain,(
% 5.73/1.07    spl4_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 5.73/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 5.73/1.07  fof(f3598,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl4_3),
% 5.73/1.07    inference(superposition,[],[f311,f461])).
% 5.73/1.07  fof(f461,plain,(
% 5.73/1.07    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1) = k5_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 5.73/1.07    inference(superposition,[],[f85,f49])).
% 5.73/1.07  fof(f49,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f1])).
% 5.73/1.07  fof(f1,axiom,(
% 5.73/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.73/1.07  fof(f85,plain,(
% 5.73/1.07    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 5.73/1.07    inference(definition_unfolding,[],[f77,f78,f76,f84])).
% 5.73/1.07  fof(f84,plain,(
% 5.73/1.07    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f45,f83])).
% 5.73/1.07  fof(f83,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 5.73/1.07    inference(definition_unfolding,[],[f50,f82])).
% 5.73/1.07  fof(f50,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f16])).
% 5.73/1.07  fof(f16,axiom,(
% 5.73/1.07    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.73/1.07  fof(f45,plain,(
% 5.73/1.07    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.73/1.07    inference(cnf_transformation,[],[f15])).
% 5.73/1.07  fof(f15,axiom,(
% 5.73/1.07    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 5.73/1.07  fof(f78,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.73/1.07    inference(definition_unfolding,[],[f52,f51])).
% 5.73/1.07  fof(f51,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.73/1.07    inference(cnf_transformation,[],[f5])).
% 5.73/1.07  fof(f5,axiom,(
% 5.73/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.73/1.07  fof(f52,plain,(
% 5.73/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.73/1.07    inference(cnf_transformation,[],[f11])).
% 5.73/1.07  fof(f11,axiom,(
% 5.73/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.73/1.07  fof(f77,plain,(
% 5.73/1.07    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 5.73/1.07    inference(cnf_transformation,[],[f14])).
% 5.73/1.07  fof(f14,axiom,(
% 5.73/1.07    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 5.73/1.07  fof(f311,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl4_3),
% 5.73/1.07    inference(avatar_component_clause,[],[f309])).
% 5.73/1.07  fof(f312,plain,(
% 5.73/1.07    spl4_3 | ~spl4_2),
% 5.73/1.07    inference(avatar_split_clause,[],[f307,f120,f309])).
% 5.73/1.07  fof(f120,plain,(
% 5.73/1.07    spl4_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 5.73/1.07    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 5.73/1.07  fof(f307,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl4_2),
% 5.73/1.07    inference(forward_demodulation,[],[f122,f49])).
% 5.73/1.07  fof(f122,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl4_2),
% 5.73/1.07    inference(avatar_component_clause,[],[f120])).
% 5.73/1.07  fof(f123,plain,(
% 5.73/1.07    spl4_2),
% 5.73/1.07    inference(avatar_split_clause,[],[f86,f120])).
% 5.73/1.07  fof(f86,plain,(
% 5.73/1.07    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 5.73/1.07    inference(definition_unfolding,[],[f42,f84,f78,f84,f84])).
% 5.73/1.07  fof(f42,plain,(
% 5.73/1.07    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 5.73/1.07    inference(cnf_transformation,[],[f29])).
% 5.73/1.07  fof(f29,plain,(
% 5.73/1.07    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 5.73/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).
% 5.73/1.07  fof(f28,plain,(
% 5.73/1.07    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 5.73/1.07    introduced(choice_axiom,[])).
% 5.73/1.07  fof(f25,plain,(
% 5.73/1.07    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 5.73/1.07    inference(ennf_transformation,[],[f23])).
% 5.73/1.07  fof(f23,negated_conjecture,(
% 5.73/1.07    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 5.73/1.07    inference(negated_conjecture,[],[f22])).
% 5.73/1.07  fof(f22,conjecture,(
% 5.73/1.07    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 5.73/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 5.73/1.07  fof(f118,plain,(
% 5.73/1.07    ~spl4_1),
% 5.73/1.07    inference(avatar_split_clause,[],[f43,f115])).
% 5.73/1.07  fof(f43,plain,(
% 5.73/1.07    sK0 != sK1),
% 5.73/1.07    inference(cnf_transformation,[],[f29])).
% 5.73/1.07  % SZS output end Proof for theBenchmark
% 5.73/1.07  % (23875)------------------------------
% 5.73/1.07  % (23875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.73/1.07  % (23875)Termination reason: Refutation
% 5.73/1.07  
% 5.73/1.07  % (23875)Memory used [KB]: 14839
% 5.73/1.07  % (23875)Time elapsed: 0.624 s
% 5.73/1.07  % (23875)------------------------------
% 5.73/1.07  % (23875)------------------------------
% 5.73/1.07  % (23832)Success in time 0.792 s
%------------------------------------------------------------------------------
