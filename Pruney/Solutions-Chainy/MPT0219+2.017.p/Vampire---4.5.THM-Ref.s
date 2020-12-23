%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:22 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 235 expanded)
%              Number of leaves         :   20 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 ( 497 expanded)
%              Number of equality atoms :  130 ( 363 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f130,f141,f160,f168])).

fof(f168,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f96,f96,f96,f92,f159,f53])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f159,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_6
  <=> r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f92,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f21,f22])).

fof(f21,plain,(
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

fof(f96,plain,
    ( sK1 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f145,f138,f157])).

fof(f138,plain,
    ( spl5_5
  <=> sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f145,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f140,f89])).

fof(f89,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f140,plain,
    ( sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f141,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f133,f121,f138])).

fof(f121,plain,
    ( spl5_3
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f133,plain,
    ( sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f92,f123])).

fof(f123,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f130,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f111,f99,f121])).

fof(f99,plain,
    ( spl5_2
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f111,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f77,f101])).

fof(f101,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f77,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f42,f72,f67,f73,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f72])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f71])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f102,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f75,f99])).

fof(f75,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f36,f73,f67,f73,f73])).

fof(f36,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f97,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1243316225)
% 0.14/0.37  ipcrm: permission denied for id (1243348994)
% 0.14/0.37  ipcrm: permission denied for id (1243381763)
% 0.14/0.37  ipcrm: permission denied for id (1243414532)
% 0.14/0.37  ipcrm: permission denied for id (1243447301)
% 0.14/0.38  ipcrm: permission denied for id (1247150087)
% 0.14/0.38  ipcrm: permission denied for id (1243545608)
% 0.14/0.38  ipcrm: permission denied for id (1243578377)
% 0.14/0.38  ipcrm: permission denied for id (1247182858)
% 0.14/0.38  ipcrm: permission denied for id (1247215627)
% 0.14/0.38  ipcrm: permission denied for id (1247248396)
% 0.14/0.38  ipcrm: permission denied for id (1243742221)
% 0.14/0.38  ipcrm: permission denied for id (1247281166)
% 0.14/0.39  ipcrm: permission denied for id (1243807759)
% 0.14/0.39  ipcrm: permission denied for id (1247313936)
% 0.14/0.39  ipcrm: permission denied for id (1243873298)
% 0.14/0.39  ipcrm: permission denied for id (1243938836)
% 0.14/0.39  ipcrm: permission denied for id (1243971605)
% 0.14/0.39  ipcrm: permission denied for id (1244004374)
% 0.14/0.40  ipcrm: permission denied for id (1244037143)
% 0.14/0.40  ipcrm: permission denied for id (1244069912)
% 0.14/0.40  ipcrm: permission denied for id (1244102681)
% 0.14/0.40  ipcrm: permission denied for id (1244135450)
% 0.14/0.40  ipcrm: permission denied for id (1249345563)
% 0.21/0.40  ipcrm: permission denied for id (1249443869)
% 0.21/0.40  ipcrm: permission denied for id (1247543327)
% 0.21/0.41  ipcrm: permission denied for id (1249542177)
% 0.21/0.41  ipcrm: permission denied for id (1244332066)
% 0.21/0.41  ipcrm: permission denied for id (1244364835)
% 0.21/0.41  ipcrm: permission denied for id (1247641636)
% 0.21/0.41  ipcrm: permission denied for id (1244430373)
% 0.21/0.41  ipcrm: permission denied for id (1244463142)
% 0.21/0.41  ipcrm: permission denied for id (1250492455)
% 0.21/0.42  ipcrm: permission denied for id (1247707176)
% 0.21/0.42  ipcrm: permission denied for id (1244528681)
% 0.21/0.42  ipcrm: permission denied for id (1244561450)
% 0.21/0.42  ipcrm: permission denied for id (1247739947)
% 0.21/0.42  ipcrm: permission denied for id (1249607724)
% 0.21/0.42  ipcrm: permission denied for id (1247805485)
% 0.21/0.42  ipcrm: permission denied for id (1244725295)
% 0.21/0.42  ipcrm: permission denied for id (1244758064)
% 0.21/0.43  ipcrm: permission denied for id (1244790833)
% 0.21/0.43  ipcrm: permission denied for id (1247871026)
% 0.21/0.43  ipcrm: permission denied for id (1244856371)
% 0.21/0.43  ipcrm: permission denied for id (1247969333)
% 0.21/0.43  ipcrm: permission denied for id (1248002102)
% 0.21/0.43  ipcrm: permission denied for id (1245020216)
% 0.21/0.44  ipcrm: permission denied for id (1245052985)
% 0.21/0.44  ipcrm: permission denied for id (1245085754)
% 0.21/0.44  ipcrm: permission denied for id (1248067643)
% 0.21/0.44  ipcrm: permission denied for id (1245151292)
% 0.21/0.44  ipcrm: permission denied for id (1245184061)
% 0.21/0.44  ipcrm: permission denied for id (1245216830)
% 0.21/0.44  ipcrm: permission denied for id (1248100415)
% 0.21/0.44  ipcrm: permission denied for id (1245282368)
% 0.21/0.44  ipcrm: permission denied for id (1249738817)
% 0.21/0.45  ipcrm: permission denied for id (1245347906)
% 0.21/0.45  ipcrm: permission denied for id (1245380675)
% 0.21/0.45  ipcrm: permission denied for id (1248165956)
% 0.21/0.45  ipcrm: permission denied for id (1249771589)
% 0.21/0.45  ipcrm: permission denied for id (1245478982)
% 0.21/0.45  ipcrm: permission denied for id (1248231495)
% 0.21/0.45  ipcrm: permission denied for id (1245544520)
% 0.21/0.45  ipcrm: permission denied for id (1245577289)
% 0.21/0.46  ipcrm: permission denied for id (1250623562)
% 0.21/0.46  ipcrm: permission denied for id (1248297035)
% 0.21/0.46  ipcrm: permission denied for id (1245642828)
% 0.21/0.46  ipcrm: permission denied for id (1249837133)
% 0.21/0.46  ipcrm: permission denied for id (1245708366)
% 0.21/0.46  ipcrm: permission denied for id (1245741135)
% 0.21/0.46  ipcrm: permission denied for id (1245806673)
% 0.21/0.47  ipcrm: permission denied for id (1245839442)
% 0.21/0.47  ipcrm: permission denied for id (1248395347)
% 0.21/0.47  ipcrm: permission denied for id (1248428116)
% 0.21/0.47  ipcrm: permission denied for id (1245904981)
% 0.21/0.47  ipcrm: permission denied for id (1245937750)
% 0.21/0.47  ipcrm: permission denied for id (1249902679)
% 0.21/0.47  ipcrm: permission denied for id (1245970520)
% 0.21/0.47  ipcrm: permission denied for id (1246003289)
% 0.21/0.47  ipcrm: permission denied for id (1249935450)
% 0.21/0.48  ipcrm: permission denied for id (1248559195)
% 0.21/0.48  ipcrm: permission denied for id (1246101596)
% 0.21/0.48  ipcrm: permission denied for id (1250689117)
% 0.21/0.48  ipcrm: permission denied for id (1248624734)
% 0.21/0.48  ipcrm: permission denied for id (1246167135)
% 0.21/0.48  ipcrm: permission denied for id (1248657504)
% 0.21/0.48  ipcrm: permission denied for id (1246232673)
% 0.21/0.49  ipcrm: permission denied for id (1246298211)
% 0.21/0.49  ipcrm: permission denied for id (1246330980)
% 0.21/0.49  ipcrm: permission denied for id (1248723045)
% 0.21/0.49  ipcrm: permission denied for id (1250033766)
% 0.21/0.49  ipcrm: permission denied for id (1248788583)
% 0.21/0.49  ipcrm: permission denied for id (1246429288)
% 0.21/0.49  ipcrm: permission denied for id (1248821353)
% 0.21/0.49  ipcrm: permission denied for id (1250066538)
% 0.21/0.49  ipcrm: permission denied for id (1246462059)
% 0.21/0.50  ipcrm: permission denied for id (1248886892)
% 0.21/0.50  ipcrm: permission denied for id (1246527597)
% 0.21/0.50  ipcrm: permission denied for id (1246560366)
% 0.21/0.50  ipcrm: permission denied for id (1250099311)
% 0.21/0.50  ipcrm: permission denied for id (1246593136)
% 0.21/0.50  ipcrm: permission denied for id (1246625905)
% 0.21/0.50  ipcrm: permission denied for id (1246658674)
% 0.21/0.50  ipcrm: permission denied for id (1250754675)
% 0.21/0.51  ipcrm: permission denied for id (1250787444)
% 0.21/0.51  ipcrm: permission denied for id (1246756981)
% 0.21/0.51  ipcrm: permission denied for id (1249050742)
% 0.21/0.51  ipcrm: permission denied for id (1250197623)
% 0.21/0.51  ipcrm: permission denied for id (1249116280)
% 0.21/0.51  ipcrm: permission denied for id (1246855289)
% 0.21/0.51  ipcrm: permission denied for id (1250820218)
% 0.21/0.51  ipcrm: permission denied for id (1246920827)
% 0.21/0.51  ipcrm: permission denied for id (1249181820)
% 0.21/0.52  ipcrm: permission denied for id (1246986365)
% 0.21/0.52  ipcrm: permission denied for id (1247019134)
% 0.21/0.52  ipcrm: permission denied for id (1247051903)
% 1.24/0.66  % (21050)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.24/0.66  % (21038)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.24/0.66  % (21043)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.67  % (21036)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.67  % (21058)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.24/0.67  % (21044)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.24/0.67  % (21061)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.24/0.67  % (21046)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.24/0.67  % (21061)Refutation not found, incomplete strategy% (21061)------------------------------
% 1.24/0.67  % (21061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.67  % (21061)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.67  
% 1.24/0.67  % (21061)Memory used [KB]: 6140
% 1.24/0.67  % (21061)Time elapsed: 0.101 s
% 1.24/0.67  % (21061)------------------------------
% 1.24/0.67  % (21061)------------------------------
% 1.24/0.68  % (21044)Refutation found. Thanks to Tanya!
% 1.24/0.68  % SZS status Theorem for theBenchmark
% 1.24/0.68  % SZS output start Proof for theBenchmark
% 1.24/0.68  fof(f169,plain,(
% 1.24/0.68    $false),
% 1.24/0.68    inference(avatar_sat_refutation,[],[f97,f102,f130,f141,f160,f168])).
% 1.24/0.68  fof(f168,plain,(
% 1.24/0.68    spl5_1 | ~spl5_6),
% 1.24/0.68    inference(avatar_contradiction_clause,[],[f162])).
% 1.24/0.68  fof(f162,plain,(
% 1.24/0.68    $false | (spl5_1 | ~spl5_6)),
% 1.24/0.68    inference(unit_resulting_resolution,[],[f96,f96,f96,f92,f159,f53])).
% 1.24/0.68  fof(f53,plain,(
% 1.24/0.68    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.24/0.68    inference(cnf_transformation,[],[f34])).
% 1.24/0.68  fof(f34,plain,(
% 1.24/0.68    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.24/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.24/0.68  fof(f33,plain,(
% 1.24/0.68    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.24/0.68    introduced(choice_axiom,[])).
% 1.24/0.68  fof(f32,plain,(
% 1.24/0.68    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.24/0.68    inference(rectify,[],[f31])).
% 1.24/0.68  fof(f31,plain,(
% 1.24/0.68    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.24/0.68    inference(flattening,[],[f30])).
% 1.24/0.68  fof(f30,plain,(
% 1.24/0.68    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.24/0.68    inference(nnf_transformation,[],[f22])).
% 1.24/0.68  fof(f22,plain,(
% 1.24/0.68    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.24/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.24/0.68  fof(f159,plain,(
% 1.24/0.68    r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_6),
% 1.24/0.68    inference(avatar_component_clause,[],[f157])).
% 1.24/0.68  fof(f157,plain,(
% 1.24/0.68    spl5_6 <=> r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.24/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.24/0.68  fof(f92,plain,(
% 1.24/0.68    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.24/0.68    inference(equality_resolution,[],[f84])).
% 1.24/0.68  fof(f84,plain,(
% 1.24/0.68    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.24/0.68    inference(definition_unfolding,[],[f61,f71])).
% 1.24/0.68  fof(f71,plain,(
% 1.24/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f50,f70])).
% 1.24/0.68  fof(f70,plain,(
% 1.24/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f52,f69])).
% 1.24/0.68  fof(f69,plain,(
% 1.24/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f63,f68])).
% 1.24/0.68  fof(f68,plain,(
% 1.24/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f64,f65])).
% 1.24/0.68  fof(f65,plain,(
% 1.24/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f17])).
% 1.24/0.68  fof(f17,axiom,(
% 1.24/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.24/0.68  fof(f64,plain,(
% 1.24/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f16])).
% 1.24/0.68  fof(f16,axiom,(
% 1.24/0.68    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.24/0.68  fof(f63,plain,(
% 1.24/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f15])).
% 1.24/0.68  fof(f15,axiom,(
% 1.24/0.68    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.24/0.68  fof(f52,plain,(
% 1.24/0.68    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f14])).
% 1.24/0.68  fof(f14,axiom,(
% 1.24/0.68    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.24/0.68  fof(f50,plain,(
% 1.24/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f13])).
% 1.24/0.68  fof(f13,axiom,(
% 1.24/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.24/0.68  fof(f61,plain,(
% 1.24/0.68    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.24/0.68    inference(cnf_transformation,[],[f35])).
% 1.24/0.68  fof(f35,plain,(
% 1.24/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.24/0.68    inference(nnf_transformation,[],[f23])).
% 1.24/0.68  fof(f23,plain,(
% 1.24/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.24/0.68    inference(definition_folding,[],[f21,f22])).
% 1.24/0.68  fof(f21,plain,(
% 1.24/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.24/0.68    inference(ennf_transformation,[],[f7])).
% 1.24/0.68  fof(f7,axiom,(
% 1.24/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.24/0.68  fof(f96,plain,(
% 1.24/0.68    sK1 != sK2 | spl5_1),
% 1.24/0.68    inference(avatar_component_clause,[],[f94])).
% 1.24/0.68  fof(f94,plain,(
% 1.24/0.68    spl5_1 <=> sK1 = sK2),
% 1.24/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.24/0.68  fof(f160,plain,(
% 1.24/0.68    spl5_6 | ~spl5_5),
% 1.24/0.68    inference(avatar_split_clause,[],[f145,f138,f157])).
% 1.24/0.68  fof(f138,plain,(
% 1.24/0.68    spl5_5 <=> sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.24/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.24/0.68  fof(f145,plain,(
% 1.24/0.68    r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.24/0.68    inference(resolution,[],[f140,f89])).
% 1.24/0.68  fof(f89,plain,(
% 1.24/0.68    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.24/0.68    inference(equality_resolution,[],[f56])).
% 1.24/0.68  fof(f56,plain,(
% 1.24/0.68    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f34])).
% 1.24/0.68  fof(f140,plain,(
% 1.24/0.68    sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.24/0.68    inference(avatar_component_clause,[],[f138])).
% 1.24/0.68  fof(f141,plain,(
% 1.24/0.68    spl5_5 | ~spl5_3),
% 1.24/0.68    inference(avatar_split_clause,[],[f133,f121,f138])).
% 1.24/0.68  fof(f121,plain,(
% 1.24/0.68    spl5_3 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.24/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.24/0.68  fof(f133,plain,(
% 1.24/0.68    sP0(sK2,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_3),
% 1.24/0.68    inference(superposition,[],[f92,f123])).
% 1.24/0.68  fof(f123,plain,(
% 1.24/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl5_3),
% 1.24/0.68    inference(avatar_component_clause,[],[f121])).
% 1.24/0.68  fof(f130,plain,(
% 1.24/0.68    spl5_3 | ~spl5_2),
% 1.24/0.68    inference(avatar_split_clause,[],[f111,f99,f121])).
% 1.24/0.68  fof(f99,plain,(
% 1.24/0.68    spl5_2 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.24/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.24/0.68  fof(f111,plain,(
% 1.24/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl5_2),
% 1.24/0.68    inference(superposition,[],[f77,f101])).
% 1.24/0.68  fof(f101,plain,(
% 1.24/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl5_2),
% 1.24/0.68    inference(avatar_component_clause,[],[f99])).
% 1.24/0.68  fof(f77,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.24/0.68    inference(definition_unfolding,[],[f42,f72,f67,f73,f73])).
% 1.24/0.68  fof(f73,plain,(
% 1.24/0.68    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f38,f72])).
% 1.24/0.68  fof(f38,plain,(
% 1.24/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f11])).
% 1.24/0.68  fof(f11,axiom,(
% 1.24/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.68  fof(f67,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.24/0.68    inference(definition_unfolding,[],[f43,f41])).
% 1.24/0.68  fof(f41,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.68    inference(cnf_transformation,[],[f2])).
% 1.24/0.68  fof(f2,axiom,(
% 1.24/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.68  fof(f43,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.24/0.68    inference(cnf_transformation,[],[f6])).
% 1.24/0.68  fof(f6,axiom,(
% 1.24/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.24/0.68  fof(f72,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.24/0.68    inference(definition_unfolding,[],[f40,f71])).
% 1.24/0.68  fof(f40,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.24/0.68    inference(cnf_transformation,[],[f12])).
% 1.24/0.68  fof(f12,axiom,(
% 1.24/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.68  fof(f42,plain,(
% 1.24/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.24/0.68    inference(cnf_transformation,[],[f9])).
% 1.24/0.68  fof(f9,axiom,(
% 1.24/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.24/0.68  fof(f102,plain,(
% 1.24/0.68    spl5_2),
% 1.24/0.68    inference(avatar_split_clause,[],[f75,f99])).
% 1.24/0.68  fof(f75,plain,(
% 1.24/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.24/0.68    inference(definition_unfolding,[],[f36,f73,f67,f73,f73])).
% 1.24/0.68  fof(f36,plain,(
% 1.24/0.68    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.24/0.68    inference(cnf_transformation,[],[f25])).
% 1.24/0.68  fof(f25,plain,(
% 1.24/0.68    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.24/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f24])).
% 1.24/0.68  fof(f24,plain,(
% 1.24/0.68    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.24/0.68    introduced(choice_axiom,[])).
% 1.24/0.68  fof(f20,plain,(
% 1.24/0.68    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.24/0.68    inference(ennf_transformation,[],[f19])).
% 1.24/0.68  fof(f19,negated_conjecture,(
% 1.24/0.68    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.24/0.68    inference(negated_conjecture,[],[f18])).
% 1.24/0.68  fof(f18,conjecture,(
% 1.24/0.68    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.24/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.24/0.68  fof(f97,plain,(
% 1.24/0.68    ~spl5_1),
% 1.24/0.68    inference(avatar_split_clause,[],[f37,f94])).
% 1.24/0.68  fof(f37,plain,(
% 1.24/0.68    sK1 != sK2),
% 1.24/0.68    inference(cnf_transformation,[],[f25])).
% 1.24/0.68  % SZS output end Proof for theBenchmark
% 1.24/0.68  % (21044)------------------------------
% 1.24/0.68  % (21044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.68  % (21044)Termination reason: Refutation
% 1.24/0.68  
% 1.24/0.68  % (21044)Memory used [KB]: 10874
% 1.24/0.68  % (21044)Time elapsed: 0.122 s
% 1.24/0.68  % (21044)------------------------------
% 1.24/0.68  % (21044)------------------------------
% 1.24/0.68  % (21046)Refutation not found, incomplete strategy% (21046)------------------------------
% 1.24/0.68  % (21046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.68  % (21046)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.68  
% 1.24/0.68  % (21046)Memory used [KB]: 10618
% 1.24/0.68  % (21046)Time elapsed: 0.103 s
% 1.24/0.68  % (21046)------------------------------
% 1.24/0.68  % (21046)------------------------------
% 1.24/0.68  % (21050)Refutation not found, incomplete strategy% (21050)------------------------------
% 1.24/0.68  % (21050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.68  % (21050)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.68  
% 1.24/0.68  % (21050)Memory used [KB]: 10618
% 1.24/0.68  % (21050)Time elapsed: 0.120 s
% 1.24/0.68  % (21050)------------------------------
% 1.24/0.68  % (21050)------------------------------
% 1.24/0.68  % (21041)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.68  % (21054)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.24/0.68  % (21048)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.24/0.68  % (20900)Success in time 0.321 s
%------------------------------------------------------------------------------
