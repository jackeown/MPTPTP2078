%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:17 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 535 expanded)
%              Number of leaves         :   33 ( 187 expanded)
%              Depth                    :   13
%              Number of atoms          :  329 ( 897 expanded)
%              Number of equality atoms :  201 ( 664 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f122,f138,f393,f548,f620,f3108,f3249])).

fof(f3249,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f3245,f3106,f104,f100])).

fof(f100,plain,
    ( spl5_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f104,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3106,plain,
    ( spl5_32
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f3245,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | ~ spl5_32 ),
    inference(resolution,[],[f3188,f95])).

fof(f95,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f3188,plain,
    ( ! [X19] :
        ( ~ r2_hidden(X19,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3))
        | sK2 = X19
        | sK3 = X19 )
    | ~ spl5_32 ),
    inference(duplicate_literal_removal,[],[f3186])).

fof(f3186,plain,
    ( ! [X19] :
        ( ~ r2_hidden(X19,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3))
        | sK2 = X19
        | sK2 = X19
        | sK3 = X19 )
    | ~ spl5_32 ),
    inference(superposition,[],[f98,f3107])).

fof(f3107,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f3106])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3108,plain,
    ( spl5_32
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f3104,f618,f3106])).

fof(f618,plain,
    ( spl5_15
  <=> k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f3104,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f3103,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f52,f71,f71])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f3103,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f3101,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f3101,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f83,f619])).

fof(f619,plain,
    ( k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f618])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f56,f70,f48,f71,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f620,plain,
    ( spl5_15
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f616,f546,f120,f618])).

fof(f120,plain,
    ( spl5_4
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f546,plain,
    ( spl5_14
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f616,plain,
    ( k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f615,f215])).

fof(f215,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_4 ),
    inference(superposition,[],[f180,f212])).

fof(f212,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f206,f40])).

fof(f206,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f74,f180])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f180,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(X6,k4_xboole_0(X6,k1_xboole_0))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f160,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f160,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f79,f147])).

fof(f147,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f146,f40])).

fof(f146,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f74,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f50,f50])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f615,plain,
    ( k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f598,f145])).

fof(f145,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f598,plain,
    ( k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_14 ),
    inference(superposition,[],[f74,f547])).

fof(f547,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f546])).

fof(f548,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f543,f391,f120,f546])).

fof(f391,plain,
    ( spl5_6
  <=> k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f543,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f534,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f73,f72])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f534,plain,
    ( ! [X22] :
        ( ~ r1_tarski(X22,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | k4_xboole_0(X22,k4_xboole_0(X22,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = X22 )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f516,f212])).

fof(f516,plain,
    ( ! [X22] :
        ( ~ r1_tarski(X22,k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0))
        | k4_xboole_0(X22,k4_xboole_0(X22,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = X22 )
    | ~ spl5_6 ),
    inference(superposition,[],[f467,f392])).

fof(f392,plain,
    ( k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f391])).

fof(f467,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k4_xboole_0(X3,k4_xboole_0(X3,X2)))
      | k4_xboole_0(X4,k4_xboole_0(X4,X2)) = X4 ) ),
    inference(superposition,[],[f140,f79])).

fof(f140,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f393,plain,
    ( spl5_6
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f389,f136,f120,f391])).

fof(f136,plain,
    ( spl5_5
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f389,plain,
    ( k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f388,f215])).

fof(f388,plain,
    ( k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f375,f145])).

fof(f375,plain,
    ( k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_5 ),
    inference(superposition,[],[f74,f137])).

fof(f137,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f131,f108,f136])).

fof(f108,plain,
    ( spl5_3
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f131,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_3 ),
    inference(resolution,[],[f80,f109])).

fof(f109,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f122,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f118,f120])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f77,f76])).

fof(f110,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f75,f108])).

fof(f75,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f37,f72,f72])).

fof(f37,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f106,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f104])).

fof(f38,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f100])).

fof(f39,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (9376)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (9362)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (9368)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (9360)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (9370)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (9356)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (9355)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (9354)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (9378)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (9354)Refutation not found, incomplete strategy% (9354)------------------------------
% 0.19/0.52  % (9354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (9354)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (9354)Memory used [KB]: 1663
% 0.19/0.52  % (9354)Time elapsed: 0.115 s
% 0.19/0.52  % (9354)------------------------------
% 0.19/0.52  % (9354)------------------------------
% 0.19/0.52  % (9357)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (9359)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (9369)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (9379)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (9374)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (9358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (9358)Refutation not found, incomplete strategy% (9358)------------------------------
% 0.19/0.53  % (9358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9358)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9358)Memory used [KB]: 6140
% 0.19/0.53  % (9358)Time elapsed: 0.125 s
% 0.19/0.53  % (9358)------------------------------
% 0.19/0.53  % (9358)------------------------------
% 0.19/0.53  % (9373)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (9371)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (9383)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (9380)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (9372)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (9375)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (9361)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (9366)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (9365)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (9363)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (9363)Refutation not found, incomplete strategy% (9363)------------------------------
% 0.19/0.54  % (9363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (9363)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (9363)Memory used [KB]: 10618
% 0.19/0.54  % (9363)Time elapsed: 0.139 s
% 0.19/0.54  % (9363)------------------------------
% 0.19/0.54  % (9363)------------------------------
% 0.19/0.54  % (9367)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.54  % (9364)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (9364)Refutation not found, incomplete strategy% (9364)------------------------------
% 0.19/0.54  % (9364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (9364)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (9364)Memory used [KB]: 10618
% 0.19/0.54  % (9364)Time elapsed: 0.138 s
% 0.19/0.54  % (9364)------------------------------
% 0.19/0.54  % (9364)------------------------------
% 0.19/0.55  % (9369)Refutation not found, incomplete strategy% (9369)------------------------------
% 0.19/0.55  % (9369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (9369)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (9369)Memory used [KB]: 6268
% 0.19/0.55  % (9369)Time elapsed: 0.148 s
% 0.19/0.55  % (9369)------------------------------
% 0.19/0.55  % (9369)------------------------------
% 0.19/0.55  % (9374)Refutation not found, incomplete strategy% (9374)------------------------------
% 0.19/0.55  % (9374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (9374)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (9374)Memory used [KB]: 10746
% 0.19/0.55  % (9374)Time elapsed: 0.148 s
% 0.19/0.55  % (9374)------------------------------
% 0.19/0.55  % (9374)------------------------------
% 0.19/0.55  % (9377)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.55  % (9381)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.55  % (9377)Refutation not found, incomplete strategy% (9377)------------------------------
% 0.19/0.55  % (9377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (9377)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (9377)Memory used [KB]: 1791
% 0.19/0.55  % (9377)Time elapsed: 0.150 s
% 0.19/0.55  % (9377)------------------------------
% 0.19/0.55  % (9377)------------------------------
% 0.19/0.55  % (9382)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.72/0.61  % (9362)Refutation not found, incomplete strategy% (9362)------------------------------
% 1.72/0.61  % (9362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (9362)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.62  
% 1.72/0.62  % (9362)Memory used [KB]: 11513
% 1.72/0.62  % (9362)Time elapsed: 0.189 s
% 1.72/0.62  % (9362)------------------------------
% 1.72/0.62  % (9362)------------------------------
% 1.72/0.62  % (9356)Refutation not found, incomplete strategy% (9356)------------------------------
% 1.72/0.62  % (9356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (9356)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.62  
% 1.72/0.62  % (9356)Memory used [KB]: 11641
% 1.72/0.62  % (9356)Time elapsed: 0.216 s
% 1.72/0.62  % (9356)------------------------------
% 1.72/0.62  % (9356)------------------------------
% 2.25/0.66  % (9384)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.25/0.66  % (9384)Refutation not found, incomplete strategy% (9384)------------------------------
% 2.25/0.66  % (9384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.66  % (9384)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.66  
% 2.25/0.66  % (9384)Memory used [KB]: 6140
% 2.25/0.66  % (9384)Time elapsed: 0.107 s
% 2.25/0.66  % (9384)------------------------------
% 2.25/0.66  % (9384)------------------------------
% 2.25/0.66  % (9385)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.25/0.68  % (9386)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.25/0.68  % (9388)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.25/0.68  % (9387)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.25/0.68  % (9390)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.25/0.68  % (9389)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.25/0.71  % (9379)Refutation not found, incomplete strategy% (9379)------------------------------
% 2.25/0.71  % (9379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.71  % (9379)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.71  
% 2.25/0.71  % (9379)Memory used [KB]: 7803
% 2.25/0.71  % (9379)Time elapsed: 0.311 s
% 2.25/0.71  % (9379)------------------------------
% 2.25/0.71  % (9379)------------------------------
% 2.73/0.75  % (9373)Refutation found. Thanks to Tanya!
% 2.73/0.75  % SZS status Theorem for theBenchmark
% 2.73/0.75  % SZS output start Proof for theBenchmark
% 2.73/0.75  fof(f3250,plain,(
% 2.73/0.75    $false),
% 2.73/0.75    inference(avatar_sat_refutation,[],[f102,f106,f110,f122,f138,f393,f548,f620,f3108,f3249])).
% 2.73/0.75  fof(f3249,plain,(
% 2.73/0.75    spl5_1 | spl5_2 | ~spl5_32),
% 2.73/0.75    inference(avatar_split_clause,[],[f3245,f3106,f104,f100])).
% 2.73/0.75  fof(f100,plain,(
% 2.73/0.75    spl5_1 <=> sK0 = sK3),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.73/0.75  fof(f104,plain,(
% 2.73/0.75    spl5_2 <=> sK0 = sK2),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.73/0.75  fof(f3106,plain,(
% 2.73/0.75    spl5_32 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.73/0.75  fof(f3245,plain,(
% 2.73/0.75    sK0 = sK2 | sK0 = sK3 | ~spl5_32),
% 2.73/0.75    inference(resolution,[],[f3188,f95])).
% 2.73/0.75  fof(f95,plain,(
% 2.73/0.75    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 2.73/0.75    inference(equality_resolution,[],[f94])).
% 2.73/0.75  fof(f94,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 2.73/0.75    inference(equality_resolution,[],[f89])).
% 2.73/0.75  fof(f89,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.73/0.75    inference(definition_unfolding,[],[f59,f71])).
% 2.73/0.75  fof(f71,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f53,f70])).
% 2.73/0.75  fof(f70,plain,(
% 2.73/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f55,f69])).
% 2.73/0.75  fof(f69,plain,(
% 2.73/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f65,f68])).
% 2.73/0.75  fof(f68,plain,(
% 2.73/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f66,f67])).
% 2.73/0.75  fof(f67,plain,(
% 2.73/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f19])).
% 2.73/0.75  fof(f19,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.73/0.75  fof(f66,plain,(
% 2.73/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f18])).
% 2.73/0.75  fof(f18,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.73/0.75  fof(f65,plain,(
% 2.73/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f17])).
% 2.73/0.75  fof(f17,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.73/0.75  fof(f55,plain,(
% 2.73/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f16])).
% 2.73/0.75  fof(f16,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.73/0.75  fof(f53,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f15])).
% 2.73/0.75  fof(f15,axiom,(
% 2.73/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.73/0.75  fof(f59,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.73/0.75    inference(cnf_transformation,[],[f36])).
% 2.73/0.75  fof(f36,plain,(
% 2.73/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.73/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 2.73/0.75  fof(f35,plain,(
% 2.73/0.75    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 2.73/0.75    introduced(choice_axiom,[])).
% 2.73/0.75  fof(f34,plain,(
% 2.73/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.73/0.75    inference(rectify,[],[f33])).
% 2.73/0.75  fof(f33,plain,(
% 2.73/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.73/0.75    inference(flattening,[],[f32])).
% 2.73/0.75  fof(f32,plain,(
% 2.73/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.73/0.75    inference(nnf_transformation,[],[f29])).
% 2.73/0.75  fof(f29,plain,(
% 2.73/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.73/0.75    inference(ennf_transformation,[],[f11])).
% 2.73/0.75  fof(f11,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.73/0.75  fof(f3188,plain,(
% 2.73/0.75    ( ! [X19] : (~r2_hidden(X19,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)) | sK2 = X19 | sK3 = X19) ) | ~spl5_32),
% 2.73/0.75    inference(duplicate_literal_removal,[],[f3186])).
% 2.73/0.75  fof(f3186,plain,(
% 2.73/0.75    ( ! [X19] : (~r2_hidden(X19,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3)) | sK2 = X19 | sK2 = X19 | sK3 = X19) ) | ~spl5_32),
% 2.73/0.75    inference(superposition,[],[f98,f3107])).
% 2.73/0.75  fof(f3107,plain,(
% 2.73/0.75    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3) | ~spl5_32),
% 2.73/0.75    inference(avatar_component_clause,[],[f3106])).
% 2.73/0.75  fof(f98,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.73/0.75    inference(equality_resolution,[],[f91])).
% 2.73/0.75  fof(f91,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.73/0.75    inference(definition_unfolding,[],[f57,f71])).
% 2.73/0.75  fof(f57,plain,(
% 2.73/0.75    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.73/0.75    inference(cnf_transformation,[],[f36])).
% 2.73/0.75  fof(f3108,plain,(
% 2.73/0.75    spl5_32 | ~spl5_15),
% 2.73/0.75    inference(avatar_split_clause,[],[f3104,f618,f3106])).
% 2.73/0.75  fof(f618,plain,(
% 2.73/0.75    spl5_15 <=> k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.73/0.75  fof(f3104,plain,(
% 2.73/0.75    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0,sK3) | ~spl5_15),
% 2.73/0.75    inference(forward_demodulation,[],[f3103,f81])).
% 2.73/0.75  fof(f81,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f52,f71,f71])).
% 2.73/0.75  fof(f52,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f20])).
% 2.73/0.75  fof(f20,axiom,(
% 2.73/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 2.73/0.75  fof(f3103,plain,(
% 2.73/0.75    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) | ~spl5_15),
% 2.73/0.75    inference(forward_demodulation,[],[f3101,f40])).
% 2.73/0.75  fof(f40,plain,(
% 2.73/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.73/0.75    inference(cnf_transformation,[],[f9])).
% 2.73/0.75  fof(f9,axiom,(
% 2.73/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.73/0.75  fof(f3101,plain,(
% 2.73/0.75    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0) | ~spl5_15),
% 2.73/0.75    inference(superposition,[],[f83,f619])).
% 2.73/0.75  fof(f619,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_15),
% 2.73/0.75    inference(avatar_component_clause,[],[f618])).
% 2.73/0.75  fof(f83,plain,(
% 2.73/0.75    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) )),
% 2.73/0.75    inference(definition_unfolding,[],[f56,f70,f48,f71,f73])).
% 2.73/0.75  fof(f73,plain,(
% 2.73/0.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f41,f72])).
% 2.73/0.75  fof(f72,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f47,f71])).
% 2.73/0.75  fof(f47,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f14])).
% 2.73/0.75  fof(f14,axiom,(
% 2.73/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.73/0.75  fof(f41,plain,(
% 2.73/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f13])).
% 2.73/0.75  fof(f13,axiom,(
% 2.73/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.73/0.75  fof(f48,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f10])).
% 2.73/0.75  fof(f10,axiom,(
% 2.73/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.73/0.75  fof(f56,plain,(
% 2.73/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f12])).
% 2.73/0.75  fof(f12,axiom,(
% 2.73/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.73/0.75  fof(f620,plain,(
% 2.73/0.75    spl5_15 | ~spl5_4 | ~spl5_14),
% 2.73/0.75    inference(avatar_split_clause,[],[f616,f546,f120,f618])).
% 2.73/0.75  fof(f120,plain,(
% 2.73/0.75    spl5_4 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.73/0.75  fof(f546,plain,(
% 2.73/0.75    spl5_14 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.73/0.75  fof(f616,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_4 | ~spl5_14)),
% 2.73/0.75    inference(forward_demodulation,[],[f615,f215])).
% 2.73/0.75  fof(f215,plain,(
% 2.73/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl5_4),
% 2.73/0.75    inference(superposition,[],[f180,f212])).
% 2.73/0.75  fof(f212,plain,(
% 2.73/0.75    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) ) | ~spl5_4),
% 2.73/0.75    inference(forward_demodulation,[],[f206,f40])).
% 2.73/0.75  fof(f206,plain,(
% 2.73/0.75    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) ) | ~spl5_4),
% 2.73/0.75    inference(superposition,[],[f74,f180])).
% 2.73/0.75  fof(f74,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.73/0.75    inference(definition_unfolding,[],[f49,f50])).
% 2.73/0.75  fof(f50,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f8])).
% 2.73/0.75  fof(f8,axiom,(
% 2.73/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.73/0.75  fof(f49,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f3])).
% 2.73/0.75  fof(f3,axiom,(
% 2.73/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.73/0.75  fof(f180,plain,(
% 2.73/0.75    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,k4_xboole_0(X6,k1_xboole_0))) ) | ~spl5_4),
% 2.73/0.75    inference(forward_demodulation,[],[f160,f121])).
% 2.73/0.75  fof(f121,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_4),
% 2.73/0.75    inference(avatar_component_clause,[],[f120])).
% 2.73/0.75  fof(f160,plain,(
% 2.73/0.75    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X6,k1_xboole_0))) )),
% 2.73/0.75    inference(superposition,[],[f79,f147])).
% 2.73/0.75  fof(f147,plain,(
% 2.73/0.75    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.73/0.75    inference(forward_demodulation,[],[f146,f40])).
% 2.73/0.75  fof(f146,plain,(
% 2.73/0.75    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 2.73/0.75    inference(superposition,[],[f74,f114])).
% 2.73/0.75  fof(f114,plain,(
% 2.73/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 2.73/0.75    inference(resolution,[],[f77,f42])).
% 2.73/0.75  fof(f42,plain,(
% 2.73/0.75    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.73/0.75    inference(cnf_transformation,[],[f26])).
% 2.73/0.75  fof(f26,plain,(
% 2.73/0.75    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.73/0.75    inference(ennf_transformation,[],[f7])).
% 2.73/0.75  fof(f7,axiom,(
% 2.73/0.75    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.73/0.75  fof(f77,plain,(
% 2.73/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.73/0.75    inference(definition_unfolding,[],[f44,f50])).
% 2.73/0.75  fof(f44,plain,(
% 2.73/0.75    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f4])).
% 2.73/0.75  fof(f4,axiom,(
% 2.73/0.75    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.73/0.75  fof(f79,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.73/0.75    inference(definition_unfolding,[],[f46,f50,f50])).
% 2.73/0.75  fof(f46,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f1])).
% 2.73/0.75  fof(f1,axiom,(
% 2.73/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.73/0.75  fof(f615,plain,(
% 2.73/0.75    k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_14),
% 2.73/0.75    inference(forward_demodulation,[],[f598,f145])).
% 2.73/0.75  fof(f145,plain,(
% 2.73/0.75    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.73/0.75    inference(superposition,[],[f74,f76])).
% 2.73/0.75  fof(f76,plain,(
% 2.73/0.75    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.73/0.75    inference(definition_unfolding,[],[f43,f50])).
% 2.73/0.75  fof(f43,plain,(
% 2.73/0.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.73/0.75    inference(cnf_transformation,[],[f24])).
% 2.73/0.75  fof(f24,plain,(
% 2.73/0.75    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.73/0.75    inference(rectify,[],[f2])).
% 2.73/0.75  fof(f2,axiom,(
% 2.73/0.75    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.73/0.75  fof(f598,plain,(
% 2.73/0.75    k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_14),
% 2.73/0.75    inference(superposition,[],[f74,f547])).
% 2.73/0.75  fof(f547,plain,(
% 2.73/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl5_14),
% 2.73/0.75    inference(avatar_component_clause,[],[f546])).
% 2.73/0.75  fof(f548,plain,(
% 2.73/0.75    spl5_14 | ~spl5_4 | ~spl5_6),
% 2.73/0.75    inference(avatar_split_clause,[],[f543,f391,f120,f546])).
% 2.73/0.75  fof(f391,plain,(
% 2.73/0.75    spl5_6 <=> k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.73/0.75  fof(f543,plain,(
% 2.73/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | (~spl5_4 | ~spl5_6)),
% 2.73/0.75    inference(resolution,[],[f534,f78])).
% 2.73/0.75  fof(f78,plain,(
% 2.73/0.75    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.73/0.75    inference(definition_unfolding,[],[f45,f73,f72])).
% 2.73/0.75  fof(f45,plain,(
% 2.73/0.75    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f21])).
% 2.73/0.75  fof(f21,axiom,(
% 2.73/0.75    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 2.73/0.75  fof(f534,plain,(
% 2.73/0.75    ( ! [X22] : (~r1_tarski(X22,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | k4_xboole_0(X22,k4_xboole_0(X22,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = X22) ) | (~spl5_4 | ~spl5_6)),
% 2.73/0.75    inference(forward_demodulation,[],[f516,f212])).
% 2.73/0.75  fof(f516,plain,(
% 2.73/0.75    ( ! [X22] : (~r1_tarski(X22,k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0)) | k4_xboole_0(X22,k4_xboole_0(X22,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = X22) ) | ~spl5_6),
% 2.73/0.75    inference(superposition,[],[f467,f392])).
% 2.73/0.75  fof(f392,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_6),
% 2.73/0.75    inference(avatar_component_clause,[],[f391])).
% 2.73/0.75  fof(f467,plain,(
% 2.73/0.75    ( ! [X4,X2,X3] : (~r1_tarski(X4,k4_xboole_0(X3,k4_xboole_0(X3,X2))) | k4_xboole_0(X4,k4_xboole_0(X4,X2)) = X4) )),
% 2.73/0.75    inference(superposition,[],[f140,f79])).
% 2.73/0.75  fof(f140,plain,(
% 2.73/0.75    ( ! [X4,X2,X3] : (~r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.73/0.75    inference(resolution,[],[f82,f80])).
% 2.73/0.75  fof(f80,plain,(
% 2.73/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.73/0.75    inference(definition_unfolding,[],[f51,f50])).
% 2.73/0.75  fof(f51,plain,(
% 2.73/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.73/0.75    inference(cnf_transformation,[],[f27])).
% 2.73/0.75  fof(f27,plain,(
% 2.73/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.73/0.75    inference(ennf_transformation,[],[f6])).
% 2.73/0.75  fof(f6,axiom,(
% 2.73/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.73/0.75  fof(f82,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 2.73/0.75    inference(definition_unfolding,[],[f54,f50])).
% 2.73/0.75  fof(f54,plain,(
% 2.73/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.73/0.75    inference(cnf_transformation,[],[f28])).
% 2.73/0.75  fof(f28,plain,(
% 2.73/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.73/0.75    inference(ennf_transformation,[],[f5])).
% 2.73/0.75  fof(f5,axiom,(
% 2.73/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.73/0.75  fof(f393,plain,(
% 2.73/0.75    spl5_6 | ~spl5_4 | ~spl5_5),
% 2.73/0.75    inference(avatar_split_clause,[],[f389,f136,f120,f391])).
% 2.73/0.75  fof(f136,plain,(
% 2.73/0.75    spl5_5 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.73/0.75  fof(f389,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_4 | ~spl5_5)),
% 2.73/0.75    inference(forward_demodulation,[],[f388,f215])).
% 2.73/0.75  fof(f388,plain,(
% 2.73/0.75    k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_5),
% 2.73/0.75    inference(forward_demodulation,[],[f375,f145])).
% 2.73/0.75  fof(f375,plain,(
% 2.73/0.75    k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_5),
% 2.73/0.75    inference(superposition,[],[f74,f137])).
% 2.73/0.75  fof(f137,plain,(
% 2.73/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl5_5),
% 2.73/0.75    inference(avatar_component_clause,[],[f136])).
% 2.73/0.75  fof(f138,plain,(
% 2.73/0.75    spl5_5 | ~spl5_3),
% 2.73/0.75    inference(avatar_split_clause,[],[f131,f108,f136])).
% 2.73/0.75  fof(f108,plain,(
% 2.73/0.75    spl5_3 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.73/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.73/0.75  fof(f131,plain,(
% 2.73/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl5_3),
% 2.73/0.75    inference(resolution,[],[f80,f109])).
% 2.73/0.75  fof(f109,plain,(
% 2.73/0.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_3),
% 2.73/0.75    inference(avatar_component_clause,[],[f108])).
% 2.73/0.75  fof(f122,plain,(
% 2.73/0.75    spl5_4),
% 2.73/0.75    inference(avatar_split_clause,[],[f118,f120])).
% 2.73/0.75  fof(f118,plain,(
% 2.73/0.75    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.73/0.75    inference(resolution,[],[f115,f42])).
% 2.73/0.75  fof(f115,plain,(
% 2.73/0.75    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) )),
% 2.73/0.75    inference(superposition,[],[f77,f76])).
% 2.73/0.75  fof(f110,plain,(
% 2.73/0.75    spl5_3),
% 2.73/0.75    inference(avatar_split_clause,[],[f75,f108])).
% 2.73/0.75  fof(f75,plain,(
% 2.73/0.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.73/0.75    inference(definition_unfolding,[],[f37,f72,f72])).
% 2.73/0.75  fof(f37,plain,(
% 2.73/0.75    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.73/0.75    inference(cnf_transformation,[],[f31])).
% 2.73/0.75  fof(f31,plain,(
% 2.73/0.75    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.73/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f30])).
% 2.73/0.75  fof(f30,plain,(
% 2.73/0.75    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 2.73/0.75    introduced(choice_axiom,[])).
% 2.73/0.75  fof(f25,plain,(
% 2.73/0.75    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.73/0.75    inference(ennf_transformation,[],[f23])).
% 2.73/0.75  fof(f23,negated_conjecture,(
% 2.73/0.75    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.73/0.75    inference(negated_conjecture,[],[f22])).
% 2.73/0.75  fof(f22,conjecture,(
% 2.73/0.75    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.73/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 2.73/0.75  fof(f106,plain,(
% 2.73/0.75    ~spl5_2),
% 2.73/0.75    inference(avatar_split_clause,[],[f38,f104])).
% 2.73/0.75  fof(f38,plain,(
% 2.73/0.75    sK0 != sK2),
% 2.73/0.75    inference(cnf_transformation,[],[f31])).
% 2.73/0.75  fof(f102,plain,(
% 2.73/0.75    ~spl5_1),
% 2.73/0.75    inference(avatar_split_clause,[],[f39,f100])).
% 2.73/0.75  fof(f39,plain,(
% 2.73/0.75    sK0 != sK3),
% 2.73/0.75    inference(cnf_transformation,[],[f31])).
% 2.73/0.75  % SZS output end Proof for theBenchmark
% 2.73/0.75  % (9373)------------------------------
% 2.73/0.75  % (9373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.75  % (9373)Termination reason: Refutation
% 2.73/0.75  
% 2.73/0.75  % (9373)Memory used [KB]: 13048
% 2.73/0.75  % (9373)Time elapsed: 0.325 s
% 2.73/0.75  % (9373)------------------------------
% 2.73/0.75  % (9373)------------------------------
% 2.73/0.75  % (9353)Success in time 0.39 s
%------------------------------------------------------------------------------
