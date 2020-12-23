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
% DateTime   : Thu Dec  3 12:58:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 558 expanded)
%              Number of leaves         :   30 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  305 ( 948 expanded)
%              Number of equality atoms :  177 ( 723 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f162,f174,f189,f226,f241])).

fof(f241,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl6_7 ),
    inference(resolution,[],[f227,f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] : sP0(X2,X1,X2,X3,X4,X5,X6,X7) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f227,plain,
    ( ! [X0] : ~ sP0(sK2,k4_tarski(sK2,X0),sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f225,f131])).

fof(f131,plain,(
    ! [X21,X19,X17,X15,X22,X20,X18,X16] :
      ( r1_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15),k6_enumset1(X22,X22,X21,X20,X19,X18,X17,X16))
      | ~ sP0(X15,X16,X17,X18,X19,X20,X21,X22) ) ),
    inference(resolution,[],[f129,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (10687)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f129,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X7,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(resolution,[],[f67,f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f24,f26,f25])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X9,X7) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X8,X7) )
          & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X8,X7) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f225,plain,
    ( ! [X1] : ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl6_7
  <=> ! [X1] : ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f226,plain,
    ( spl6_3
    | spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f222,f110,f224,f156])).

fof(f156,plain,
    ( spl6_3
  <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f110,plain,
    ( spl6_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f222,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1)))
        | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f53,f211])).

fof(f211,plain,
    ( ! [X0] : k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X0))
    | ~ spl6_1 ),
    inference(superposition,[],[f97,f191])).

fof(f191,plain,
    ( sK2 = k4_tarski(sK2,sK4)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f41,f190])).

fof(f190,plain,
    ( sK2 = sK3
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f121,f112])).

fof(f112,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f121,plain,(
    k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f41,plain,(
    sK2 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & sK2 = k4_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK2
   => sK2 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f97,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f60,f88,f84,f84])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f189,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f175,f102])).

fof(f175,plain,
    ( ! [X0] : ~ sP0(sK2,k4_tarski(X0,sK2),sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f161,f131])).

fof(f161,plain,
    ( ! [X0] : ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_4
  <=> ! [X0] : ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f174,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_3 ),
    inference(superposition,[],[f120,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f120,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f119,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f45,f85,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f84])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f84])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f44,f86,f87])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f119,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f100,f91])).

fof(f91,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f88,f85,f88,f84])).

fof(f49,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f100,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f57,f88,f86,f88,f88])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f162,plain,
    ( spl6_3
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f153,f114,f160,f156])).

fof(f114,plain,
    ( spl6_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2)))
        | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) )
    | ~ spl6_2 ),
    inference(superposition,[],[f54,f143])).

fof(f143,plain,
    ( ! [X0] : k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2))
    | ~ spl6_2 ),
    inference(superposition,[],[f96,f125])).

fof(f125,plain,
    ( sK2 = k4_tarski(sK3,sK2)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f41,f124])).

fof(f124,plain,
    ( sK2 = sK4
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f123,f116])).

fof(f116,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f123,plain,(
    k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[],[f52,f41])).

fof(f52,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f61,f84,f88,f84])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f42,f114,f110])).

fof(f42,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (10673)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (10674)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (10662)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (10662)Refutation not found, incomplete strategy% (10662)------------------------------
% 0.21/0.51  % (10662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10662)Memory used [KB]: 1663
% 0.21/0.51  % (10662)Time elapsed: 0.095 s
% 0.21/0.51  % (10662)------------------------------
% 0.21/0.51  % (10662)------------------------------
% 0.21/0.51  % (10664)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10665)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10677)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (10675)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (10673)Refutation not found, incomplete strategy% (10673)------------------------------
% 0.21/0.51  % (10673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10673)Memory used [KB]: 10618
% 0.21/0.51  % (10673)Time elapsed: 0.108 s
% 0.21/0.51  % (10673)------------------------------
% 0.21/0.51  % (10673)------------------------------
% 0.21/0.52  % (10684)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (10676)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (10663)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10672)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10670)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10691)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (10677)Refutation not found, incomplete strategy% (10677)------------------------------
% 0.21/0.52  % (10677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10677)Memory used [KB]: 6268
% 0.21/0.52  % (10677)Time elapsed: 0.003 s
% 0.21/0.52  % (10677)------------------------------
% 0.21/0.52  % (10677)------------------------------
% 0.21/0.52  % (10667)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (10672)Refutation not found, incomplete strategy% (10672)------------------------------
% 0.21/0.52  % (10672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10672)Memory used [KB]: 10618
% 0.21/0.52  % (10672)Time elapsed: 0.106 s
% 0.21/0.52  % (10672)------------------------------
% 0.21/0.52  % (10672)------------------------------
% 0.21/0.53  % (10674)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f117,f162,f174,f189,f226,f241])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ~spl6_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    $false | ~spl6_7),
% 0.21/0.53    inference(resolution,[],[f227,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X7,X5,X3,X1] : (sP0(X2,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.21/0.53    inference(equality_resolution,[],[f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | X0 != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(rectify,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : (sP0(X8,X6,X5,X4,X3,X2,X1,X0) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK2,k4_tarski(sK2,X0),sK2,sK2,sK2,sK2,sK2,sK2)) ) | ~spl6_7),
% 0.21/0.53    inference(resolution,[],[f225,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X21,X19,X17,X15,X22,X20,X18,X16] : (r1_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15),k6_enumset1(X22,X22,X21,X20,X19,X18,X17,X16)) | ~sP0(X15,X16,X17,X18,X19,X20,X21,X22)) )),
% 0.21/0.53    inference(resolution,[],[f129,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f56,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f59,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f62,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f63,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f64,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  % (10687)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X7,X7,X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.21/0.53    inference(resolution,[],[f67,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.53    inference(equality_resolution,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.21/0.53    inference(definition_unfolding,[],[f78,f65])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.53    inference(definition_folding,[],[f24,f26,f25])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X7)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1)))) ) | ~spl6_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f224])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    spl6_7 <=> ! [X1] : ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl6_3 | spl6_7 | ~spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f222,f110,f224,f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    spl6_3 <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl6_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X1))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ) | ~spl6_1),
% 0.21/0.53    inference(superposition,[],[f53,f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ( ! [X0] : (k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK2,X0))) ) | ~spl6_1),
% 0.21/0.53    inference(superposition,[],[f97,f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    sK2 = k4_tarski(sK2,sK4) | ~spl6_1),
% 0.21/0.53    inference(backward_demodulation,[],[f41,f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    sK2 = sK3 | ~spl6_1),
% 0.21/0.53    inference(backward_demodulation,[],[f121,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    sK2 = k1_mcart_1(sK2) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    k1_mcart_1(sK2) = sK3),
% 0.21/0.53    inference(superposition,[],[f51,f41])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    (sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK2 => sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f20])).
% 0.21/0.53  fof(f20,conjecture,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f60,f88,f84,f84])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    $false | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f175,f102])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK2,k4_tarski(X0,sK2),sK2,sK2,sK2,sK2,sK2,sK2)) ) | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f161,f131])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2)))) ) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl6_4 <=> ! [X0] : ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ~spl6_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    $false | ~spl6_3),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~spl6_3),
% 0.21/0.53    inference(superposition,[],[f120,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f156])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f119,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f89,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f85,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f84])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f84])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f86,f87])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f50,f85])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f100,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f88,f85,f88,f84])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.21/0.53    inference(equality_resolution,[],[f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f57,f88,f86,f88,f88])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl6_3 | spl6_4 | ~spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f153,f114,f160,f156])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl6_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ) | ~spl6_2),
% 0.21/0.53    inference(superposition,[],[f54,f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X0] : (k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(X0,sK2))) ) | ~spl6_2),
% 0.21/0.53    inference(superposition,[],[f96,f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    sK2 = k4_tarski(sK3,sK2) | ~spl6_2),
% 0.21/0.53    inference(backward_demodulation,[],[f41,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    sK2 = sK4 | ~spl6_2),
% 0.21/0.53    inference(forward_demodulation,[],[f123,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    sK2 = k2_mcart_1(sK2) | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f114])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    k2_mcart_1(sK2) = sK4),
% 0.21/0.53    inference(superposition,[],[f52,f41])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f61,f84,f88,f84])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl6_1 | spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f114,f110])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10674)------------------------------
% 0.21/0.53  % (10674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10674)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10674)Memory used [KB]: 6396
% 0.21/0.53  % (10674)Time elapsed: 0.122 s
% 0.21/0.53  % (10674)------------------------------
% 0.21/0.53  % (10674)------------------------------
% 0.21/0.53  % (10661)Success in time 0.168 s
%------------------------------------------------------------------------------
