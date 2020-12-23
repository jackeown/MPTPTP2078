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
% DateTime   : Thu Dec  3 12:58:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 266 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  255 ( 588 expanded)
%              Number of equality atoms :  128 ( 365 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f148,f162,f171,f186,f195])).

fof(f195,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl6_5 ),
    inference(resolution,[],[f187,f80])).

fof(f80,plain,(
    ! [X4,X2,X3,X1] : sP0(X2,X1,X2,X3,X4) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP0(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f187,plain,
    ( ! [X0] : ~ sP0(sK2,k4_tarski(sK2,X0),sK2,sK2,sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f185,f104])).

fof(f104,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( r1_tarski(k2_enumset1(X9,X9,X9,X9),k2_enumset1(X13,X12,X11,X10))
      | ~ sP0(X9,X10,X11,X12,X13) ) ),
    inference(resolution,[],[f102,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_enumset1(X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP1(X0,X1,X2,X3,X4) )
      & ( sP1(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP1(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP0(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X6,X3,X2,X1,X0)
      | r2_hidden(X6,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP0(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ~ sP0(X5,X3,X2,X1,X0) )
            & ( sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f185,plain,
    ( ! [X1] : ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_5
  <=> ! [X1] : ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f186,plain,
    ( spl6_3
    | spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f182,f85,f184,f142])).

fof(f142,plain,
    ( spl6_3
  <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f85,plain,
    ( spl6_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1)))
        | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f49,f175])).

fof(f175,plain,
    ( ! [X1] : k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK4,X1)) = k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1))
    | ~ spl6_1 ),
    inference(superposition,[],[f78,f173])).

fof(f173,plain,
    ( sK2 = k4_tarski(sK2,sK4)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f37,f172])).

fof(f172,plain,
    ( sK2 = sK3
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f94,f87])).

fof(f87,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f94,plain,(
    k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f37,plain,(
    sK2 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & sK2 = k4_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK2
   => sK2 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f54,f71,f67,f67])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f171,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f163,f80])).

fof(f163,plain,
    ( ! [X0] : ~ sP0(sK2,k4_tarski(X0,sK2),sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f147,f104])).

fof(f147,plain,
    ( ! [X0] : ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_4
  <=> ! [X0] : ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f162,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_3 ),
    inference(superposition,[],[f111,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f110,f93])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f73,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))) = X0 ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f74,f73])).

fof(f74,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0))))) ),
    inference(definition_unfolding,[],[f42,f70,f71])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f148,plain,
    ( spl6_3
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f139,f89,f146,f142])).

fof(f89,plain,
    ( spl6_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2)))
        | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) )
    | ~ spl6_2 ),
    inference(superposition,[],[f50,f115])).

fof(f115,plain,
    ( ! [X0] : k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,X0),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2))
    | ~ spl6_2 ),
    inference(superposition,[],[f77,f98])).

fof(f98,plain,
    ( sK2 = k4_tarski(sK3,sK2)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f37,f97])).

fof(f97,plain,
    ( sK2 = sK4
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f96,f91])).

fof(f91,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,(
    k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[],[f48,f37])).

% (12564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f55,f67,f71,f67])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f38,f89,f85])).

fof(f38,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.51  % (12553)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12561)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12555)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12571)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (12558)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12561)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (12566)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (12549)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12549)Refutation not found, incomplete strategy% (12549)------------------------------
% 0.21/0.53  % (12549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12549)Memory used [KB]: 1663
% 0.21/0.53  % (12549)Time elapsed: 0.112 s
% 0.21/0.53  % (12549)------------------------------
% 0.21/0.53  % (12549)------------------------------
% 0.21/0.53  % (12551)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12566)Refutation not found, incomplete strategy% (12566)------------------------------
% 0.21/0.53  % (12566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12572)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (12573)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (12566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12566)Memory used [KB]: 10618
% 0.21/0.53  % (12566)Time elapsed: 0.115 s
% 0.21/0.53  % (12566)------------------------------
% 0.21/0.53  % (12566)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f92,f148,f162,f171,f186,f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~spl6_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    $false | ~spl6_5),
% 0.21/0.53    inference(resolution,[],[f187,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X4,X2,X3,X1] : (sP0(X2,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(equality_resolution,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | X0 != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.53    inference(rectify,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X5,X3,X2,X1,X0] : (sP0(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK2,k4_tarski(sK2,X0),sK2,sK2,sK2)) ) | ~spl6_5),
% 0.21/0.53    inference(resolution,[],[f185,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X12,X10,X13,X11,X9] : (r1_tarski(k2_enumset1(X9,X9,X9,X9),k2_enumset1(X13,X12,X11,X10)) | ~sP0(X9,X10,X11,X12,X13)) )),
% 0.21/0.53    inference(resolution,[],[f102,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(resolution,[],[f57,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(equality_resolution,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP1(X0,X1,X2,X3,X4)) & (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP1(X0,X1,X2,X3,X4))),
% 0.21/0.53    inference(definition_folding,[],[f21,f23,f22])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (sP1(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X6,X3,X2,X1,X0) | r2_hidden(X6,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sP0(sK5(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP0(X5,X3,X2,X1,X0)) & (sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1)))) ) | ~spl6_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    spl6_5 <=> ! [X1] : ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl6_3 | spl6_5 | ~spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f182,f85,f184,f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl6_3 <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl6_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1))) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)) ) | ~spl6_1),
% 0.21/0.53    inference(superposition,[],[f49,f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X1] : (k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK4,X1)) = k2_enumset1(sK2,sK2,sK2,k4_tarski(sK2,X1))) ) | ~spl6_1),
% 0.21/0.53    inference(superposition,[],[f78,f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    sK2 = k4_tarski(sK2,sK4) | ~spl6_1),
% 0.21/0.53    inference(backward_demodulation,[],[f37,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    sK2 = sK3 | ~spl6_1),
% 0.21/0.53    inference(backward_demodulation,[],[f94,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    sK2 = k1_mcart_1(sK2) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f85])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    k1_mcart_1(sK2) = sK3),
% 0.21/0.53    inference(superposition,[],[f47,f37])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    (sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f26,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK2 => sK2 = k4_tarski(sK3,sK4)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f54,f71,f67,f67])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    $false | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f163,f80])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK2,k4_tarski(X0,sK2),sK2,sK2,sK2)) ) | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f147,f104])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2)))) ) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl6_4 <=> ! [X0] : ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~spl6_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    $false | ~spl6_3),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~spl6_3),
% 0.21/0.53    inference(superposition,[],[f111,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f142])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f110,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 0.21/0.53    inference(backward_demodulation,[],[f72,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f67])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f68])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.21/0.53    inference(superposition,[],[f74,f73])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f70,f71])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl6_3 | spl6_4 | ~spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f139,f89,f146,f142])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl6_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2))) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)) ) | ~spl6_2),
% 0.21/0.54    inference(superposition,[],[f50,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,X0),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,k4_tarski(X0,sK2))) ) | ~spl6_2),
% 0.21/0.54    inference(superposition,[],[f77,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    sK2 = k4_tarski(sK3,sK2) | ~spl6_2),
% 0.21/0.54    inference(backward_demodulation,[],[f37,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    sK2 = sK4 | ~spl6_2),
% 0.21/0.54    inference(forward_demodulation,[],[f96,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    sK2 = k2_mcart_1(sK2) | ~spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f89])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    k2_mcart_1(sK2) = sK4),
% 0.21/0.54    inference(superposition,[],[f48,f37])).
% 0.21/0.54  % (12564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f67,f71,f67])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl6_1 | spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f89,f85])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12561)------------------------------
% 0.21/0.54  % (12561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12561)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12561)Memory used [KB]: 6268
% 0.21/0.54  % (12561)Time elapsed: 0.113 s
% 0.21/0.54  % (12561)------------------------------
% 0.21/0.54  % (12561)------------------------------
% 0.21/0.54  % (12552)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (12564)Refutation not found, incomplete strategy% (12564)------------------------------
% 0.21/0.54  % (12564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12564)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12564)Memory used [KB]: 6140
% 0.21/0.54  % (12564)Time elapsed: 0.002 s
% 0.21/0.54  % (12564)------------------------------
% 0.21/0.54  % (12564)------------------------------
% 0.21/0.54  % (12577)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12548)Success in time 0.176 s
%------------------------------------------------------------------------------
