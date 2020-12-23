%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:00 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 685 expanded)
%              Number of leaves         :   33 ( 245 expanded)
%              Depth                    :   16
%              Number of atoms          :  449 (1659 expanded)
%              Number of equality atoms :  210 (1003 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f205,f216,f241,f347,f377,f378,f414,f494,f505,f510,f513,f531,f699,f737,f869,f1131])).

fof(f1131,plain,
    ( ~ spl10_1
    | ~ spl10_1
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1130,f866,f198,f198])).

fof(f198,plain,
    ( spl10_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f866,plain,
    ( spl10_28
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1130,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_1
    | ~ spl10_28 ),
    inference(trivial_inequality_removal,[],[f1129])).

fof(f1129,plain,
    ( sK1 != sK1
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_1
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f1128,f868])).

fof(f868,plain,
    ( sK1 = sK2
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1128,plain,
    ( sK1 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f146,f199])).

fof(f199,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f146,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f73,f141,f141])).

fof(f141,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f78,f137])).

fof(f137,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f85,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f109,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f124,f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f125,f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f126,f128])).

fof(f128,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f124,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f109,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f73,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f869,plain,
    ( spl10_28
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f854,f213,f198,f866])).

fof(f213,plain,
    ( spl10_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f854,plain,
    ( sK1 = sK2
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f214,f199])).

fof(f214,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f737,plain,
    ( ~ spl10_9
    | spl10_4
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f730,f696,f213,f374])).

fof(f374,plain,
    ( spl10_9
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f696,plain,
    ( spl10_24
  <=> sK0 = sK7(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f730,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl10_4
    | ~ spl10_24 ),
    inference(trivial_inequality_removal,[],[f729])).

fof(f729,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK0 != sK0
    | sK2 != sK2
    | spl10_4
    | ~ spl10_24 ),
    inference(superposition,[],[f557,f698])).

fof(f698,plain,
    ( sK0 = sK7(sK0,sK2)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f696])).

fof(f557,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7(sK0,X1),X1)
        | sK0 != sK7(sK0,X1)
        | sK2 != X1 )
    | spl10_4 ),
    inference(superposition,[],[f215,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK7(X0,X1) != X0
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f101,f141])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) != X0
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f215,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f699,plain,
    ( spl10_24
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f687,f238,f213,f696])).

fof(f238,plain,
    ( spl10_5
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f687,plain,
    ( sK0 = sK7(sK0,sK2)
    | spl10_4
    | ~ spl10_5 ),
    inference(trivial_inequality_removal,[],[f686])).

fof(f686,plain,
    ( sK0 = sK7(sK0,sK2)
    | sK2 != sK2
    | spl10_4
    | ~ spl10_5 ),
    inference(duplicate_literal_removal,[],[f684])).

fof(f684,plain,
    ( sK0 = sK7(sK0,sK2)
    | sK2 != sK2
    | sK0 = sK7(sK0,sK2)
    | spl10_4
    | ~ spl10_5 ),
    inference(resolution,[],[f556,f330])).

fof(f330,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | sK0 = X2 )
    | ~ spl10_5 ),
    inference(resolution,[],[f283,f187])).

fof(f187,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f98,f141])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f283,plain,
    ( ! [X9] :
        ( r2_hidden(X9,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X9,sK2) )
    | ~ spl10_5 ),
    inference(superposition,[],[f194,f240])).

fof(f240,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f238])).

fof(f194,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f119,f138])).

fof(f138,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f84,f137])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & ~ r2_hidden(sK9(X0,X1,X2),X0) )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( r2_hidden(sK9(X0,X1,X2),X1)
            | r2_hidden(sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & ~ r2_hidden(sK9(X0,X1,X2),X0) )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( r2_hidden(sK9(X0,X1,X2),X1)
          | r2_hidden(sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f556,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),X0)
        | sK0 = sK7(sK0,X0)
        | sK2 != X0 )
    | spl10_4 ),
    inference(superposition,[],[f215,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f100,f141])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f531,plain,
    ( spl10_6
    | ~ spl10_3
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f525,f411,f209,f300])).

fof(f300,plain,
    ( spl10_6
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f209,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f411,plain,
    ( spl10_12
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f525,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl10_3
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f520,f149])).

fof(f149,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f138])).

fof(f81,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f520,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl10_3
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f413,f210])).

fof(f210,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f209])).

fof(f413,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f411])).

fof(f513,plain,
    ( spl10_3
    | spl10_16
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f511,f507,f502,f209])).

fof(f502,plain,
    ( spl10_16
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f507,plain,
    ( spl10_17
  <=> sK0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f511,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl10_17 ),
    inference(superposition,[],[f79,f509])).

fof(f509,plain,
    ( sK0 = sK3(sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f507])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f510,plain,
    ( spl10_3
    | spl10_17
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f481,f238,f507,f209])).

fof(f481,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1
    | ~ spl10_5 ),
    inference(resolution,[],[f474,f79])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK0 = X0 )
    | ~ spl10_5 ),
    inference(resolution,[],[f284,f187])).

fof(f284,plain,
    ( ! [X10] :
        ( r2_hidden(X10,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X10,sK1) )
    | ~ spl10_5 ),
    inference(superposition,[],[f195,f240])).

fof(f195,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f118,f138])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f505,plain,
    ( ~ spl10_16
    | spl10_1
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f499,f491,f198,f502])).

fof(f491,plain,
    ( spl10_15
  <=> sK0 = sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f499,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl10_1
    | ~ spl10_15 ),
    inference(trivial_inequality_removal,[],[f497])).

fof(f497,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 != sK0
    | sK1 != sK1
    | spl10_1
    | ~ spl10_15 ),
    inference(superposition,[],[f207,f493])).

fof(f493,plain,
    ( sK0 = sK7(sK0,sK1)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f491])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7(sK0,X1),X1)
        | sK0 != sK7(sK0,X1)
        | sK1 != X1 )
    | spl10_1 ),
    inference(superposition,[],[f200,f155])).

fof(f200,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f494,plain,
    ( spl10_15
    | spl10_1
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f488,f238,f198,f491])).

fof(f488,plain,
    ( sK0 = sK7(sK0,sK1)
    | spl10_1
    | ~ spl10_5 ),
    inference(trivial_inequality_removal,[],[f487])).

fof(f487,plain,
    ( sK0 = sK7(sK0,sK1)
    | sK1 != sK1
    | spl10_1
    | ~ spl10_5 ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,
    ( sK0 = sK7(sK0,sK1)
    | sK0 = sK7(sK0,sK1)
    | sK1 != sK1
    | spl10_1
    | ~ spl10_5 ),
    inference(resolution,[],[f474,f206])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),X0)
        | sK0 = sK7(sK0,X0)
        | sK1 != X0 )
    | spl10_1 ),
    inference(superposition,[],[f200,f156])).

fof(f414,plain,
    ( spl10_12
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f382,f238,f202,f411])).

fof(f202,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f382,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1))
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f381,f178])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f123,f135,f135])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f381,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f240,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f202])).

fof(f378,plain,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2
    | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f377,plain,
    ( spl10_2
    | spl10_9
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f365,f344,f374,f202])).

fof(f344,plain,
    ( spl10_7
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f365,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl10_7 ),
    inference(superposition,[],[f79,f346])).

fof(f346,plain,
    ( sK0 = sK3(sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f344])).

fof(f347,plain,
    ( spl10_2
    | spl10_7
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f336,f238,f344,f202])).

fof(f336,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl10_5 ),
    inference(resolution,[],[f330,f79])).

fof(f241,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f147,f238])).

fof(f147,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f72,f141,f138])).

fof(f72,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f216,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f145,f213,f209])).

fof(f145,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f74,f141])).

fof(f74,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f205,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f144,f202,f198])).

fof(f144,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f75,f141])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (12597)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (12605)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (12620)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (12595)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (12604)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (12612)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (12620)Refutation not found, incomplete strategy% (12620)------------------------------
% 0.21/0.56  % (12620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12620)Memory used [KB]: 1663
% 0.21/0.56  % (12620)Time elapsed: 0.160 s
% 0.21/0.56  % (12620)------------------------------
% 0.21/0.56  % (12620)------------------------------
% 0.21/0.58  % (12615)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (12599)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.59  % (12607)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.68/0.60  % (12607)Refutation not found, incomplete strategy% (12607)------------------------------
% 1.68/0.60  % (12607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (12607)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (12607)Memory used [KB]: 10746
% 1.68/0.60  % (12607)Time elapsed: 0.167 s
% 1.68/0.60  % (12607)------------------------------
% 1.68/0.60  % (12607)------------------------------
% 1.68/0.61  % (12592)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.68/0.62  % (12613)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.68/0.62  % (12591)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.96/0.62  % (12602)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.96/0.62  % (12610)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.96/0.63  % (12593)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.96/0.63  % (12618)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.96/0.63  % (12609)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.96/0.63  % (12617)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.96/0.63  % (12608)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.96/0.63  % (12596)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.96/0.63  % (12616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.96/0.64  % (12600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.96/0.64  % (12601)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.96/0.65  % (12603)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.96/0.65  % (12598)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.96/0.65  % (12603)Refutation not found, incomplete strategy% (12603)------------------------------
% 1.96/0.65  % (12603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (12603)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.65  
% 1.96/0.65  % (12603)Memory used [KB]: 10618
% 1.96/0.65  % (12603)Time elapsed: 0.224 s
% 1.96/0.65  % (12603)------------------------------
% 1.96/0.65  % (12603)------------------------------
% 1.96/0.65  % (12606)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.96/0.65  % (12619)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.96/0.66  % (12611)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.96/0.66  % (12614)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.96/0.66  % (12589)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.37/0.75  % (12632)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.37/0.75  % (12601)Refutation found. Thanks to Tanya!
% 2.37/0.75  % SZS status Theorem for theBenchmark
% 2.37/0.75  % SZS output start Proof for theBenchmark
% 2.37/0.75  fof(f1132,plain,(
% 2.37/0.75    $false),
% 2.37/0.75    inference(avatar_sat_refutation,[],[f205,f216,f241,f347,f377,f378,f414,f494,f505,f510,f513,f531,f699,f737,f869,f1131])).
% 2.37/0.75  fof(f1131,plain,(
% 2.37/0.75    ~spl10_1 | ~spl10_1 | ~spl10_28),
% 2.37/0.75    inference(avatar_split_clause,[],[f1130,f866,f198,f198])).
% 2.37/0.75  fof(f198,plain,(
% 2.37/0.75    spl10_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.37/0.75  fof(f866,plain,(
% 2.37/0.75    spl10_28 <=> sK1 = sK2),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 2.37/0.75  fof(f1130,plain,(
% 2.37/0.75    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl10_1 | ~spl10_28)),
% 2.37/0.75    inference(trivial_inequality_removal,[],[f1129])).
% 2.37/0.75  fof(f1129,plain,(
% 2.37/0.75    sK1 != sK1 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl10_1 | ~spl10_28)),
% 2.37/0.75    inference(forward_demodulation,[],[f1128,f868])).
% 2.37/0.75  fof(f868,plain,(
% 2.37/0.75    sK1 = sK2 | ~spl10_28),
% 2.37/0.75    inference(avatar_component_clause,[],[f866])).
% 2.37/0.75  fof(f1128,plain,(
% 2.37/0.75    sK1 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl10_1),
% 2.37/0.75    inference(forward_demodulation,[],[f146,f199])).
% 2.37/0.75  fof(f199,plain,(
% 2.37/0.75    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl10_1),
% 2.37/0.75    inference(avatar_component_clause,[],[f198])).
% 2.37/0.75  fof(f146,plain,(
% 2.37/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    inference(definition_unfolding,[],[f73,f141,f141])).
% 2.37/0.75  fof(f141,plain,(
% 2.37/0.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f78,f137])).
% 2.37/0.75  fof(f137,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f85,f136])).
% 2.37/0.75  fof(f136,plain,(
% 2.37/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f109,f135])).
% 2.37/0.75  fof(f135,plain,(
% 2.37/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f124,f134])).
% 2.37/0.75  fof(f134,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f125,f133])).
% 2.37/0.75  fof(f133,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f126,f128])).
% 2.37/0.75  fof(f128,plain,(
% 2.37/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f30])).
% 2.37/0.75  fof(f30,axiom,(
% 2.37/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.37/0.75  fof(f126,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f29])).
% 2.37/0.75  fof(f29,axiom,(
% 2.37/0.75    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.37/0.75  fof(f125,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f28])).
% 2.37/0.75  fof(f28,axiom,(
% 2.37/0.75    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.37/0.75  fof(f124,plain,(
% 2.37/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f27])).
% 2.37/0.75  fof(f27,axiom,(
% 2.37/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.37/0.75  fof(f109,plain,(
% 2.37/0.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f26])).
% 2.37/0.75  fof(f26,axiom,(
% 2.37/0.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.37/0.75  fof(f85,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f25])).
% 2.37/0.75  fof(f25,axiom,(
% 2.37/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.37/0.75  fof(f78,plain,(
% 2.37/0.75    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f24])).
% 2.37/0.75  fof(f24,axiom,(
% 2.37/0.75    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.37/0.75  fof(f73,plain,(
% 2.37/0.75    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.37/0.75    inference(cnf_transformation,[],[f45])).
% 2.37/0.75  fof(f45,plain,(
% 2.37/0.75    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.37/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44])).
% 2.37/0.75  fof(f44,plain,(
% 2.37/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.37/0.75    introduced(choice_axiom,[])).
% 2.37/0.75  fof(f40,plain,(
% 2.37/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.37/0.75    inference(ennf_transformation,[],[f37])).
% 2.37/0.75  fof(f37,negated_conjecture,(
% 2.37/0.75    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.37/0.75    inference(negated_conjecture,[],[f36])).
% 2.37/0.75  fof(f36,conjecture,(
% 2.37/0.75    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.37/0.75  fof(f869,plain,(
% 2.37/0.75    spl10_28 | ~spl10_1 | ~spl10_4),
% 2.37/0.75    inference(avatar_split_clause,[],[f854,f213,f198,f866])).
% 2.37/0.75  fof(f213,plain,(
% 2.37/0.75    spl10_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.37/0.75  fof(f854,plain,(
% 2.37/0.75    sK1 = sK2 | (~spl10_1 | ~spl10_4)),
% 2.37/0.75    inference(forward_demodulation,[],[f214,f199])).
% 2.37/0.75  fof(f214,plain,(
% 2.37/0.75    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl10_4),
% 2.37/0.75    inference(avatar_component_clause,[],[f213])).
% 2.37/0.75  fof(f737,plain,(
% 2.37/0.75    ~spl10_9 | spl10_4 | ~spl10_24),
% 2.37/0.75    inference(avatar_split_clause,[],[f730,f696,f213,f374])).
% 2.37/0.75  fof(f374,plain,(
% 2.37/0.75    spl10_9 <=> r2_hidden(sK0,sK2)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.37/0.75  fof(f696,plain,(
% 2.37/0.75    spl10_24 <=> sK0 = sK7(sK0,sK2)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 2.37/0.75  fof(f730,plain,(
% 2.37/0.75    ~r2_hidden(sK0,sK2) | (spl10_4 | ~spl10_24)),
% 2.37/0.75    inference(trivial_inequality_removal,[],[f729])).
% 2.37/0.75  fof(f729,plain,(
% 2.37/0.75    ~r2_hidden(sK0,sK2) | sK0 != sK0 | sK2 != sK2 | (spl10_4 | ~spl10_24)),
% 2.37/0.75    inference(superposition,[],[f557,f698])).
% 2.37/0.75  fof(f698,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK2) | ~spl10_24),
% 2.37/0.75    inference(avatar_component_clause,[],[f696])).
% 2.37/0.75  fof(f557,plain,(
% 2.37/0.75    ( ! [X1] : (~r2_hidden(sK7(sK0,X1),X1) | sK0 != sK7(sK0,X1) | sK2 != X1) ) | spl10_4),
% 2.37/0.75    inference(superposition,[],[f215,f155])).
% 2.37/0.75  fof(f155,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f101,f141])).
% 2.37/0.75  fof(f101,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f57])).
% 2.37/0.75  fof(f57,plain,(
% 2.37/0.75    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.37/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f55,f56])).
% 2.37/0.75  fof(f56,plain,(
% 2.37/0.75    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 2.37/0.75    introduced(choice_axiom,[])).
% 2.37/0.75  fof(f55,plain,(
% 2.37/0.75    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.37/0.75    inference(rectify,[],[f54])).
% 2.37/0.75  fof(f54,plain,(
% 2.37/0.75    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.37/0.75    inference(nnf_transformation,[],[f17])).
% 2.37/0.75  fof(f17,axiom,(
% 2.37/0.75    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.37/0.75  fof(f215,plain,(
% 2.37/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl10_4),
% 2.37/0.75    inference(avatar_component_clause,[],[f213])).
% 2.37/0.75  fof(f699,plain,(
% 2.37/0.75    spl10_24 | spl10_4 | ~spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f687,f238,f213,f696])).
% 2.37/0.75  fof(f238,plain,(
% 2.37/0.75    spl10_5 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.37/0.75  fof(f687,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK2) | (spl10_4 | ~spl10_5)),
% 2.37/0.75    inference(trivial_inequality_removal,[],[f686])).
% 2.37/0.75  fof(f686,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK2) | sK2 != sK2 | (spl10_4 | ~spl10_5)),
% 2.37/0.75    inference(duplicate_literal_removal,[],[f684])).
% 2.37/0.75  fof(f684,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK2) | sK2 != sK2 | sK0 = sK7(sK0,sK2) | (spl10_4 | ~spl10_5)),
% 2.37/0.75    inference(resolution,[],[f556,f330])).
% 2.37/0.75  fof(f330,plain,(
% 2.37/0.75    ( ! [X2] : (~r2_hidden(X2,sK2) | sK0 = X2) ) | ~spl10_5),
% 2.37/0.75    inference(resolution,[],[f283,f187])).
% 2.37/0.75  fof(f187,plain,(
% 2.37/0.75    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 2.37/0.75    inference(equality_resolution,[],[f158])).
% 2.37/0.75  fof(f158,plain,(
% 2.37/0.75    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.37/0.75    inference(definition_unfolding,[],[f98,f141])).
% 2.37/0.75  fof(f98,plain,(
% 2.37/0.75    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.37/0.75    inference(cnf_transformation,[],[f57])).
% 2.37/0.75  fof(f283,plain,(
% 2.37/0.75    ( ! [X9] : (r2_hidden(X9,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X9,sK2)) ) | ~spl10_5),
% 2.37/0.75    inference(superposition,[],[f194,f240])).
% 2.37/0.75  fof(f240,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl10_5),
% 2.37/0.75    inference(avatar_component_clause,[],[f238])).
% 2.37/0.75  fof(f194,plain,(
% 2.37/0.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.37/0.75    inference(equality_resolution,[],[f175])).
% 2.37/0.75  fof(f175,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.37/0.75    inference(definition_unfolding,[],[f119,f138])).
% 2.37/0.75  fof(f138,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.37/0.75    inference(definition_unfolding,[],[f84,f137])).
% 2.37/0.75  fof(f84,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.37/0.75    inference(cnf_transformation,[],[f34])).
% 2.37/0.75  fof(f34,axiom,(
% 2.37/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.37/0.75  fof(f119,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.37/0.75    inference(cnf_transformation,[],[f71])).
% 2.37/0.75  fof(f71,plain,(
% 2.37/0.75    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK9(X0,X1,X2),X1) & ~r2_hidden(sK9(X0,X1,X2),X0)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.37/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f69,f70])).
% 2.37/0.75  fof(f70,plain,(
% 2.37/0.75    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK9(X0,X1,X2),X1) & ~r2_hidden(sK9(X0,X1,X2),X0)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 2.37/0.75    introduced(choice_axiom,[])).
% 2.37/0.75  fof(f69,plain,(
% 2.37/0.75    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.37/0.75    inference(rectify,[],[f68])).
% 2.37/0.75  fof(f68,plain,(
% 2.37/0.75    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.37/0.75    inference(flattening,[],[f67])).
% 2.37/0.75  fof(f67,plain,(
% 2.37/0.75    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.37/0.75    inference(nnf_transformation,[],[f2])).
% 2.37/0.75  fof(f2,axiom,(
% 2.37/0.75    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.37/0.75  fof(f556,plain,(
% 2.37/0.75    ( ! [X0] : (r2_hidden(sK7(sK0,X0),X0) | sK0 = sK7(sK0,X0) | sK2 != X0) ) | spl10_4),
% 2.37/0.75    inference(superposition,[],[f215,f156])).
% 2.37/0.75  fof(f156,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f100,f141])).
% 2.37/0.75  fof(f100,plain,(
% 2.37/0.75    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f57])).
% 2.37/0.75  fof(f531,plain,(
% 2.37/0.75    spl10_6 | ~spl10_3 | ~spl10_12),
% 2.37/0.75    inference(avatar_split_clause,[],[f525,f411,f209,f300])).
% 2.37/0.75  fof(f300,plain,(
% 2.37/0.75    spl10_6 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.37/0.75  fof(f209,plain,(
% 2.37/0.75    spl10_3 <=> k1_xboole_0 = sK1),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.37/0.75  fof(f411,plain,(
% 2.37/0.75    spl10_12 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1))),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 2.37/0.75  fof(f525,plain,(
% 2.37/0.75    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl10_3 | ~spl10_12)),
% 2.37/0.75    inference(forward_demodulation,[],[f520,f149])).
% 2.37/0.75  fof(f149,plain,(
% 2.37/0.75    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.37/0.75    inference(definition_unfolding,[],[f81,f138])).
% 2.37/0.75  fof(f81,plain,(
% 2.37/0.75    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.37/0.75    inference(cnf_transformation,[],[f39])).
% 2.37/0.75  fof(f39,plain,(
% 2.37/0.75    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.37/0.75    inference(rectify,[],[f4])).
% 2.37/0.75  fof(f4,axiom,(
% 2.37/0.75    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.37/0.75  fof(f520,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl10_3 | ~spl10_12)),
% 2.37/0.75    inference(backward_demodulation,[],[f413,f210])).
% 2.37/0.75  fof(f210,plain,(
% 2.37/0.75    k1_xboole_0 = sK1 | ~spl10_3),
% 2.37/0.75    inference(avatar_component_clause,[],[f209])).
% 2.37/0.75  fof(f413,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1)) | ~spl10_12),
% 2.37/0.75    inference(avatar_component_clause,[],[f411])).
% 2.37/0.75  fof(f513,plain,(
% 2.37/0.75    spl10_3 | spl10_16 | ~spl10_17),
% 2.37/0.75    inference(avatar_split_clause,[],[f511,f507,f502,f209])).
% 2.37/0.75  fof(f502,plain,(
% 2.37/0.75    spl10_16 <=> r2_hidden(sK0,sK1)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 2.37/0.75  fof(f507,plain,(
% 2.37/0.75    spl10_17 <=> sK0 = sK3(sK1)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 2.37/0.75  fof(f511,plain,(
% 2.37/0.75    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | ~spl10_17),
% 2.37/0.75    inference(superposition,[],[f79,f509])).
% 2.37/0.75  fof(f509,plain,(
% 2.37/0.75    sK0 = sK3(sK1) | ~spl10_17),
% 2.37/0.75    inference(avatar_component_clause,[],[f507])).
% 2.37/0.75  fof(f79,plain,(
% 2.37/0.75    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.37/0.75    inference(cnf_transformation,[],[f47])).
% 2.37/0.75  fof(f47,plain,(
% 2.37/0.75    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.37/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f46])).
% 2.37/0.75  fof(f46,plain,(
% 2.37/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.37/0.75    introduced(choice_axiom,[])).
% 2.37/0.75  fof(f41,plain,(
% 2.37/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.37/0.75    inference(ennf_transformation,[],[f6])).
% 2.37/0.75  fof(f6,axiom,(
% 2.37/0.75    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.37/0.75  fof(f510,plain,(
% 2.37/0.75    spl10_3 | spl10_17 | ~spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f481,f238,f507,f209])).
% 2.37/0.75  fof(f481,plain,(
% 2.37/0.75    sK0 = sK3(sK1) | k1_xboole_0 = sK1 | ~spl10_5),
% 2.37/0.75    inference(resolution,[],[f474,f79])).
% 2.37/0.75  fof(f474,plain,(
% 2.37/0.75    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) ) | ~spl10_5),
% 2.37/0.75    inference(resolution,[],[f284,f187])).
% 2.37/0.75  fof(f284,plain,(
% 2.37/0.75    ( ! [X10] : (r2_hidden(X10,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X10,sK1)) ) | ~spl10_5),
% 2.37/0.75    inference(superposition,[],[f195,f240])).
% 2.37/0.75  fof(f195,plain,(
% 2.37/0.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.37/0.75    inference(equality_resolution,[],[f176])).
% 2.37/0.75  fof(f176,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.37/0.75    inference(definition_unfolding,[],[f118,f138])).
% 2.37/0.75  fof(f118,plain,(
% 2.37/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.37/0.75    inference(cnf_transformation,[],[f71])).
% 2.37/0.75  fof(f505,plain,(
% 2.37/0.75    ~spl10_16 | spl10_1 | ~spl10_15),
% 2.37/0.75    inference(avatar_split_clause,[],[f499,f491,f198,f502])).
% 2.37/0.75  fof(f491,plain,(
% 2.37/0.75    spl10_15 <=> sK0 = sK7(sK0,sK1)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 2.37/0.75  fof(f499,plain,(
% 2.37/0.75    ~r2_hidden(sK0,sK1) | (spl10_1 | ~spl10_15)),
% 2.37/0.75    inference(trivial_inequality_removal,[],[f497])).
% 2.37/0.75  fof(f497,plain,(
% 2.37/0.75    ~r2_hidden(sK0,sK1) | sK0 != sK0 | sK1 != sK1 | (spl10_1 | ~spl10_15)),
% 2.37/0.75    inference(superposition,[],[f207,f493])).
% 2.37/0.75  fof(f493,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK1) | ~spl10_15),
% 2.37/0.75    inference(avatar_component_clause,[],[f491])).
% 2.37/0.75  fof(f207,plain,(
% 2.37/0.75    ( ! [X1] : (~r2_hidden(sK7(sK0,X1),X1) | sK0 != sK7(sK0,X1) | sK1 != X1) ) | spl10_1),
% 2.37/0.75    inference(superposition,[],[f200,f155])).
% 2.37/0.75  fof(f200,plain,(
% 2.37/0.75    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl10_1),
% 2.37/0.75    inference(avatar_component_clause,[],[f198])).
% 2.37/0.75  fof(f494,plain,(
% 2.37/0.75    spl10_15 | spl10_1 | ~spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f488,f238,f198,f491])).
% 2.37/0.75  fof(f488,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK1) | (spl10_1 | ~spl10_5)),
% 2.37/0.75    inference(trivial_inequality_removal,[],[f487])).
% 2.37/0.75  fof(f487,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK1) | sK1 != sK1 | (spl10_1 | ~spl10_5)),
% 2.37/0.75    inference(duplicate_literal_removal,[],[f486])).
% 2.37/0.75  fof(f486,plain,(
% 2.37/0.75    sK0 = sK7(sK0,sK1) | sK0 = sK7(sK0,sK1) | sK1 != sK1 | (spl10_1 | ~spl10_5)),
% 2.37/0.75    inference(resolution,[],[f474,f206])).
% 2.37/0.75  fof(f206,plain,(
% 2.37/0.75    ( ! [X0] : (r2_hidden(sK7(sK0,X0),X0) | sK0 = sK7(sK0,X0) | sK1 != X0) ) | spl10_1),
% 2.37/0.75    inference(superposition,[],[f200,f156])).
% 2.37/0.75  fof(f414,plain,(
% 2.37/0.75    spl10_12 | ~spl10_2 | ~spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f382,f238,f202,f411])).
% 2.37/0.75  fof(f202,plain,(
% 2.37/0.75    spl10_2 <=> k1_xboole_0 = sK2),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.37/0.75  fof(f382,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1,sK1)) | (~spl10_2 | ~spl10_5)),
% 2.37/0.75    inference(forward_demodulation,[],[f381,f178])).
% 2.37/0.75  fof(f178,plain,(
% 2.37/0.75    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 2.37/0.75    inference(definition_unfolding,[],[f123,f135,f135])).
% 2.37/0.75  fof(f123,plain,(
% 2.37/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.37/0.75    inference(cnf_transformation,[],[f18])).
% 2.37/0.75  fof(f18,axiom,(
% 2.37/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.37/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 2.37/0.75  fof(f381,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) | (~spl10_2 | ~spl10_5)),
% 2.37/0.75    inference(forward_demodulation,[],[f240,f203])).
% 2.37/0.75  fof(f203,plain,(
% 2.37/0.75    k1_xboole_0 = sK2 | ~spl10_2),
% 2.37/0.75    inference(avatar_component_clause,[],[f202])).
% 2.37/0.75  fof(f378,plain,(
% 2.37/0.75    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2 | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.37/0.75  fof(f377,plain,(
% 2.37/0.75    spl10_2 | spl10_9 | ~spl10_7),
% 2.37/0.75    inference(avatar_split_clause,[],[f365,f344,f374,f202])).
% 2.37/0.75  fof(f344,plain,(
% 2.37/0.75    spl10_7 <=> sK0 = sK3(sK2)),
% 2.37/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 2.37/0.75  fof(f365,plain,(
% 2.37/0.75    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl10_7),
% 2.37/0.75    inference(superposition,[],[f79,f346])).
% 2.37/0.75  fof(f346,plain,(
% 2.37/0.75    sK0 = sK3(sK2) | ~spl10_7),
% 2.37/0.75    inference(avatar_component_clause,[],[f344])).
% 2.37/0.75  fof(f347,plain,(
% 2.37/0.75    spl10_2 | spl10_7 | ~spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f336,f238,f344,f202])).
% 2.37/0.75  fof(f336,plain,(
% 2.37/0.75    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl10_5),
% 2.37/0.75    inference(resolution,[],[f330,f79])).
% 2.37/0.75  fof(f241,plain,(
% 2.37/0.75    spl10_5),
% 2.37/0.75    inference(avatar_split_clause,[],[f147,f238])).
% 2.37/0.75  fof(f147,plain,(
% 2.37/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.37/0.75    inference(definition_unfolding,[],[f72,f141,f138])).
% 2.37/0.75  fof(f72,plain,(
% 2.37/0.75    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.37/0.75    inference(cnf_transformation,[],[f45])).
% 2.37/0.75  fof(f216,plain,(
% 2.37/0.75    ~spl10_3 | ~spl10_4),
% 2.37/0.75    inference(avatar_split_clause,[],[f145,f213,f209])).
% 2.37/0.75  fof(f145,plain,(
% 2.37/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.37/0.75    inference(definition_unfolding,[],[f74,f141])).
% 2.37/0.75  fof(f74,plain,(
% 2.37/0.75    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.37/0.75    inference(cnf_transformation,[],[f45])).
% 2.37/0.75  fof(f205,plain,(
% 2.37/0.75    ~spl10_1 | ~spl10_2),
% 2.37/0.75    inference(avatar_split_clause,[],[f144,f202,f198])).
% 2.37/0.75  fof(f144,plain,(
% 2.37/0.75    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.37/0.75    inference(definition_unfolding,[],[f75,f141])).
% 2.37/0.75  fof(f75,plain,(
% 2.37/0.75    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.37/0.75    inference(cnf_transformation,[],[f45])).
% 2.37/0.75  % SZS output end Proof for theBenchmark
% 2.37/0.75  % (12601)------------------------------
% 2.37/0.75  % (12601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.37/0.75  % (12601)Termination reason: Refutation
% 2.37/0.75  
% 2.37/0.75  % (12601)Memory used [KB]: 11513
% 2.37/0.75  % (12601)Time elapsed: 0.330 s
% 2.37/0.75  % (12601)------------------------------
% 2.37/0.75  % (12601)------------------------------
% 3.05/0.78  % (12582)Success in time 0.41 s
%------------------------------------------------------------------------------
