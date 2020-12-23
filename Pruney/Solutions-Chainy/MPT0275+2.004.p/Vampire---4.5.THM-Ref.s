%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:26 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 171 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 ( 736 expanded)
%              Number of equality atoms :  138 ( 341 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f138,f139,f426,f574,f575,f674,f786,f791,f3185,f3190,f3193])).

fof(f3193,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3190,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3185,plain,
    ( spl6_96
    | spl6_97
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f3161,f788,f3182,f3178])).

fof(f3178,plain,
    ( spl6_96
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f3182,plain,
    ( spl6_97
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f788,plain,
    ( spl6_27
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f3161,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f3151])).

fof(f3151,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl6_27 ),
    inference(resolution,[],[f790,f124])).

fof(f124,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f86,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
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
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f790,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f788])).

fof(f791,plain,
    ( spl6_27
    | spl6_9 ),
    inference(avatar_split_clause,[],[f773,f220,f788])).

fof(f220,plain,
    ( spl6_9
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f773,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f222,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f222,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f220])).

fof(f786,plain,
    ( ~ spl6_26
    | spl6_9 ),
    inference(avatar_split_clause,[],[f774,f220,f783])).

fof(f783,plain,
    ( spl6_26
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f774,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f222,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f674,plain,
    ( ~ spl6_9
    | spl6_1 ),
    inference(avatar_split_clause,[],[f652,f126,f220])).

fof(f126,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f652,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f128,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f128,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f575,plain,
    ( spl6_3
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f547,f220,f134])).

fof(f134,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f547,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f119,f221,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f221,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f220])).

fof(f119,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f89,f78])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f574,plain,
    ( spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f550,f220,f130])).

fof(f130,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f550,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f123,f221,f69])).

fof(f123,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f87,f78])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f426,plain,
    ( spl6_9
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f404,f126,f220])).

fof(f404,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f127,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f127,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f139,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f98,f130,f126])).

fof(f98,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f52,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

% (7160)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f138,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f97,f134,f126])).

fof(f97,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f53,f94])).

fof(f53,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f137,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f96,f134,f130,f126])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f54,f94])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (7135)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (7127)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (7119)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (7122)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (7120)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (7121)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (7138)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (7130)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (7115)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (7129)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (7117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (7114)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (7140)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (7116)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (7113)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.54  % (7137)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (7139)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (7141)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.55  % (7134)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (7124)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (7131)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (7136)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (7133)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.55  % (7118)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.55  % (7132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (7123)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (7130)Refutation not found, incomplete strategy% (7130)------------------------------
% 1.50/0.56  % (7130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (7130)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (7130)Memory used [KB]: 10618
% 1.50/0.56  % (7130)Time elapsed: 0.154 s
% 1.50/0.56  % (7130)------------------------------
% 1.50/0.56  % (7130)------------------------------
% 1.50/0.56  % (7128)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.56  % (7125)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (7126)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.57  % (7142)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.40/0.67  % (7138)Refutation found. Thanks to Tanya!
% 2.40/0.67  % SZS status Theorem for theBenchmark
% 2.40/0.69  % SZS output start Proof for theBenchmark
% 2.40/0.69  fof(f3194,plain,(
% 2.40/0.69    $false),
% 2.40/0.69    inference(avatar_sat_refutation,[],[f137,f138,f139,f426,f574,f575,f674,f786,f791,f3185,f3190,f3193])).
% 2.40/0.69  fof(f3193,plain,(
% 2.40/0.69    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)),
% 2.40/0.69    introduced(theory_tautology_sat_conflict,[])).
% 2.40/0.69  fof(f3190,plain,(
% 2.40/0.69    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)),
% 2.40/0.69    introduced(theory_tautology_sat_conflict,[])).
% 2.40/0.69  fof(f3185,plain,(
% 2.40/0.69    spl6_96 | spl6_97 | ~spl6_27),
% 2.40/0.69    inference(avatar_split_clause,[],[f3161,f788,f3182,f3178])).
% 2.40/0.69  fof(f3178,plain,(
% 2.40/0.69    spl6_96 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 2.40/0.69  fof(f3182,plain,(
% 2.40/0.69    spl6_97 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 2.40/0.69  fof(f788,plain,(
% 2.40/0.69    spl6_27 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.40/0.69  fof(f3161,plain,(
% 2.40/0.69    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl6_27),
% 2.40/0.69    inference(duplicate_literal_removal,[],[f3151])).
% 2.40/0.69  fof(f3151,plain,(
% 2.40/0.69    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl6_27),
% 2.40/0.69    inference(resolution,[],[f790,f124])).
% 2.40/0.69  fof(f124,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 2.40/0.69    inference(equality_resolution,[],[f112])).
% 2.40/0.69  fof(f112,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.40/0.69    inference(definition_unfolding,[],[f86,f78])).
% 2.40/0.69  fof(f78,plain,(
% 2.40/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f18])).
% 2.40/0.69  fof(f18,axiom,(
% 2.40/0.69    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.40/0.69  fof(f86,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.40/0.69    inference(cnf_transformation,[],[f51])).
% 2.40/0.69  fof(f51,plain,(
% 2.40/0.69    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 2.40/0.69  fof(f50,plain,(
% 2.40/0.69    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.40/0.69    introduced(choice_axiom,[])).
% 2.40/0.69  fof(f49,plain,(
% 2.40/0.69    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.69    inference(rectify,[],[f48])).
% 2.40/0.69  fof(f48,plain,(
% 2.40/0.69    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.69    inference(flattening,[],[f47])).
% 2.40/0.69  fof(f47,plain,(
% 2.40/0.69    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.69    inference(nnf_transformation,[],[f28])).
% 2.40/0.69  fof(f28,plain,(
% 2.40/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.40/0.69    inference(ennf_transformation,[],[f14])).
% 2.40/0.69  fof(f14,axiom,(
% 2.40/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.40/0.69  fof(f790,plain,(
% 2.40/0.69    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_27),
% 2.40/0.69    inference(avatar_component_clause,[],[f788])).
% 2.40/0.69  fof(f791,plain,(
% 2.40/0.69    spl6_27 | spl6_9),
% 2.40/0.69    inference(avatar_split_clause,[],[f773,f220,f788])).
% 2.40/0.69  fof(f220,plain,(
% 2.40/0.69    spl6_9 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.40/0.69  fof(f773,plain,(
% 2.40/0.69    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_9),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f222,f70])).
% 2.40/0.69  fof(f70,plain,(
% 2.40/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f38])).
% 2.40/0.69  fof(f38,plain,(
% 2.40/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 2.40/0.69  fof(f37,plain,(
% 2.40/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.40/0.69    introduced(choice_axiom,[])).
% 2.40/0.69  fof(f36,plain,(
% 2.40/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.69    inference(rectify,[],[f35])).
% 2.40/0.69  fof(f35,plain,(
% 2.40/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.69    inference(nnf_transformation,[],[f27])).
% 2.40/0.69  fof(f27,plain,(
% 2.40/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.69    inference(ennf_transformation,[],[f1])).
% 2.40/0.69  fof(f1,axiom,(
% 2.40/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.69  fof(f222,plain,(
% 2.40/0.69    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_9),
% 2.40/0.69    inference(avatar_component_clause,[],[f220])).
% 2.40/0.69  fof(f786,plain,(
% 2.40/0.69    ~spl6_26 | spl6_9),
% 2.40/0.69    inference(avatar_split_clause,[],[f774,f220,f783])).
% 2.40/0.69  fof(f783,plain,(
% 2.40/0.69    spl6_26 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.40/0.69  fof(f774,plain,(
% 2.40/0.69    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | spl6_9),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f222,f71])).
% 2.40/0.69  fof(f71,plain,(
% 2.40/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f38])).
% 2.40/0.69  fof(f674,plain,(
% 2.40/0.69    ~spl6_9 | spl6_1),
% 2.40/0.69    inference(avatar_split_clause,[],[f652,f126,f220])).
% 2.40/0.69  fof(f126,plain,(
% 2.40/0.69    spl6_1 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.40/0.69  fof(f652,plain,(
% 2.40/0.69    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_1),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f128,f73])).
% 2.40/0.69  fof(f73,plain,(
% 2.40/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f39])).
% 2.40/0.69  fof(f39,plain,(
% 2.40/0.69    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.40/0.69    inference(nnf_transformation,[],[f4])).
% 2.40/0.69  fof(f4,axiom,(
% 2.40/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.40/0.69  fof(f128,plain,(
% 2.40/0.69    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_1),
% 2.40/0.69    inference(avatar_component_clause,[],[f126])).
% 2.40/0.69  fof(f575,plain,(
% 2.40/0.69    spl6_3 | ~spl6_9),
% 2.40/0.69    inference(avatar_split_clause,[],[f547,f220,f134])).
% 2.40/0.69  fof(f134,plain,(
% 2.40/0.69    spl6_3 <=> r2_hidden(sK1,sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.40/0.69  fof(f547,plain,(
% 2.40/0.69    r2_hidden(sK1,sK2) | ~spl6_9),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f119,f221,f69])).
% 2.40/0.69  fof(f69,plain,(
% 2.40/0.69    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f38])).
% 2.40/0.69  fof(f221,plain,(
% 2.40/0.69    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl6_9),
% 2.40/0.69    inference(avatar_component_clause,[],[f220])).
% 2.40/0.69  fof(f119,plain,(
% 2.40/0.69    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 2.40/0.69    inference(equality_resolution,[],[f118])).
% 2.40/0.69  fof(f118,plain,(
% 2.40/0.69    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 2.40/0.69    inference(equality_resolution,[],[f109])).
% 2.40/0.69  fof(f109,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.40/0.69    inference(definition_unfolding,[],[f89,f78])).
% 2.40/0.69  fof(f89,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.40/0.69    inference(cnf_transformation,[],[f51])).
% 2.40/0.69  fof(f574,plain,(
% 2.40/0.69    spl6_2 | ~spl6_9),
% 2.40/0.69    inference(avatar_split_clause,[],[f550,f220,f130])).
% 2.40/0.69  fof(f130,plain,(
% 2.40/0.69    spl6_2 <=> r2_hidden(sK0,sK2)),
% 2.40/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.40/0.69  fof(f550,plain,(
% 2.40/0.69    r2_hidden(sK0,sK2) | ~spl6_9),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f123,f221,f69])).
% 2.40/0.69  fof(f123,plain,(
% 2.40/0.69    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 2.40/0.69    inference(equality_resolution,[],[f122])).
% 2.40/0.69  fof(f122,plain,(
% 2.40/0.69    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 2.40/0.69    inference(equality_resolution,[],[f111])).
% 2.40/0.69  fof(f111,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.40/0.69    inference(definition_unfolding,[],[f87,f78])).
% 2.40/0.69  fof(f87,plain,(
% 2.40/0.69    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.40/0.69    inference(cnf_transformation,[],[f51])).
% 2.40/0.69  fof(f426,plain,(
% 2.40/0.69    spl6_9 | ~spl6_1),
% 2.40/0.69    inference(avatar_split_clause,[],[f404,f126,f220])).
% 2.40/0.69  fof(f404,plain,(
% 2.40/0.69    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl6_1),
% 2.40/0.69    inference(unit_resulting_resolution,[],[f127,f72])).
% 2.40/0.69  fof(f72,plain,(
% 2.40/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.40/0.69    inference(cnf_transformation,[],[f39])).
% 2.40/0.69  fof(f127,plain,(
% 2.40/0.69    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl6_1),
% 2.40/0.69    inference(avatar_component_clause,[],[f126])).
% 2.40/0.69  fof(f139,plain,(
% 2.40/0.69    spl6_1 | spl6_2),
% 2.40/0.69    inference(avatar_split_clause,[],[f98,f130,f126])).
% 2.40/0.69  fof(f98,plain,(
% 2.40/0.69    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    inference(definition_unfolding,[],[f52,f94])).
% 2.40/0.69  fof(f94,plain,(
% 2.40/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.40/0.69    inference(definition_unfolding,[],[f62,f78])).
% 2.40/0.69  fof(f62,plain,(
% 2.40/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.40/0.69    inference(cnf_transformation,[],[f17])).
% 2.40/0.69  fof(f17,axiom,(
% 2.40/0.69    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.40/0.69  fof(f52,plain,(
% 2.40/0.69    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.40/0.69    inference(cnf_transformation,[],[f32])).
% 2.40/0.69  fof(f32,plain,(
% 2.40/0.69    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.40/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 2.40/0.69  fof(f31,plain,(
% 2.40/0.69    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.40/0.69    introduced(choice_axiom,[])).
% 2.40/0.69  fof(f30,plain,(
% 2.40/0.69    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.40/0.69    inference(flattening,[],[f29])).
% 2.40/0.69  % (7160)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.40/0.69  fof(f29,plain,(
% 2.40/0.69    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.40/0.69    inference(nnf_transformation,[],[f24])).
% 2.40/0.69  fof(f24,plain,(
% 2.40/0.69    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.40/0.69    inference(ennf_transformation,[],[f22])).
% 2.40/0.69  fof(f22,negated_conjecture,(
% 2.40/0.69    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.40/0.69    inference(negated_conjecture,[],[f21])).
% 2.40/0.69  fof(f21,conjecture,(
% 2.40/0.69    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 2.40/0.69  fof(f138,plain,(
% 2.40/0.69    spl6_1 | spl6_3),
% 2.40/0.69    inference(avatar_split_clause,[],[f97,f134,f126])).
% 2.40/0.69  fof(f97,plain,(
% 2.40/0.69    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    inference(definition_unfolding,[],[f53,f94])).
% 2.40/0.69  fof(f53,plain,(
% 2.40/0.69    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.40/0.69    inference(cnf_transformation,[],[f32])).
% 2.40/0.69  fof(f137,plain,(
% 2.40/0.69    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 2.40/0.69    inference(avatar_split_clause,[],[f96,f134,f130,f126])).
% 2.40/0.69  fof(f96,plain,(
% 2.40/0.69    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.40/0.69    inference(definition_unfolding,[],[f54,f94])).
% 2.40/0.69  fof(f54,plain,(
% 2.40/0.69    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.40/0.69    inference(cnf_transformation,[],[f32])).
% 2.40/0.69  % SZS output end Proof for theBenchmark
% 2.40/0.69  % (7138)------------------------------
% 2.40/0.69  % (7138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.69  % (7138)Termination reason: Refutation
% 2.40/0.69  
% 2.40/0.69  % (7138)Memory used [KB]: 7803
% 2.40/0.69  % (7138)Time elapsed: 0.280 s
% 2.40/0.69  % (7138)------------------------------
% 2.40/0.69  % (7138)------------------------------
% 2.40/0.70  % (7110)Success in time 0.335 s
%------------------------------------------------------------------------------
