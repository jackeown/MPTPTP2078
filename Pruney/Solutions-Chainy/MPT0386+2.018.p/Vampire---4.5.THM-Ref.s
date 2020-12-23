%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 119 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 ( 380 expanded)
%              Number of equality atoms :   38 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f86,f153,f158,f173,f178,f181])).

fof(f181,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl10_7 ),
    inference(resolution,[],[f168,f37])).

fof(f37,plain,(
    ~ r1_tarski(k1_setfam_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k1_setfam_1(sK3),sK2)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),X0)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK3),sK2)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f168,plain,
    ( r1_tarski(k1_setfam_1(sK3),sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl10_7
  <=> r1_tarski(k1_setfam_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f178,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl10_8 ),
    inference(resolution,[],[f172,f36])).

fof(f36,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f172,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_8
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f173,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f160,f151,f170,f166])).

fof(f151,plain,
    ( spl10_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f160,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r1_tarski(k1_setfam_1(sK3),sK2)
    | ~ spl10_6 ),
    inference(resolution,[],[f152,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f158,plain,
    ( ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(resolution,[],[f154,f83])).

fof(f83,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f154,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f36,f149])).

fof(f149,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f153,plain,
    ( spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f143,f151,f147])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k1_xboole_0 = sK3
      | r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0) ) ),
    inference(resolution,[],[f107,f37])).

fof(f107,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k1_setfam_1(X5),X6)
      | ~ r2_hidden(X7,X5)
      | k1_xboole_0 = X5
      | r2_hidden(sK9(k1_setfam_1(X5),X6),X7) ) ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(X1))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f98,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f11,f15,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( k1_setfam_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(k1_setfam_1(X1),X1)
      | ~ r2_hidden(X2,k1_setfam_1(X1))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X1] :
      ( sP0(X1,k1_setfam_1(X1))
      | ~ sP1(k1_setfam_1(X1),X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_setfam_1(X1) != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_setfam_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( ( k1_setfam_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k1_setfam_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X7,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(X5,X7) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
              & r2_hidden(sK6(X0,X1),X0) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ! [X4] :
                ( r2_hidden(sK5(X0,X1),X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ( ~ r2_hidden(X5,sK7(X0,X5))
                & r2_hidden(sK7(X0,X5),X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK5(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK5(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK5(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK7(X0,X5))
        & r2_hidden(sK7(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X4] :
                  ( r2_hidden(X2,X4)
                  | ~ r2_hidden(X4,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ? [X6] :
                  ( ~ r2_hidden(X5,X6)
                  & r2_hidden(X6,X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f86,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl10_3 ),
    inference(resolution,[],[f80,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f80,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl10_3
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f84,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f77,f82,f79])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f52,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:04:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (5947)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (5956)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (5940)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (5963)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (5947)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f84,f86,f153,f158,f173,f178,f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl10_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    $false | ~spl10_7),
% 0.22/0.53    inference(resolution,[],[f168,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK3),sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ~r1_tarski(k1_setfam_1(sK3),sK2) & r2_hidden(sK2,sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1)) => (~r1_tarski(k1_setfam_1(sK3),sK2) & r2_hidden(sK2,sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    r1_tarski(k1_setfam_1(sK3),sK2) | ~spl10_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    spl10_7 <=> r1_tarski(k1_setfam_1(sK3),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl10_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    $false | spl10_8),
% 0.22/0.53    inference(resolution,[],[f172,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r2_hidden(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ~r2_hidden(sK2,sK3) | spl10_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl10_8 <=> r2_hidden(sK2,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    spl10_7 | ~spl10_8 | ~spl10_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f160,f151,f170,f166])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    spl10_6 <=> ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~r2_hidden(sK2,sK3) | r1_tarski(k1_setfam_1(sK3),sK2) | ~spl10_6),
% 0.22/0.53    inference(resolution,[],[f152,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f33,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0) | ~r2_hidden(X0,sK3)) ) | ~spl10_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f151])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ~spl10_4 | ~spl10_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    $false | (~spl10_4 | ~spl10_5)),
% 0.22/0.53    inference(resolution,[],[f154,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl10_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    r2_hidden(sK2,k1_xboole_0) | ~spl10_5),
% 0.22/0.53    inference(backward_demodulation,[],[f36,f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    k1_xboole_0 = sK3 | ~spl10_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl10_5 <=> k1_xboole_0 = sK3),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    spl10_5 | spl10_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f143,f151,f147])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK3) | k1_xboole_0 = sK3 | r2_hidden(sK9(k1_setfam_1(sK3),sK2),X0)) )),
% 0.22/0.53    inference(resolution,[],[f107,f37])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (r1_tarski(k1_setfam_1(X5),X6) | ~r2_hidden(X7,X5) | k1_xboole_0 = X5 | r2_hidden(sK9(k1_setfam_1(X5),X6),X7)) )),
% 0.22/0.53    inference(resolution,[],[f103,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(X1)) | r2_hidden(X0,X2) | ~r2_hidden(X2,X1) | k1_xboole_0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f98,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP1(X1,X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 0.22/0.53    inference(definition_folding,[],[f11,f15,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X1,X0] : ((k1_setfam_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(k1_setfam_1(X1),X1) | ~r2_hidden(X2,k1_setfam_1(X1)) | r2_hidden(X2,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f42,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X1] : (sP0(X1,k1_setfam_1(X1)) | ~sP1(k1_setfam_1(X1),X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X1,X0) | k1_setfam_1(X1) != X0 | ~sP1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_setfam_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_setfam_1(X1) != X0)) | ~sP1(X0,X1))),
% 0.22/0.53    inference(rectify,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X1,X0] : (((k1_setfam_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_setfam_1(X0) != X1)) | ~sP1(X1,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X7,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | r2_hidden(X5,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | (((~r2_hidden(sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)) | ~r2_hidden(sK5(X0,X1),X1)) & (! [X4] : (r2_hidden(sK5(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK7(X0,X5)) & r2_hidden(sK7(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f24,f27,f26,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK5(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK5(X0,X1),X1)) & (! [X4] : (r2_hidden(sK5(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : (~r2_hidden(sK5(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK7(X0,X5)) & r2_hidden(sK7(X0,X5),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~spl10_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    $false | ~spl10_3),
% 0.22/0.53    inference(resolution,[],[f80,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl10_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl10_3 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl10_3 | spl10_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f77,f82,f79])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f52,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f61,f38])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(resolution,[],[f52,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (5947)------------------------------
% 0.22/0.53  % (5947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5947)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (5947)Memory used [KB]: 6268
% 0.22/0.53  % (5947)Time elapsed: 0.108 s
% 0.22/0.53  % (5947)------------------------------
% 0.22/0.53  % (5947)------------------------------
% 0.22/0.53  % (5932)Success in time 0.171 s
%------------------------------------------------------------------------------
