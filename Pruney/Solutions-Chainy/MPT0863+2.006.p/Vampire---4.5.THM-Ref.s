%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 155 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 ( 504 expanded)
%              Number of equality atoms :  183 ( 342 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f68,f178,f204,f207,f233,f235,f338,f340,f367,f369])).

fof(f369,plain,
    ( spl6_4
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f368])).

% (17217)Refutation not found, incomplete strategy% (17217)------------------------------
% (17217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f368,plain,
    ( $false
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f342,f66])).

% (17217)Termination reason: Refutation not found, incomplete strategy

% (17217)Memory used [KB]: 10618
% (17217)Time elapsed: 0.125 s
% (17217)------------------------------
% (17217)------------------------------
fof(f66,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_4
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f342,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl6_8 ),
    inference(superposition,[],[f24,f177])).

fof(f177,plain,
    ( sK0 = k4_tarski(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_8
  <=> sK0 = k4_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f24,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f367,plain,
    ( spl6_1
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl6_1
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f341,f52])).

fof(f52,plain,
    ( sK2 != k1_mcart_1(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f341,plain,
    ( sK2 = k1_mcart_1(sK0)
    | ~ spl6_8 ),
    inference(superposition,[],[f23,f177])).

fof(f23,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f340,plain,
    ( spl6_2
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl6_2
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f313,f56])).

fof(f56,plain,
    ( sK4 != k2_mcart_1(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_2
  <=> sK4 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f313,plain,
    ( sK4 = k2_mcart_1(sK0)
    | ~ spl6_7 ),
    inference(superposition,[],[f24,f173])).

fof(f173,plain,
    ( sK0 = k4_tarski(sK1,sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> sK0 = k4_tarski(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f338,plain,
    ( spl6_3
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f312,f61])).

fof(f61,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f312,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl6_7 ),
    inference(superposition,[],[f23,f173])).

fof(f235,plain,
    ( spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f209,f66])).

fof(f209,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl6_6 ),
    inference(superposition,[],[f24,f169])).

fof(f169,plain,
    ( sK0 = k4_tarski(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_6
  <=> sK0 = k4_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f233,plain,
    ( spl6_3
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl6_6 ),
    inference(superposition,[],[f23,f169])).

fof(f207,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f180,f56])).

fof(f180,plain,
    ( sK4 = k2_mcart_1(sK0)
    | ~ spl6_5 ),
    inference(superposition,[],[f24,f165])).

fof(f165,plain,
    ( sK0 = k4_tarski(sK2,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_5
  <=> sK0 = k4_tarski(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f204,plain,
    ( spl6_1
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f179,f52])).

fof(f179,plain,
    ( sK2 = k1_mcart_1(sK0)
    | ~ spl6_5 ),
    inference(superposition,[],[f23,f165])).

fof(f178,plain,
    ( spl6_5
    | spl6_6
    | spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f152,f175,f171,f167,f163])).

fof(f152,plain,
    ( sK0 = k4_tarski(sK2,sK3)
    | sK0 = k4_tarski(sK1,sK4)
    | sK0 = k4_tarski(sK1,sK3)
    | sK0 = k4_tarski(sK2,sK4) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f17,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( sK4 != k2_mcart_1(sK0)
          & sK3 != k2_mcart_1(sK0) )
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)))
      | k4_tarski(X3,X1) = X4
      | k4_tarski(X0,X2) = X4
      | k4_tarski(X0,X1) = X4
      | k4_tarski(X3,X2) = X4 ) ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f26,f37,f37])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f48,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK5(X0,X1,X2,X3,X4) != X3
              & sK5(X0,X1,X2,X3,X4) != X2
              & sK5(X0,X1,X2,X3,X4) != X1
              & sK5(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sK5(X0,X1,X2,X3,X4) = X3
            | sK5(X0,X1,X2,X3,X4) = X2
            | sK5(X0,X1,X2,X3,X4) = X1
            | sK5(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f15])).

fof(f15,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4) != X3
            & sK5(X0,X1,X2,X3,X4) != X2
            & sK5(X0,X1,X2,X3,X4) != X1
            & sK5(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sK5(X0,X1,X2,X3,X4) = X3
          | sK5(X0,X1,X2,X3,X4) = X2
          | sK5(X0,X1,X2,X3,X4) = X1
          | sK5(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f68,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f18,f64,f59])).

% (17240)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f18,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f19,f64,f50])).

fof(f19,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,
    ( ~ spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f20,f54,f59])).

fof(f20,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f21,f54,f50])).

fof(f21,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17241)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (17218)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (17232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (17217)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (17219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (17219)Refutation not found, incomplete strategy% (17219)------------------------------
% 0.22/0.53  % (17219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17219)Memory used [KB]: 6268
% 0.22/0.53  % (17219)Time elapsed: 0.110 s
% 0.22/0.53  % (17237)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (17218)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (17225)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (17216)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (17223)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (17243)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (17220)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (17241)Refutation not found, incomplete strategy% (17241)------------------------------
% 0.22/0.54  % (17241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (17241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17241)Memory used [KB]: 6396
% 0.22/0.54  % (17241)Time elapsed: 0.110 s
% 0.22/0.54  % (17241)------------------------------
% 0.22/0.54  % (17241)------------------------------
% 0.22/0.54  % (17224)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (17242)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (17245)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f370,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f57,f62,f67,f68,f178,f204,f207,f233,f235,f338,f340,f367,f369])).
% 0.22/0.55  fof(f369,plain,(
% 0.22/0.55    spl6_4 | ~spl6_8),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f368])).
% 0.22/0.55  % (17217)Refutation not found, incomplete strategy% (17217)------------------------------
% 0.22/0.55  % (17217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  fof(f368,plain,(
% 0.22/0.55    $false | (spl6_4 | ~spl6_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f342,f66])).
% 0.22/0.55  % (17217)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17217)Memory used [KB]: 10618
% 0.22/0.55  % (17217)Time elapsed: 0.125 s
% 0.22/0.55  % (17217)------------------------------
% 0.22/0.55  % (17217)------------------------------
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    sK3 != k2_mcart_1(sK0) | spl6_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    spl6_4 <=> sK3 = k2_mcart_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    sK3 = k2_mcart_1(sK0) | ~spl6_8),
% 0.22/0.55    inference(superposition,[],[f24,f177])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    sK0 = k4_tarski(sK2,sK3) | ~spl6_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    spl6_8 <=> sK0 = k4_tarski(sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.55  fof(f367,plain,(
% 0.22/0.55    spl6_1 | ~spl6_8),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.55  fof(f366,plain,(
% 0.22/0.55    $false | (spl6_1 | ~spl6_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f341,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    sK2 != k1_mcart_1(sK0) | spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    spl6_1 <=> sK2 = k1_mcart_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.55  fof(f341,plain,(
% 0.22/0.55    sK2 = k1_mcart_1(sK0) | ~spl6_8),
% 0.22/0.55    inference(superposition,[],[f23,f177])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f340,plain,(
% 0.22/0.55    spl6_2 | ~spl6_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f339])).
% 0.22/0.55  fof(f339,plain,(
% 0.22/0.55    $false | (spl6_2 | ~spl6_7)),
% 0.22/0.55    inference(subsumption_resolution,[],[f313,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    sK4 != k2_mcart_1(sK0) | spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    spl6_2 <=> sK4 = k2_mcart_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.55  fof(f313,plain,(
% 0.22/0.55    sK4 = k2_mcart_1(sK0) | ~spl6_7),
% 0.22/0.55    inference(superposition,[],[f24,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    sK0 = k4_tarski(sK1,sK4) | ~spl6_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl6_7 <=> sK0 = k4_tarski(sK1,sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.55  fof(f338,plain,(
% 0.22/0.55    spl6_3 | ~spl6_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f337])).
% 0.22/0.55  fof(f337,plain,(
% 0.22/0.55    $false | (spl6_3 | ~spl6_7)),
% 0.22/0.55    inference(subsumption_resolution,[],[f312,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    sK1 != k1_mcart_1(sK0) | spl6_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    spl6_3 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.55  fof(f312,plain,(
% 0.22/0.55    sK1 = k1_mcart_1(sK0) | ~spl6_7),
% 0.22/0.55    inference(superposition,[],[f23,f173])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    spl6_4 | ~spl6_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    $false | (spl6_4 | ~spl6_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f209,f66])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    sK3 = k2_mcart_1(sK0) | ~spl6_6),
% 0.22/0.55    inference(superposition,[],[f24,f169])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    sK0 = k4_tarski(sK1,sK3) | ~spl6_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f167])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    spl6_6 <=> sK0 = k4_tarski(sK1,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.55  fof(f233,plain,(
% 0.22/0.55    spl6_3 | ~spl6_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f232])).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    $false | (spl6_3 | ~spl6_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f208,f61])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    sK1 = k1_mcart_1(sK0) | ~spl6_6),
% 0.22/0.55    inference(superposition,[],[f23,f169])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    spl6_2 | ~spl6_5),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    $false | (spl6_2 | ~spl6_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f180,f56])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    sK4 = k2_mcart_1(sK0) | ~spl6_5),
% 0.22/0.55    inference(superposition,[],[f24,f165])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    sK0 = k4_tarski(sK2,sK4) | ~spl6_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    spl6_5 <=> sK0 = k4_tarski(sK2,sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    spl6_1 | ~spl6_5),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    $false | (spl6_1 | ~spl6_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f179,f52])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    sK2 = k1_mcart_1(sK0) | ~spl6_5),
% 0.22/0.55    inference(superposition,[],[f23,f165])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl6_5 | spl6_6 | spl6_7 | spl6_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f152,f175,f171,f167,f163])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    sK0 = k4_tarski(sK2,sK3) | sK0 = k4_tarski(sK1,sK4) | sK0 = k4_tarski(sK1,sK3) | sK0 = k4_tarski(sK2,sK4)),
% 0.22/0.55    inference(resolution,[],[f75,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4)))),
% 0.22/0.55    inference(definition_unfolding,[],[f17,f37,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f22,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2))) | k4_tarski(X3,X1) = X4 | k4_tarski(X0,X2) = X4 | k4_tarski(X0,X1) = X4 | k4_tarski(X3,X2) = X4) )),
% 0.22/0.55    inference(superposition,[],[f48,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f26,f37,f37])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) | X2 = X6 | X1 = X6 | X0 = X6 | X3 = X6) )),
% 0.22/0.55    inference(equality_resolution,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.55    inference(rectify,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.55    inference(flattening,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.55    inference(nnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ~spl6_3 | ~spl6_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f18,f64,f59])).
% 0.22/0.55  % (17240)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ~spl6_1 | ~spl6_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f19,f64,f50])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ~spl6_3 | ~spl6_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f20,f54,f59])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ~spl6_1 | ~spl6_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f21,f54,f50])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (17218)------------------------------
% 0.22/0.55  % (17218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (17218)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (17218)Memory used [KB]: 11257
% 0.22/0.55  % (17218)Time elapsed: 0.117 s
% 0.22/0.55  % (17218)------------------------------
% 0.22/0.55  % (17218)------------------------------
% 0.22/0.55  % (17239)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (17219)------------------------------
% 0.22/0.55  % (17219)------------------------------
% 0.22/0.55  % (17233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (17237)Refutation not found, incomplete strategy% (17237)------------------------------
% 0.22/0.55  % (17237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17237)Memory used [KB]: 1663
% 0.22/0.55  % (17237)Time elapsed: 0.133 s
% 0.22/0.55  % (17237)------------------------------
% 0.22/0.55  % (17237)------------------------------
% 0.22/0.55  % (17228)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (17213)Success in time 0.183 s
%------------------------------------------------------------------------------
