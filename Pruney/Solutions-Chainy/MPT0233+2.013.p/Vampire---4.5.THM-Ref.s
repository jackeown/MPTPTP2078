%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 436 expanded)
%              Number of leaves         :   23 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 (1190 expanded)
%              Number of equality atoms :  151 ( 734 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f458,f462,f509,f557,f593])).

fof(f593,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f591,f58])).

fof(f58,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f591,plain,
    ( sK1 = sK4
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f583,f57])).

fof(f57,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f583,plain,
    ( sK1 = sK3
    | sK1 = sK4
    | ~ spl9_1 ),
    inference(resolution,[],[f580,f170])).

fof(f170,plain,(
    ! [X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f117,f116])).

fof(f116,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f117,plain,(
    ! [X0,X1] : sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f84,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f91,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f93,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f94,f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

% (6959)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f14,f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f580,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
        | sK3 = X0
        | sK4 = X0 )
    | ~ spl9_1 ),
    inference(resolution,[],[f567,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f567,plain,
    ( sP0(sK4,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl9_1 ),
    inference(superposition,[],[f117,f428])).

fof(f428,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl9_1
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f557,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f549,f58])).

fof(f549,plain,
    ( sK1 = sK4
    | ~ spl9_4 ),
    inference(resolution,[],[f543,f170])).

fof(f543,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
        | sK4 = X0 )
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f540])).

fof(f540,plain,
    ( ! [X0] :
        ( sK4 = X0
        | ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
        | sK4 = X0 )
    | ~ spl9_4 ),
    inference(resolution,[],[f522,f78])).

fof(f522,plain,
    ( sP0(sK4,sK4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl9_4 ),
    inference(superposition,[],[f117,f440])).

fof(f440,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl9_4
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f509,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f501,f57])).

fof(f501,plain,
    ( sK1 = sK3
    | ~ spl9_3 ),
    inference(resolution,[],[f495,f170])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
        | sK3 = X0 )
    | ~ spl9_3 ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,
    ( ! [X0] :
        ( sK3 = X0
        | ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
        | sK3 = X0 )
    | ~ spl9_3 ),
    inference(resolution,[],[f474,f78])).

fof(f474,plain,
    ( sP0(sK3,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl9_3 ),
    inference(superposition,[],[f117,f436])).

fof(f436,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl9_3
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f462,plain,
    ( spl9_1
    | spl9_3
    | spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f461,f430,f438,f434,f426])).

fof(f430,plain,
    ( spl9_2
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f461,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f459,f431])).

fof(f431,plain,
    ( k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f430])).

fof(f459,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(resolution,[],[f104,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f86,f101,f102,f102,f101])).

fof(f102,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f101])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f104,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f56,f101,f101])).

fof(f56,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f458,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f451,f132])).

fof(f132,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f131,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f73,f65])).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f451,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_2 ),
    inference(superposition,[],[f336,f432])).

fof(f432,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f430])).

fof(f336,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f170,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6940)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (6956)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (6939)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.55  % (6938)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.56  % (6954)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.57  % (6948)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.57  % (6947)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.57  % (6948)Refutation not found, incomplete strategy% (6948)------------------------------
% 1.31/0.57  % (6948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (6948)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (6948)Memory used [KB]: 10618
% 1.31/0.57  % (6948)Time elapsed: 0.136 s
% 1.31/0.57  % (6948)------------------------------
% 1.31/0.57  % (6948)------------------------------
% 1.31/0.57  % (6955)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.58  % (6942)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.58  % (6958)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.58  % (6933)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.59/0.58  % (6936)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.59/0.58  % (6938)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f624,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(avatar_sat_refutation,[],[f458,f462,f509,f557,f593])).
% 1.59/0.59  fof(f593,plain,(
% 1.59/0.59    ~spl9_1),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f592])).
% 1.59/0.59  fof(f592,plain,(
% 1.59/0.59    $false | ~spl9_1),
% 1.59/0.59    inference(subsumption_resolution,[],[f591,f58])).
% 1.59/0.59  fof(f58,plain,(
% 1.59/0.59    sK1 != sK4),
% 1.59/0.59    inference(cnf_transformation,[],[f39])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f38])).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f29,plain,(
% 1.59/0.59    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.59    inference(ennf_transformation,[],[f26])).
% 1.59/0.59  fof(f26,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.59    inference(negated_conjecture,[],[f25])).
% 1.59/0.59  fof(f25,conjecture,(
% 1.59/0.59    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.59/0.59  fof(f591,plain,(
% 1.59/0.59    sK1 = sK4 | ~spl9_1),
% 1.59/0.59    inference(subsumption_resolution,[],[f583,f57])).
% 1.59/0.59  fof(f57,plain,(
% 1.59/0.59    sK1 != sK3),
% 1.59/0.59    inference(cnf_transformation,[],[f39])).
% 1.59/0.59  fof(f583,plain,(
% 1.59/0.59    sK1 = sK3 | sK1 = sK4 | ~spl9_1),
% 1.59/0.59    inference(resolution,[],[f580,f170])).
% 1.59/0.59  fof(f170,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(resolution,[],[f117,f116])).
% 1.59/0.59  fof(f116,plain,(
% 1.59/0.59    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.59/0.59    inference(equality_resolution,[],[f79])).
% 1.59/0.59  fof(f79,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f52])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).
% 1.59/0.59  fof(f51,plain,(
% 1.59/0.59    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f50,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.59/0.59    inference(rectify,[],[f49])).
% 1.59/0.59  fof(f49,plain,(
% 1.59/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.59/0.59    inference(flattening,[],[f48])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.59/0.59    inference(nnf_transformation,[],[f36])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.59/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.59  fof(f117,plain,(
% 1.59/0.59    ( ! [X0,X1] : (sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(equality_resolution,[],[f108])).
% 1.59/0.59  fof(f108,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.59/0.59    inference(definition_unfolding,[],[f84,f101])).
% 1.59/0.59  fof(f101,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f68,f100])).
% 1.59/0.59  fof(f100,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f76,f99])).
% 1.59/0.59  fof(f99,plain,(
% 1.59/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f91,f98])).
% 1.59/0.59  fof(f98,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f93,f97])).
% 1.59/0.59  fof(f97,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f94,f95])).
% 1.59/0.59  fof(f95,plain,(
% 1.59/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f22])).
% 1.59/0.59  fof(f22,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.59/0.59  fof(f94,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.59/0.59  fof(f93,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  % (6959)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.59  fof(f20,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.59/0.59  fof(f91,plain,(
% 1.59/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f19,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.59  fof(f76,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f18])).
% 1.59/0.59  fof(f18,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f17])).
% 1.59/0.59  fof(f17,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.59  fof(f84,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.59    inference(cnf_transformation,[],[f53])).
% 1.59/0.59  fof(f53,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.59/0.59    inference(nnf_transformation,[],[f37])).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.59/0.59    inference(definition_folding,[],[f14,f36])).
% 1.59/0.59  fof(f14,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.59/0.59  fof(f580,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK3 = X0 | sK4 = X0) ) | ~spl9_1),
% 1.59/0.59    inference(resolution,[],[f567,f78])).
% 1.59/0.59  fof(f78,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.59/0.59    inference(cnf_transformation,[],[f52])).
% 1.59/0.59  fof(f567,plain,(
% 1.59/0.59    sP0(sK4,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl9_1),
% 1.59/0.59    inference(superposition,[],[f117,f428])).
% 1.59/0.59  fof(f428,plain,(
% 1.59/0.59    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | ~spl9_1),
% 1.59/0.59    inference(avatar_component_clause,[],[f426])).
% 1.59/0.59  fof(f426,plain,(
% 1.59/0.59    spl9_1 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.59/0.59  fof(f557,plain,(
% 1.59/0.59    ~spl9_4),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f556])).
% 1.59/0.59  fof(f556,plain,(
% 1.59/0.59    $false | ~spl9_4),
% 1.59/0.59    inference(subsumption_resolution,[],[f549,f58])).
% 1.59/0.59  fof(f549,plain,(
% 1.59/0.59    sK1 = sK4 | ~spl9_4),
% 1.59/0.59    inference(resolution,[],[f543,f170])).
% 1.59/0.59  fof(f543,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK4 = X0) ) | ~spl9_4),
% 1.59/0.59    inference(duplicate_literal_removal,[],[f540])).
% 1.59/0.59  fof(f540,plain,(
% 1.59/0.59    ( ! [X0] : (sK4 = X0 | ~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK4 = X0) ) | ~spl9_4),
% 1.59/0.59    inference(resolution,[],[f522,f78])).
% 1.59/0.59  fof(f522,plain,(
% 1.59/0.59    sP0(sK4,sK4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl9_4),
% 1.59/0.59    inference(superposition,[],[f117,f440])).
% 1.59/0.59  fof(f440,plain,(
% 1.59/0.59    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl9_4),
% 1.59/0.59    inference(avatar_component_clause,[],[f438])).
% 1.59/0.59  fof(f438,plain,(
% 1.59/0.59    spl9_4 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.59/0.59  fof(f509,plain,(
% 1.59/0.59    ~spl9_3),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f508])).
% 1.59/0.59  fof(f508,plain,(
% 1.59/0.59    $false | ~spl9_3),
% 1.59/0.59    inference(subsumption_resolution,[],[f501,f57])).
% 1.59/0.59  fof(f501,plain,(
% 1.59/0.59    sK1 = sK3 | ~spl9_3),
% 1.59/0.59    inference(resolution,[],[f495,f170])).
% 1.59/0.59  fof(f495,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK3 = X0) ) | ~spl9_3),
% 1.59/0.59    inference(duplicate_literal_removal,[],[f492])).
% 1.59/0.59  fof(f492,plain,(
% 1.59/0.59    ( ! [X0] : (sK3 = X0 | ~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK3 = X0) ) | ~spl9_3),
% 1.59/0.59    inference(resolution,[],[f474,f78])).
% 1.59/0.59  fof(f474,plain,(
% 1.59/0.59    sP0(sK3,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl9_3),
% 1.59/0.59    inference(superposition,[],[f117,f436])).
% 1.59/0.59  fof(f436,plain,(
% 1.59/0.59    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl9_3),
% 1.59/0.59    inference(avatar_component_clause,[],[f434])).
% 1.59/0.59  fof(f434,plain,(
% 1.59/0.59    spl9_3 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.59/0.59  fof(f462,plain,(
% 1.59/0.59    spl9_1 | spl9_3 | spl9_4 | spl9_2),
% 1.59/0.59    inference(avatar_split_clause,[],[f461,f430,f438,f434,f426])).
% 1.59/0.59  fof(f430,plain,(
% 1.59/0.59    spl9_2 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.59/0.59  fof(f461,plain,(
% 1.59/0.59    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) | spl9_2),
% 1.59/0.59    inference(subsumption_resolution,[],[f459,f431])).
% 1.59/0.59  fof(f431,plain,(
% 1.59/0.59    k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | spl9_2),
% 1.59/0.59    inference(avatar_component_clause,[],[f430])).
% 1.59/0.59  fof(f459,plain,(
% 1.59/0.59    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 1.59/0.59    inference(resolution,[],[f104,f113])).
% 1.59/0.59  fof(f113,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 1.59/0.59    inference(definition_unfolding,[],[f86,f101,f102,f102,f101])).
% 1.59/0.59  fof(f102,plain,(
% 1.59/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f61,f101])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,axiom,(
% 1.59/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.59  fof(f86,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f55])).
% 1.59/0.59  fof(f55,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.59/0.59    inference(flattening,[],[f54])).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.59/0.59    inference(nnf_transformation,[],[f35])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f24])).
% 1.59/0.59  fof(f24,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.59/0.59  fof(f104,plain,(
% 1.59/0.59    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.59/0.59    inference(definition_unfolding,[],[f56,f101,f101])).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.59/0.59    inference(cnf_transformation,[],[f39])).
% 1.59/0.59  fof(f458,plain,(
% 1.59/0.59    ~spl9_2),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f457])).
% 1.59/0.59  fof(f457,plain,(
% 1.59/0.59    $false | ~spl9_2),
% 1.59/0.59    inference(subsumption_resolution,[],[f451,f132])).
% 1.59/0.59  fof(f132,plain,(
% 1.59/0.59    v1_xboole_0(k1_xboole_0)),
% 1.59/0.59    inference(resolution,[],[f131,f63])).
% 1.59/0.59  fof(f63,plain,(
% 1.59/0.59    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f43])).
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.59/0.59  fof(f42,plain,(
% 1.59/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.59    inference(rectify,[],[f40])).
% 1.59/0.59  fof(f40,plain,(
% 1.59/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.59/0.59    inference(nnf_transformation,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.59/0.59  fof(f131,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(resolution,[],[f128,f59])).
% 1.59/0.59  fof(f59,plain,(
% 1.59/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f12])).
% 1.59/0.59  fof(f12,axiom,(
% 1.59/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.59/0.59  fof(f128,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 1.59/0.59    inference(superposition,[],[f73,f65])).
% 1.59/0.59  fof(f65,plain,(
% 1.59/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f27])).
% 1.59/0.59  fof(f27,plain,(
% 1.59/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.59/0.59    inference(rectify,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.59/0.59  fof(f73,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f47])).
% 1.59/0.59  fof(f47,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f46])).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f31,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(ennf_transformation,[],[f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(rectify,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.59/0.59  fof(f451,plain,(
% 1.59/0.59    ~v1_xboole_0(k1_xboole_0) | ~spl9_2),
% 1.59/0.59    inference(superposition,[],[f336,f432])).
% 1.59/0.59  fof(f432,plain,(
% 1.59/0.59    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl9_2),
% 1.59/0.59    inference(avatar_component_clause,[],[f430])).
% 1.59/0.59  fof(f336,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(resolution,[],[f170,f62])).
% 1.59/0.59  fof(f62,plain,(
% 1.59/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f43])).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (6938)------------------------------
% 1.59/0.59  % (6938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (6938)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (6938)Memory used [KB]: 11001
% 1.59/0.59  % (6938)Time elapsed: 0.144 s
% 1.59/0.59  % (6938)------------------------------
% 1.59/0.59  % (6938)------------------------------
% 1.59/0.59  % (6931)Success in time 0.217 s
%------------------------------------------------------------------------------
