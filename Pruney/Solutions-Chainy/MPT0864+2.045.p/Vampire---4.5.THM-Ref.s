%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  387 (1036 expanded)
%              Number of equality atoms :  177 ( 484 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f73,f79,f86,f92,f551,f612,f618,f632,f636,f640])).

fof(f640,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f109,f630])).

fof(f630,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f628])).

% (24821)Refutation not found, incomplete strategy% (24821)------------------------------
% (24821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24821)Termination reason: Refutation not found, incomplete strategy

fof(f628,plain,
    ( spl6_10
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

% (24821)Memory used [KB]: 10746
% (24821)Time elapsed: 0.200 s
% (24821)------------------------------
% (24821)------------------------------
fof(f109,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    inference(condensation,[],[f108])).

fof(f108,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | ~ r2_hidden(X7,X6) ) ),
    inference(superposition,[],[f58,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f96,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

% (24815)Refutation not found, incomplete strategy% (24815)------------------------------
% (24815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24815)Termination reason: Refutation not found, incomplete strategy

% (24815)Memory used [KB]: 1663
% (24815)Time elapsed: 0.200 s
% (24815)------------------------------
% (24815)------------------------------
% (24805)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (24814)Memory used [KB]: 1663
% (24814)Time elapsed: 0.181 s
% (24814)------------------------------
% (24814)------------------------------
fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f636,plain,
    ( spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f625,f544,f628])).

fof(f544,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f625,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_7 ),
    inference(superposition,[],[f53,f546])).

fof(f546,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f544])).

fof(f53,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f632,plain,
    ( k1_mcart_1(sK0) != sK1
    | sK0 != k1_mcart_1(sK0)
    | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f618,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f53,f611])).

fof(f611,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl6_9
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f612,plain,
    ( spl6_7
    | ~ spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f588,f89,f609,f544])).

fof(f89,plain,
    ( spl6_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f588,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl6_6 ),
    inference(equality_resolution,[],[f586])).

fof(f586,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK0,k1_enumset1(X2,X2,sK0))
        | k1_xboole_0 = k1_enumset1(X2,X2,sK0) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK0,k1_enumset1(X2,X2,sK0))
        | k1_xboole_0 = k1_enumset1(X2,X2,sK0)
        | k1_xboole_0 = k1_enumset1(X2,X2,sK0)
        | ~ r2_hidden(sK0,k1_enumset1(X2,X2,sK0)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f121,f574])).

fof(f574,plain,
    ( ! [X0] :
        ( sK3(k1_enumset1(X0,X0,sK0)) = X0
        | k1_xboole_0 = k1_enumset1(X0,X0,sK0)
        | ~ r2_hidden(sK0,k1_enumset1(X0,X0,sK0)) )
    | ~ spl6_6 ),
    inference(equality_resolution,[],[f527])).

fof(f527,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK3(k1_enumset1(X0,X0,X1)) = X0 )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) = k1_xboole_0
        | sK3(k1_enumset1(X0,X0,X1)) = X0
        | k1_enumset1(X0,X0,X1) = k1_xboole_0 )
    | ~ spl6_6 ),
    inference(superposition,[],[f121,f125])).

fof(f125,plain,(
    ! [X4,X5] :
      ( sK3(k1_enumset1(X4,X4,X5)) = X5
      | sK3(k1_enumset1(X4,X4,X5)) = X4
      | k1_xboole_0 = k1_enumset1(X4,X4,X5) ) ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f121,plain,
    ( ! [X1] :
        ( sK0 != sK3(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_6 ),
    inference(superposition,[],[f32,f91])).

fof(f91,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f551,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f542,f61,f548,f544])).

fof(f548,plain,
    ( spl6_8
  <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f61,plain,
    ( spl6_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f542,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl6_1 ),
    inference(equality_resolution,[],[f538])).

fof(f538,plain,
    ( ! [X5] :
        ( sK0 != X5
        | ~ r2_hidden(sK1,k1_enumset1(X5,X5,sK0))
        | k1_xboole_0 = k1_enumset1(X5,X5,sK0) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f533])).

fof(f533,plain,
    ( ! [X5] :
        ( sK0 != X5
        | ~ r2_hidden(sK1,k1_enumset1(X5,X5,sK0))
        | k1_xboole_0 = k1_enumset1(X5,X5,sK0)
        | k1_xboole_0 = k1_enumset1(X5,X5,sK0)
        | ~ r2_hidden(sK1,k1_enumset1(X5,X5,sK0)) )
    | ~ spl6_1 ),
    inference(superposition,[],[f110,f528])).

fof(f528,plain,
    ( ! [X0] :
        ( sK3(k1_enumset1(X0,X0,sK0)) = X0
        | k1_xboole_0 = k1_enumset1(X0,X0,sK0)
        | ~ r2_hidden(sK1,k1_enumset1(X0,X0,sK0)) )
    | ~ spl6_1 ),
    inference(equality_resolution,[],[f525])).

fof(f525,plain,
    ( ! [X6,X7] :
        ( sK0 != X7
        | ~ r2_hidden(sK1,k1_enumset1(X6,X6,X7))
        | k1_xboole_0 = k1_enumset1(X6,X6,X7)
        | sK3(k1_enumset1(X6,X6,X7)) = X6 )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f519])).

fof(f519,plain,
    ( ! [X6,X7] :
        ( sK0 != X7
        | ~ r2_hidden(sK1,k1_enumset1(X6,X6,X7))
        | k1_xboole_0 = k1_enumset1(X6,X6,X7)
        | sK3(k1_enumset1(X6,X6,X7)) = X6
        | k1_xboole_0 = k1_enumset1(X6,X6,X7) )
    | ~ spl6_1 ),
    inference(superposition,[],[f110,f125])).

fof(f110,plain,
    ( ! [X0] :
        ( sK0 != sK3(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_1 ),
    inference(superposition,[],[f31,f63])).

fof(f63,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,
    ( spl6_6
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f87,f83,f61,f89])).

fof(f83,plain,
    ( spl6_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f87,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f63,f85])).

fof(f85,plain,
    ( sK0 = sK2
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,
    ( spl6_5
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f81,f70,f61,f83])).

fof(f70,plain,
    ( spl6_3
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f81,plain,
    ( sK0 = sK2
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f80,f72])).

fof(f72,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f80,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl6_1 ),
    inference(superposition,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f79,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f74,f61,f76])).

fof(f76,plain,
    ( spl6_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f74,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl6_1 ),
    inference(superposition,[],[f28,f63])).

fof(f28,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f27,f70,f66])).

fof(f66,plain,
    ( spl6_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f27,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f64,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.38/0.56  % (24800)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.60/0.57  % (24817)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.60/0.59  % (24825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.60/0.59  % (24826)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.60/0.59  % (24826)Refutation not found, incomplete strategy% (24826)------------------------------
% 1.60/0.59  % (24826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (24826)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (24826)Memory used [KB]: 1663
% 1.60/0.59  % (24826)Time elapsed: 0.003 s
% 1.60/0.59  % (24826)------------------------------
% 1.60/0.59  % (24826)------------------------------
% 1.60/0.59  % (24810)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.60/0.59  % (24802)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.60  % (24825)Refutation not found, incomplete strategy% (24825)------------------------------
% 1.60/0.60  % (24825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (24807)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.60/0.60  % (24825)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (24798)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.60/0.60  % (24825)Memory used [KB]: 10746
% 1.60/0.60  % (24825)Time elapsed: 0.162 s
% 1.60/0.60  % (24825)------------------------------
% 1.60/0.60  % (24825)------------------------------
% 1.60/0.60  % (24798)Refutation not found, incomplete strategy% (24798)------------------------------
% 1.60/0.60  % (24798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (24798)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (24798)Memory used [KB]: 1663
% 1.60/0.60  % (24798)Time elapsed: 0.123 s
% 1.60/0.60  % (24798)------------------------------
% 1.60/0.60  % (24798)------------------------------
% 1.60/0.60  % (24809)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.60/0.60  % (24807)Refutation not found, incomplete strategy% (24807)------------------------------
% 1.60/0.60  % (24807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (24807)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (24807)Memory used [KB]: 10746
% 1.60/0.60  % (24807)Time elapsed: 0.169 s
% 1.60/0.60  % (24807)------------------------------
% 1.60/0.60  % (24807)------------------------------
% 1.60/0.60  % (24809)Refutation not found, incomplete strategy% (24809)------------------------------
% 1.60/0.60  % (24809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (24809)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (24809)Memory used [KB]: 10618
% 1.60/0.60  % (24809)Time elapsed: 0.159 s
% 1.60/0.60  % (24809)------------------------------
% 1.60/0.60  % (24809)------------------------------
% 1.60/0.60  % (24797)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.60/0.60  % (24820)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.60  % (24822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.60/0.60  % (24822)Refutation not found, incomplete strategy% (24822)------------------------------
% 1.60/0.60  % (24822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (24822)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (24822)Memory used [KB]: 6140
% 1.60/0.60  % (24822)Time elapsed: 0.181 s
% 1.60/0.60  % (24822)------------------------------
% 1.60/0.60  % (24822)------------------------------
% 1.60/0.61  % (24812)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.61  % (24808)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.60/0.61  % (24801)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.60/0.61  % (24814)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.60/0.61  % (24814)Refutation not found, incomplete strategy% (24814)------------------------------
% 1.60/0.61  % (24814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (24814)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.61  
% 1.60/0.61  % (24815)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.60/0.61  % (24803)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.61  % (24799)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.60/0.61  % (24804)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.60/0.62  % (24806)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.60/0.62  % (24819)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.60/0.62  % (24816)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.60/0.62  % (24811)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.60/0.62  % (24824)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.60/0.62  % (24813)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.62  % (24824)Refutation not found, incomplete strategy% (24824)------------------------------
% 1.60/0.62  % (24824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (24824)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.62  
% 1.60/0.62  % (24824)Memory used [KB]: 6140
% 1.60/0.62  % (24824)Time elapsed: 0.200 s
% 1.60/0.62  % (24824)------------------------------
% 1.60/0.62  % (24824)------------------------------
% 1.60/0.63  % (24808)Refutation not found, incomplete strategy% (24808)------------------------------
% 1.60/0.63  % (24808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (24818)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.60/0.63  % (24808)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (24808)Memory used [KB]: 6268
% 1.60/0.63  % (24808)Time elapsed: 0.201 s
% 1.60/0.63  % (24808)------------------------------
% 1.60/0.63  % (24808)------------------------------
% 1.60/0.63  % (24821)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.63  % (24823)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.63  % (24811)Refutation not found, incomplete strategy% (24811)------------------------------
% 1.60/0.63  % (24811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (24811)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (24811)Memory used [KB]: 1791
% 1.60/0.63  % (24811)Time elapsed: 0.191 s
% 1.60/0.63  % (24811)------------------------------
% 1.60/0.63  % (24811)------------------------------
% 1.60/0.63  % (24823)Refutation not found, incomplete strategy% (24823)------------------------------
% 1.60/0.63  % (24823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (24823)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (24823)Memory used [KB]: 6140
% 1.60/0.63  % (24823)Time elapsed: 0.199 s
% 1.60/0.63  % (24823)------------------------------
% 1.60/0.63  % (24823)------------------------------
% 1.60/0.63  % (24820)Refutation found. Thanks to Tanya!
% 1.60/0.63  % SZS status Theorem for theBenchmark
% 1.60/0.63  % SZS output start Proof for theBenchmark
% 1.60/0.63  fof(f641,plain,(
% 1.60/0.63    $false),
% 1.60/0.63    inference(avatar_sat_refutation,[],[f64,f73,f79,f86,f92,f551,f612,f618,f632,f636,f640])).
% 1.60/0.63  fof(f640,plain,(
% 1.60/0.63    ~spl6_10),
% 1.60/0.63    inference(avatar_contradiction_clause,[],[f637])).
% 1.60/0.63  fof(f637,plain,(
% 1.60/0.63    $false | ~spl6_10),
% 1.60/0.63    inference(unit_resulting_resolution,[],[f109,f630])).
% 1.60/0.63  fof(f630,plain,(
% 1.60/0.63    r2_hidden(sK0,k1_xboole_0) | ~spl6_10),
% 1.60/0.63    inference(avatar_component_clause,[],[f628])).
% 1.60/0.63  % (24821)Refutation not found, incomplete strategy% (24821)------------------------------
% 1.60/0.63  % (24821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (24821)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  fof(f628,plain,(
% 1.60/0.63    spl6_10 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.60/0.63  % (24821)Memory used [KB]: 10746
% 1.60/0.63  % (24821)Time elapsed: 0.200 s
% 1.60/0.63  % (24821)------------------------------
% 1.60/0.63  % (24821)------------------------------
% 1.60/0.63  fof(f109,plain,(
% 1.60/0.63    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) )),
% 1.60/0.63    inference(condensation,[],[f108])).
% 1.60/0.63  fof(f108,plain,(
% 1.60/0.63    ( ! [X6,X7] : (~r2_hidden(X7,k1_xboole_0) | ~r2_hidden(X7,X6)) )),
% 1.60/0.63    inference(superposition,[],[f58,f103])).
% 1.60/0.63  fof(f103,plain,(
% 1.60/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.60/0.63    inference(duplicate_literal_removal,[],[f100])).
% 1.60/0.63  fof(f100,plain,(
% 1.60/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.60/0.63    inference(resolution,[],[f96,f95])).
% 1.60/0.63  fof(f95,plain,(
% 1.60/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.60/0.63    inference(resolution,[],[f58,f30])).
% 1.60/0.63  fof(f30,plain,(
% 1.60/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.60/0.63    inference(cnf_transformation,[],[f15])).
% 1.60/0.63  fof(f15,plain,(
% 1.60/0.63    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.60/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).
% 1.60/0.63  fof(f14,plain,(
% 1.60/0.63    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.60/0.63    introduced(choice_axiom,[])).
% 1.60/0.63  fof(f10,plain,(
% 1.60/0.63    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.60/0.63    inference(ennf_transformation,[],[f6])).
% 1.60/0.63  fof(f6,axiom,(
% 1.60/0.63    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.60/0.63  % (24815)Refutation not found, incomplete strategy% (24815)------------------------------
% 1.60/0.63  % (24815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (24815)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (24815)Memory used [KB]: 1663
% 1.60/0.63  % (24815)Time elapsed: 0.200 s
% 1.60/0.63  % (24815)------------------------------
% 1.60/0.63  % (24815)------------------------------
% 1.60/0.63  % (24805)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.60/0.63  % (24814)Memory used [KB]: 1663
% 1.60/0.63  % (24814)Time elapsed: 0.181 s
% 1.60/0.63  % (24814)------------------------------
% 1.60/0.63  % (24814)------------------------------
% 1.60/0.64  fof(f96,plain,(
% 1.60/0.64    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.60/0.64    inference(resolution,[],[f59,f30])).
% 1.60/0.64  fof(f59,plain,(
% 1.60/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.60/0.64    inference(equality_resolution,[],[f39])).
% 1.60/0.64  fof(f39,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.60/0.64    inference(cnf_transformation,[],[f25])).
% 1.60/0.64  fof(f25,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 1.60/0.64  fof(f24,plain,(
% 1.60/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.60/0.64    introduced(choice_axiom,[])).
% 1.60/0.64  fof(f23,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.64    inference(rectify,[],[f22])).
% 1.60/0.64  fof(f22,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.64    inference(flattening,[],[f21])).
% 1.60/0.64  fof(f21,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.64    inference(nnf_transformation,[],[f1])).
% 1.60/0.64  fof(f1,axiom,(
% 1.60/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.60/0.64  fof(f58,plain,(
% 1.60/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.60/0.64    inference(equality_resolution,[],[f40])).
% 1.60/0.64  fof(f40,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.60/0.64    inference(cnf_transformation,[],[f25])).
% 1.60/0.64  fof(f636,plain,(
% 1.60/0.64    spl6_10 | ~spl6_7),
% 1.60/0.64    inference(avatar_split_clause,[],[f625,f544,f628])).
% 1.60/0.64  fof(f544,plain,(
% 1.60/0.64    spl6_7 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.60/0.64  fof(f625,plain,(
% 1.60/0.64    r2_hidden(sK0,k1_xboole_0) | ~spl6_7),
% 1.60/0.64    inference(superposition,[],[f53,f546])).
% 1.60/0.64  fof(f546,plain,(
% 1.60/0.64    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl6_7),
% 1.60/0.64    inference(avatar_component_clause,[],[f544])).
% 1.60/0.64  fof(f53,plain,(
% 1.60/0.64    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 1.60/0.64    inference(equality_resolution,[],[f52])).
% 1.60/0.64  fof(f52,plain,(
% 1.60/0.64    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 1.60/0.64    inference(equality_resolution,[],[f49])).
% 1.60/0.64  fof(f49,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 1.60/0.64    inference(definition_unfolding,[],[f35,f45])).
% 1.60/0.64  fof(f45,plain,(
% 1.60/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.64    inference(cnf_transformation,[],[f3])).
% 1.60/0.64  fof(f3,axiom,(
% 1.60/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.64  fof(f35,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.60/0.64    inference(cnf_transformation,[],[f20])).
% 1.60/0.64  fof(f20,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.60/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 1.60/0.64  fof(f19,plain,(
% 1.60/0.64    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.60/0.64    introduced(choice_axiom,[])).
% 1.60/0.64  fof(f18,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.60/0.64    inference(rectify,[],[f17])).
% 1.60/0.64  fof(f17,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.60/0.64    inference(flattening,[],[f16])).
% 1.60/0.64  fof(f16,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.60/0.64    inference(nnf_transformation,[],[f2])).
% 1.60/0.64  fof(f2,axiom,(
% 1.60/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.60/0.64  fof(f632,plain,(
% 1.60/0.64    k1_mcart_1(sK0) != sK1 | sK0 != k1_mcart_1(sK0) | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 1.60/0.64    introduced(theory_tautology_sat_conflict,[])).
% 1.60/0.64  fof(f618,plain,(
% 1.60/0.64    spl6_9),
% 1.60/0.64    inference(avatar_contradiction_clause,[],[f613])).
% 1.60/0.64  fof(f613,plain,(
% 1.60/0.64    $false | spl6_9),
% 1.60/0.64    inference(unit_resulting_resolution,[],[f53,f611])).
% 1.60/0.64  fof(f611,plain,(
% 1.60/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl6_9),
% 1.60/0.64    inference(avatar_component_clause,[],[f609])).
% 1.60/0.64  fof(f609,plain,(
% 1.60/0.64    spl6_9 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.60/0.64  fof(f612,plain,(
% 1.60/0.64    spl6_7 | ~spl6_9 | ~spl6_6),
% 1.60/0.64    inference(avatar_split_clause,[],[f588,f89,f609,f544])).
% 1.60/0.64  fof(f89,plain,(
% 1.60/0.64    spl6_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.60/0.64  fof(f588,plain,(
% 1.60/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl6_6),
% 1.60/0.64    inference(equality_resolution,[],[f586])).
% 1.60/0.64  fof(f586,plain,(
% 1.60/0.64    ( ! [X2] : (sK0 != X2 | ~r2_hidden(sK0,k1_enumset1(X2,X2,sK0)) | k1_xboole_0 = k1_enumset1(X2,X2,sK0)) ) | ~spl6_6),
% 1.60/0.64    inference(duplicate_literal_removal,[],[f577])).
% 1.60/0.64  fof(f577,plain,(
% 1.60/0.64    ( ! [X2] : (sK0 != X2 | ~r2_hidden(sK0,k1_enumset1(X2,X2,sK0)) | k1_xboole_0 = k1_enumset1(X2,X2,sK0) | k1_xboole_0 = k1_enumset1(X2,X2,sK0) | ~r2_hidden(sK0,k1_enumset1(X2,X2,sK0))) ) | ~spl6_6),
% 1.60/0.64    inference(superposition,[],[f121,f574])).
% 1.60/0.64  fof(f574,plain,(
% 1.60/0.64    ( ! [X0] : (sK3(k1_enumset1(X0,X0,sK0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,sK0) | ~r2_hidden(sK0,k1_enumset1(X0,X0,sK0))) ) | ~spl6_6),
% 1.60/0.64    inference(equality_resolution,[],[f527])).
% 1.60/0.64  fof(f527,plain,(
% 1.60/0.64    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK3(k1_enumset1(X0,X0,X1)) = X0) ) | ~spl6_6),
% 1.60/0.64    inference(duplicate_literal_removal,[],[f517])).
% 1.60/0.64  fof(f517,plain,(
% 1.60/0.64    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) = k1_xboole_0 | sK3(k1_enumset1(X0,X0,X1)) = X0 | k1_enumset1(X0,X0,X1) = k1_xboole_0) ) | ~spl6_6),
% 1.60/0.64    inference(superposition,[],[f121,f125])).
% 1.60/0.64  fof(f125,plain,(
% 1.60/0.64    ( ! [X4,X5] : (sK3(k1_enumset1(X4,X4,X5)) = X5 | sK3(k1_enumset1(X4,X4,X5)) = X4 | k1_xboole_0 = k1_enumset1(X4,X4,X5)) )),
% 1.60/0.64    inference(resolution,[],[f56,f30])).
% 1.60/0.64  fof(f56,plain,(
% 1.60/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.60/0.64    inference(equality_resolution,[],[f51])).
% 1.60/0.64  fof(f51,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.60/0.64    inference(definition_unfolding,[],[f33,f45])).
% 1.60/0.64  fof(f33,plain,(
% 1.60/0.64    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.60/0.64    inference(cnf_transformation,[],[f20])).
% 1.60/0.64  fof(f121,plain,(
% 1.60/0.64    ( ! [X1] : (sK0 != sK3(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl6_6),
% 1.60/0.64    inference(superposition,[],[f32,f91])).
% 1.60/0.64  fof(f91,plain,(
% 1.60/0.64    sK0 = k4_tarski(sK1,sK0) | ~spl6_6),
% 1.60/0.64    inference(avatar_component_clause,[],[f89])).
% 1.60/0.64  fof(f32,plain,(
% 1.60/0.64    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.60/0.64    inference(cnf_transformation,[],[f15])).
% 1.60/0.64  fof(f551,plain,(
% 1.60/0.64    spl6_7 | ~spl6_8 | ~spl6_1),
% 1.60/0.64    inference(avatar_split_clause,[],[f542,f61,f548,f544])).
% 1.60/0.64  fof(f548,plain,(
% 1.60/0.64    spl6_8 <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.60/0.64  fof(f61,plain,(
% 1.60/0.64    spl6_1 <=> sK0 = k4_tarski(sK1,sK2)),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.60/0.64  fof(f542,plain,(
% 1.60/0.64    ~r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl6_1),
% 1.60/0.64    inference(equality_resolution,[],[f538])).
% 1.60/0.64  fof(f538,plain,(
% 1.60/0.64    ( ! [X5] : (sK0 != X5 | ~r2_hidden(sK1,k1_enumset1(X5,X5,sK0)) | k1_xboole_0 = k1_enumset1(X5,X5,sK0)) ) | ~spl6_1),
% 1.60/0.64    inference(duplicate_literal_removal,[],[f533])).
% 1.60/0.64  fof(f533,plain,(
% 1.60/0.64    ( ! [X5] : (sK0 != X5 | ~r2_hidden(sK1,k1_enumset1(X5,X5,sK0)) | k1_xboole_0 = k1_enumset1(X5,X5,sK0) | k1_xboole_0 = k1_enumset1(X5,X5,sK0) | ~r2_hidden(sK1,k1_enumset1(X5,X5,sK0))) ) | ~spl6_1),
% 1.60/0.64    inference(superposition,[],[f110,f528])).
% 1.60/0.64  fof(f528,plain,(
% 1.60/0.64    ( ! [X0] : (sK3(k1_enumset1(X0,X0,sK0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,sK0) | ~r2_hidden(sK1,k1_enumset1(X0,X0,sK0))) ) | ~spl6_1),
% 1.60/0.64    inference(equality_resolution,[],[f525])).
% 1.60/0.64  fof(f525,plain,(
% 1.60/0.64    ( ! [X6,X7] : (sK0 != X7 | ~r2_hidden(sK1,k1_enumset1(X6,X6,X7)) | k1_xboole_0 = k1_enumset1(X6,X6,X7) | sK3(k1_enumset1(X6,X6,X7)) = X6) ) | ~spl6_1),
% 1.60/0.64    inference(duplicate_literal_removal,[],[f519])).
% 1.60/0.64  fof(f519,plain,(
% 1.60/0.64    ( ! [X6,X7] : (sK0 != X7 | ~r2_hidden(sK1,k1_enumset1(X6,X6,X7)) | k1_xboole_0 = k1_enumset1(X6,X6,X7) | sK3(k1_enumset1(X6,X6,X7)) = X6 | k1_xboole_0 = k1_enumset1(X6,X6,X7)) ) | ~spl6_1),
% 1.60/0.64    inference(superposition,[],[f110,f125])).
% 1.60/0.64  fof(f110,plain,(
% 1.60/0.64    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl6_1),
% 1.60/0.64    inference(superposition,[],[f31,f63])).
% 1.60/0.64  fof(f63,plain,(
% 1.60/0.64    sK0 = k4_tarski(sK1,sK2) | ~spl6_1),
% 1.60/0.64    inference(avatar_component_clause,[],[f61])).
% 1.60/0.64  fof(f31,plain,(
% 1.60/0.64    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.60/0.64    inference(cnf_transformation,[],[f15])).
% 1.60/0.64  fof(f92,plain,(
% 1.60/0.64    spl6_6 | ~spl6_1 | ~spl6_5),
% 1.60/0.64    inference(avatar_split_clause,[],[f87,f83,f61,f89])).
% 1.60/0.64  fof(f83,plain,(
% 1.60/0.64    spl6_5 <=> sK0 = sK2),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.60/0.64  fof(f87,plain,(
% 1.60/0.64    sK0 = k4_tarski(sK1,sK0) | (~spl6_1 | ~spl6_5)),
% 1.60/0.64    inference(superposition,[],[f63,f85])).
% 1.60/0.64  fof(f85,plain,(
% 1.60/0.64    sK0 = sK2 | ~spl6_5),
% 1.60/0.64    inference(avatar_component_clause,[],[f83])).
% 1.60/0.64  fof(f86,plain,(
% 1.60/0.64    spl6_5 | ~spl6_1 | ~spl6_3),
% 1.60/0.64    inference(avatar_split_clause,[],[f81,f70,f61,f83])).
% 1.60/0.64  fof(f70,plain,(
% 1.60/0.64    spl6_3 <=> sK0 = k2_mcart_1(sK0)),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.60/0.64  fof(f81,plain,(
% 1.60/0.64    sK0 = sK2 | (~spl6_1 | ~spl6_3)),
% 1.60/0.64    inference(forward_demodulation,[],[f80,f72])).
% 1.60/0.64  fof(f72,plain,(
% 1.60/0.64    sK0 = k2_mcart_1(sK0) | ~spl6_3),
% 1.60/0.64    inference(avatar_component_clause,[],[f70])).
% 1.60/0.64  fof(f80,plain,(
% 1.60/0.64    k2_mcart_1(sK0) = sK2 | ~spl6_1),
% 1.60/0.64    inference(superposition,[],[f29,f63])).
% 1.60/0.64  fof(f29,plain,(
% 1.60/0.64    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.60/0.64    inference(cnf_transformation,[],[f5])).
% 1.60/0.64  fof(f5,axiom,(
% 1.60/0.64    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.60/0.64  fof(f79,plain,(
% 1.60/0.64    spl6_4 | ~spl6_1),
% 1.60/0.64    inference(avatar_split_clause,[],[f74,f61,f76])).
% 1.60/0.64  fof(f76,plain,(
% 1.60/0.64    spl6_4 <=> k1_mcart_1(sK0) = sK1),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.60/0.64  fof(f74,plain,(
% 1.60/0.64    k1_mcart_1(sK0) = sK1 | ~spl6_1),
% 1.60/0.64    inference(superposition,[],[f28,f63])).
% 1.60/0.64  fof(f28,plain,(
% 1.60/0.64    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.60/0.64    inference(cnf_transformation,[],[f5])).
% 1.60/0.64  fof(f73,plain,(
% 1.60/0.64    spl6_2 | spl6_3),
% 1.60/0.64    inference(avatar_split_clause,[],[f27,f70,f66])).
% 1.60/0.64  fof(f66,plain,(
% 1.60/0.64    spl6_2 <=> sK0 = k1_mcart_1(sK0)),
% 1.60/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.60/0.64  fof(f27,plain,(
% 1.60/0.64    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.60/0.64    inference(cnf_transformation,[],[f13])).
% 1.60/0.64  fof(f13,plain,(
% 1.60/0.64    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.60/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).
% 1.60/0.64  fof(f11,plain,(
% 1.60/0.64    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.60/0.64    introduced(choice_axiom,[])).
% 1.60/0.64  fof(f12,plain,(
% 1.60/0.64    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.60/0.64    introduced(choice_axiom,[])).
% 1.60/0.64  fof(f9,plain,(
% 1.60/0.64    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.60/0.64    inference(ennf_transformation,[],[f8])).
% 1.60/0.64  fof(f8,negated_conjecture,(
% 1.60/0.64    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.60/0.64    inference(negated_conjecture,[],[f7])).
% 1.60/0.64  fof(f7,conjecture,(
% 1.60/0.64    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.60/0.64  fof(f64,plain,(
% 1.60/0.64    spl6_1),
% 1.60/0.64    inference(avatar_split_clause,[],[f26,f61])).
% 1.60/0.64  fof(f26,plain,(
% 1.60/0.64    sK0 = k4_tarski(sK1,sK2)),
% 1.60/0.64    inference(cnf_transformation,[],[f13])).
% 1.60/0.64  % SZS output end Proof for theBenchmark
% 1.60/0.64  % (24820)------------------------------
% 1.60/0.64  % (24820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.64  % (24820)Termination reason: Refutation
% 1.60/0.64  
% 1.60/0.64  % (24820)Memory used [KB]: 11129
% 1.60/0.64  % (24820)Time elapsed: 0.142 s
% 1.60/0.64  % (24820)------------------------------
% 1.60/0.64  % (24820)------------------------------
% 1.60/0.64  % (24813)Refutation not found, incomplete strategy% (24813)------------------------------
% 1.60/0.64  % (24813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.64  % (24813)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.64  
% 1.60/0.64  % (24813)Memory used [KB]: 10618
% 1.60/0.64  % (24813)Time elapsed: 0.222 s
% 1.60/0.64  % (24813)------------------------------
% 1.60/0.64  % (24813)------------------------------
% 1.60/0.65  % (24796)Success in time 0.275 s
%------------------------------------------------------------------------------
