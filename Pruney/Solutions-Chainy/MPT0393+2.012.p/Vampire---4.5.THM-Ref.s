%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 161 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  286 ( 485 expanded)
%              Number of equality atoms :   78 ( 181 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f139,f198,f228,f259,f261])).

fof(f261,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl9_7 ),
    inference(resolution,[],[f258,f103])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl9_7
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f259,plain,
    ( spl9_1
    | spl9_4
    | ~ spl9_7
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f254,f191,f256,f195,f120])).

fof(f120,plain,
    ( spl9_1
  <=> r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f195,plain,
    ( spl9_4
  <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f191,plain,
    ( spl9_3
  <=> r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f254,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ spl9_3 ),
    inference(superposition,[],[f60,f248])).

fof(f248,plain,
    ( sK2 = sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2)
    | ~ spl9_3 ),
    inference(resolution,[],[f193,f107])).

fof(f107,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f95])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f193,plain,
    ( r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f228,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl9_4 ),
    inference(resolution,[],[f221,f150])).

fof(f150,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f149])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f75,f114])).

fof(f114,plain,(
    ! [X0] : sP0(k1_xboole_0,X0,X0) ),
    inference(superposition,[],[f108,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f108,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f221,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl9_4 ),
    inference(superposition,[],[f106,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f195])).

fof(f106,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f95])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f198,plain,
    ( spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f186,f120,f195,f191])).

fof(f186,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl9_1 ),
    inference(resolution,[],[f59,f122])).

fof(f122,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl9_2 ),
    inference(resolution,[],[f134,f106])).

fof(f134,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl9_2 ),
    inference(resolution,[],[f131,f126])).

fof(f126,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_2
  <=> r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X0),X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f73,f103])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f128,plain,
    ( ~ spl9_2
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f117,f120,f124])).

fof(f117,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2) ),
    inference(extensionality_resolution,[],[f65,f96])).

fof(f96,plain,(
    sK2 != k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f55,f95])).

fof(f55,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:08:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (18006)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (18001)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (18023)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (18015)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (18001)Refutation not found, incomplete strategy% (18001)------------------------------
% 0.22/0.53  % (18001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18001)Memory used [KB]: 1663
% 0.22/0.53  % (18001)Time elapsed: 0.095 s
% 0.22/0.53  % (18001)------------------------------
% 0.22/0.53  % (18001)------------------------------
% 0.22/0.53  % (18010)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (18005)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (18014)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (18026)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (18007)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18003)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18004)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (18002)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (18003)Refutation not found, incomplete strategy% (18003)------------------------------
% 0.22/0.54  % (18003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18003)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18003)Memory used [KB]: 10746
% 0.22/0.54  % (18003)Time elapsed: 0.128 s
% 0.22/0.54  % (18003)------------------------------
% 0.22/0.54  % (18003)------------------------------
% 0.22/0.54  % (18018)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (18022)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (18013)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18022)Refutation not found, incomplete strategy% (18022)------------------------------
% 0.22/0.54  % (18022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18027)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (18016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18017)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (18030)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (18028)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18021)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18019)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18022)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (18024)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  
% 0.22/0.55  % (18022)Memory used [KB]: 1663
% 0.22/0.55  % (18022)Time elapsed: 0.108 s
% 0.22/0.55  % (18022)------------------------------
% 0.22/0.55  % (18022)------------------------------
% 0.22/0.55  % (18021)Refutation not found, incomplete strategy% (18021)------------------------------
% 0.22/0.55  % (18021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18021)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18021)Memory used [KB]: 10746
% 0.22/0.55  % (18021)Time elapsed: 0.138 s
% 0.22/0.55  % (18021)------------------------------
% 0.22/0.55  % (18021)------------------------------
% 0.22/0.55  % (18024)Refutation not found, incomplete strategy% (18024)------------------------------
% 0.22/0.55  % (18024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18024)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18024)Memory used [KB]: 1791
% 0.22/0.55  % (18024)Time elapsed: 0.138 s
% 0.22/0.55  % (18024)------------------------------
% 0.22/0.55  % (18024)------------------------------
% 0.22/0.55  % (18008)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (18020)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18009)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (18009)Refutation not found, incomplete strategy% (18009)------------------------------
% 0.22/0.55  % (18009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18009)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18009)Memory used [KB]: 10618
% 0.22/0.55  % (18009)Time elapsed: 0.140 s
% 0.22/0.55  % (18009)------------------------------
% 0.22/0.55  % (18009)------------------------------
% 0.22/0.55  % (18011)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (18025)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (18011)Refutation not found, incomplete strategy% (18011)------------------------------
% 0.22/0.55  % (18011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18011)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18011)Memory used [KB]: 10618
% 0.22/0.55  % (18011)Time elapsed: 0.149 s
% 0.22/0.55  % (18011)------------------------------
% 0.22/0.55  % (18011)------------------------------
% 0.22/0.56  % (18029)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (18012)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (18012)Refutation not found, incomplete strategy% (18012)------------------------------
% 0.22/0.56  % (18012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18012)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18012)Memory used [KB]: 10746
% 0.22/0.56  % (18012)Time elapsed: 0.154 s
% 0.22/0.56  % (18012)------------------------------
% 0.22/0.56  % (18012)------------------------------
% 0.22/0.56  % (18013)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f128,f139,f198,f228,f259,f261])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    spl9_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    $false | spl9_7),
% 0.22/0.56    inference(resolution,[],[f258,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f258,plain,(
% 0.22/0.56    ~r1_tarski(sK2,sK2) | spl9_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f256])).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    spl9_7 <=> r1_tarski(sK2,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.56  fof(f259,plain,(
% 0.22/0.56    spl9_1 | spl9_4 | ~spl9_7 | ~spl9_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f254,f191,f256,f195,f120])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    spl9_1 <=> r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    spl9_4 <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    spl9_3 <=> r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.56  fof(f254,plain,(
% 0.22/0.56    ~r1_tarski(sK2,sK2) | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~spl9_3),
% 0.22/0.56    inference(superposition,[],[f60,f248])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    sK2 = sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2) | ~spl9_3),
% 0.22/0.56    inference(resolution,[],[f193,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f100])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.22/0.56    inference(definition_unfolding,[],[f66,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f57,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f58,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f72,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl9_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f191])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,sK3(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ~spl9_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    $false | ~spl9_4),
% 0.22/0.56    inference(resolution,[],[f221,f150])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(condensation,[],[f149])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.56    inference(resolution,[],[f75,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    ( ! [X0] : (sP0(k1_xboole_0,X0,X0)) )),
% 0.22/0.56    inference(superposition,[],[f108,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.56    inference(definition_folding,[],[f1,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(flattening,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f24])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    r2_hidden(sK2,k1_xboole_0) | ~spl9_4),
% 0.22/0.56    inference(superposition,[],[f106,f197])).
% 0.22/0.56  fof(f197,plain,(
% 0.22/0.56    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl9_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f195])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 0.22/0.56    inference(equality_resolution,[],[f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 0.22/0.56    inference(equality_resolution,[],[f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.22/0.56    inference(definition_unfolding,[],[f67,f95])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    spl9_3 | spl9_4 | spl9_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f186,f120,f195,f191])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | r2_hidden(sK3(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl9_1),
% 0.22/0.56    inference(resolution,[],[f59,f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ~r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | spl9_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f120])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    spl9_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    $false | spl9_2),
% 0.22/0.56    inference(resolution,[],[f134,f106])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl9_2),
% 0.22/0.56    inference(resolution,[],[f131,f126])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ~r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2) | spl9_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f124])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    spl9_2 <=> r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X0),X1) | ~r2_hidden(X1,X0)) )),
% 0.22/0.56    inference(resolution,[],[f73,f103])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~spl9_2 | ~spl9_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f117,f120,f124])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ~r1_tarski(sK2,k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~r1_tarski(k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2)),
% 0.22/0.56    inference(extensionality_resolution,[],[f65,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    sK2 != k1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.56    inference(definition_unfolding,[],[f55,f95])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,negated_conjecture,(
% 0.22/0.56    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.56    inference(negated_conjecture,[],[f14])).
% 0.22/0.56  fof(f14,conjecture,(
% 0.22/0.56    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (18013)------------------------------
% 0.22/0.56  % (18013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18013)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (18013)Memory used [KB]: 6268
% 0.22/0.56  % (18013)Time elapsed: 0.135 s
% 0.22/0.56  % (18013)------------------------------
% 0.22/0.56  % (18013)------------------------------
% 0.22/0.57  % (18000)Success in time 0.197 s
%------------------------------------------------------------------------------
