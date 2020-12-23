%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:27 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 236 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 ( 606 expanded)
%              Number of equality atoms :  113 ( 264 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f994,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f66,f71,f82,f307,f407,f469,f477,f574,f581,f734,f925,f942,f985,f993])).

fof(f993,plain,
    ( spl5_2
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f988])).

fof(f988,plain,
    ( $false
    | spl5_2
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f60,f60,f984,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f21,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f984,plain,
    ( r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f982])).

fof(f982,plain,
    ( spl5_41
  <=> r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f60,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f985,plain,
    ( spl5_41
    | spl5_3
    | spl5_4
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f976,f727,f68,f63,f982])).

fof(f63,plain,
    ( spl5_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_4
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f727,plain,
    ( spl5_29
  <=> sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f976,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_29 ),
    inference(trivial_inequality_removal,[],[f975])).

fof(f975,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl5_4
    | ~ spl5_29 ),
    inference(superposition,[],[f74,f729])).

fof(f729,plain,
    ( sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f727])).

fof(f74,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X2),sK1)
        | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X2),X2)
        | k1_enumset1(sK0,sK0,sK0) != X2 )
    | spl5_4 ),
    inference(superposition,[],[f70,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f26,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f70,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f942,plain,
    ( ~ spl5_25
    | ~ spl5_1
    | ~ spl5_13
    | spl5_4
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f939,f723,f68,f300,f54,f571])).

fof(f571,plain,
    ( spl5_25
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f54,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f300,plain,
    ( spl5_13
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f723,plain,
    ( spl5_28
  <=> sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f939,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_28 ),
    inference(trivial_inequality_removal,[],[f934])).

fof(f934,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl5_4
    | ~ spl5_28 ),
    inference(superposition,[],[f72,f725])).

fof(f725,plain,
    ( sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f723])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),k1_enumset1(sK0,sK0,sK2))
        | ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),sK1)
        | ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),X0)
        | k1_enumset1(sK0,sK0,sK0) != X0 )
    | spl5_4 ),
    inference(superposition,[],[f70,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f925,plain,
    ( spl5_28
    | spl5_3
    | spl5_4
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f923,f731,f68,f63,f723])).

fof(f731,plain,
    ( spl5_30
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f923,plain,
    ( r2_hidden(sK2,sK1)
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f922])).

fof(f922,plain,
    ( r2_hidden(sK2,sK1)
    | sK0 != sK0
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl5_4
    | ~ spl5_30 ),
    inference(duplicate_literal_removal,[],[f907])).

fof(f907,plain,
    ( r2_hidden(sK2,sK1)
    | sK0 != sK0
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | sK0 != sK0
    | spl5_4
    | ~ spl5_30 ),
    inference(superposition,[],[f733,f262])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | sK0 != X0
        | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0)
        | sK0 != X1 )
    | spl5_4 ),
    inference(equality_factoring,[],[f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X0
        | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0)
        | sK0 != X1 )
    | spl5_4 ),
    inference(equality_factoring,[],[f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X1
        | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1))
        | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0)
        | sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X0 )
    | spl5_4 ),
    inference(resolution,[],[f97,f49])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),X0)
        | k1_enumset1(sK0,sK0,sK0) != X0
        | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0)
        | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0) )
    | spl5_4 ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X1),k1_enumset1(sK0,sK0,sK2))
        | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X1),X1)
        | k1_enumset1(sK0,sK0,sK0) != X1 )
    | spl5_4 ),
    inference(superposition,[],[f70,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f25,f17])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f733,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f731])).

fof(f734,plain,
    ( spl5_28
    | spl5_29
    | spl5_30
    | spl5_4
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f606,f404,f68,f731,f727,f723])).

fof(f404,plain,
    ( spl5_15
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f606,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)
    | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f603])).

fof(f603,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_15 ),
    inference(resolution,[],[f590,f97])).

fof(f590,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_enumset1(sK0,sK0,sK0))
        | r2_hidden(X5,sK1) )
    | ~ spl5_15 ),
    inference(superposition,[],[f52,f405])).

fof(f405,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f404])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f17])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f581,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f46,f573])).

fof(f573,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f571])).

fof(f46,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f23,f16])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f574,plain,
    ( ~ spl5_1
    | ~ spl5_25
    | spl5_15
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f551,f474,f404,f571,f54])).

fof(f474,plain,
    ( spl5_23
  <=> sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f551,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl5_15
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f550])).

fof(f550,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl5_15
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl5_15
    | ~ spl5_23 ),
    inference(superposition,[],[f505,f476])).

fof(f476,plain,
    ( sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f474])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),k1_enumset1(sK0,sK0,sK0))
        | k1_enumset1(sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),X0)
        | ~ r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),sK1) )
    | spl5_15 ),
    inference(superposition,[],[f406,f44])).

fof(f406,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f404])).

fof(f477,plain,
    ( spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f471,f466,f474])).

fof(f466,plain,
    ( spl5_22
  <=> r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f471,plain,
    ( sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_22 ),
    inference(duplicate_literal_removal,[],[f470])).

fof(f470,plain,
    ( sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_22 ),
    inference(resolution,[],[f468,f49])).

fof(f468,plain,
    ( r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f466])).

fof(f469,plain,
    ( spl5_22
    | spl5_15 ),
    inference(avatar_split_clause,[],[f463,f404,f466])).

fof(f463,plain,
    ( r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl5_15 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl5_15 ),
    inference(factoring,[],[f410])).

fof(f410,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X2),k1_enumset1(sK0,sK0,sK0))
        | r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X2),X2)
        | k1_enumset1(sK0,sK0,sK0) != X2 )
    | spl5_15 ),
    inference(superposition,[],[f406,f42])).

fof(f407,plain,
    ( ~ spl5_15
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f339,f78,f59,f404])).

fof(f78,plain,
    ( spl5_5
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f339,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl5_2
    | spl5_5 ),
    inference(backward_demodulation,[],[f80,f61])).

fof(f61,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f80,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f307,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f48,f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f300])).

fof(f48,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f22,f16])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,
    ( ~ spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f76,f68,f78])).

fof(f76,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2)))
    | spl5_4 ),
    inference(superposition,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f17,f17])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f13,f30,f17,f16])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f66,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f11,f63,f59])).

fof(f11,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f12,f54])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (21564)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (21580)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (21572)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (21580)Refutation not found, incomplete strategy% (21580)------------------------------
% 0.21/0.54  % (21580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21580)Memory used [KB]: 1663
% 0.21/0.54  % (21580)Time elapsed: 0.116 s
% 0.21/0.54  % (21580)------------------------------
% 0.21/0.54  % (21580)------------------------------
% 0.21/0.54  % (21586)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (21569)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (21568)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (21566)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (21567)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (21585)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (21588)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (21590)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (21591)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (21576)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (21570)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (21582)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (21587)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (21592)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (21578)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (21584)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (21577)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.56  % (21571)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.56  % (21575)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.56  % (21583)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.56  % (21589)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.56  % (21574)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.56  % (21577)Refutation not found, incomplete strategy% (21577)------------------------------
% 1.46/0.56  % (21577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (21577)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (21577)Memory used [KB]: 1663
% 1.46/0.56  % (21577)Time elapsed: 0.150 s
% 1.46/0.56  % (21577)------------------------------
% 1.46/0.56  % (21577)------------------------------
% 1.46/0.57  % (21563)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.57  % (21565)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.46/0.57  % (21579)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.57  % (21579)Refutation not found, incomplete strategy% (21579)------------------------------
% 1.46/0.57  % (21579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (21579)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (21579)Memory used [KB]: 10618
% 1.46/0.57  % (21579)Time elapsed: 0.161 s
% 1.46/0.57  % (21579)------------------------------
% 1.46/0.57  % (21579)------------------------------
% 1.60/0.58  % (21573)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.60/0.59  % (21581)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.03/0.64  % (21591)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f994,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(avatar_sat_refutation,[],[f57,f66,f71,f82,f307,f407,f469,f477,f574,f581,f734,f925,f942,f985,f993])).
% 2.03/0.64  fof(f993,plain,(
% 2.03/0.64    spl5_2 | ~spl5_41),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f988])).
% 2.03/0.64  fof(f988,plain,(
% 2.03/0.64    $false | (spl5_2 | ~spl5_41)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f60,f60,f984,f49])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 2.03/0.64    inference(equality_resolution,[],[f35])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 2.03/0.64    inference(definition_unfolding,[],[f21,f16])).
% 2.03/0.64  fof(f16,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.03/0.64  fof(f21,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.03/0.64  fof(f984,plain,(
% 2.03/0.64    r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0)) | ~spl5_41),
% 2.03/0.64    inference(avatar_component_clause,[],[f982])).
% 2.03/0.64  fof(f982,plain,(
% 2.03/0.64    spl5_41 <=> r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.03/0.64  fof(f60,plain,(
% 2.03/0.64    sK0 != sK2 | spl5_2),
% 2.03/0.64    inference(avatar_component_clause,[],[f59])).
% 2.03/0.64  fof(f59,plain,(
% 2.03/0.64    spl5_2 <=> sK0 = sK2),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.03/0.64  fof(f985,plain,(
% 2.03/0.64    spl5_41 | spl5_3 | spl5_4 | ~spl5_29),
% 2.03/0.64    inference(avatar_split_clause,[],[f976,f727,f68,f63,f982])).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    spl5_3 <=> r2_hidden(sK2,sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.03/0.64  fof(f68,plain,(
% 2.03/0.64    spl5_4 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.03/0.64  fof(f727,plain,(
% 2.03/0.64    spl5_29 <=> sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.03/0.64  fof(f976,plain,(
% 2.03/0.64    r2_hidden(sK2,sK1) | r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0)) | (spl5_4 | ~spl5_29)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f975])).
% 2.03/0.64  fof(f975,plain,(
% 2.03/0.64    r2_hidden(sK2,sK1) | r2_hidden(sK2,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | (spl5_4 | ~spl5_29)),
% 2.03/0.64    inference(superposition,[],[f74,f729])).
% 2.03/0.64  fof(f729,plain,(
% 2.03/0.64    sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl5_29),
% 2.03/0.64    inference(avatar_component_clause,[],[f727])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    ( ! [X2] : (r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X2),sK1) | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X2),X2) | k1_enumset1(sK0,sK0,sK0) != X2) ) | spl5_4),
% 2.03/0.64    inference(superposition,[],[f70,f42])).
% 2.03/0.64  fof(f42,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f26,f17])).
% 2.03/0.64  fof(f17,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f3])).
% 2.03/0.64  fof(f3,axiom,(
% 2.03/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.03/0.64  fof(f26,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f2])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1)) | spl5_4),
% 2.03/0.64    inference(avatar_component_clause,[],[f68])).
% 2.03/0.64  fof(f942,plain,(
% 2.03/0.64    ~spl5_25 | ~spl5_1 | ~spl5_13 | spl5_4 | ~spl5_28),
% 2.03/0.64    inference(avatar_split_clause,[],[f939,f723,f68,f300,f54,f571])).
% 2.03/0.64  fof(f571,plain,(
% 2.03/0.64    spl5_25 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.03/0.64  fof(f54,plain,(
% 2.03/0.64    spl5_1 <=> r2_hidden(sK0,sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.03/0.64  fof(f300,plain,(
% 2.03/0.64    spl5_13 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.03/0.64  fof(f723,plain,(
% 2.03/0.64    spl5_28 <=> sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.03/0.64  fof(f939,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | (spl5_4 | ~spl5_28)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f934])).
% 2.03/0.64  fof(f934,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | (spl5_4 | ~spl5_28)),
% 2.03/0.64    inference(superposition,[],[f72,f725])).
% 2.03/0.64  fof(f725,plain,(
% 2.03/0.64    sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl5_28),
% 2.03/0.64    inference(avatar_component_clause,[],[f723])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ( ! [X0] : (~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),k1_enumset1(sK0,sK0,sK2)) | ~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),sK1) | ~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),X0) | k1_enumset1(sK0,sK0,sK0) != X0) ) | spl5_4),
% 2.03/0.64    inference(superposition,[],[f70,f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f24,f17])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f2])).
% 2.03/0.64  fof(f925,plain,(
% 2.03/0.64    spl5_28 | spl5_3 | spl5_4 | ~spl5_30),
% 2.03/0.64    inference(avatar_split_clause,[],[f923,f731,f68,f63,f723])).
% 2.03/0.64  fof(f731,plain,(
% 2.03/0.64    spl5_30 <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.03/0.64  fof(f923,plain,(
% 2.03/0.64    r2_hidden(sK2,sK1) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | (spl5_4 | ~spl5_30)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f922])).
% 2.03/0.64  fof(f922,plain,(
% 2.03/0.64    r2_hidden(sK2,sK1) | sK0 != sK0 | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | (spl5_4 | ~spl5_30)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f907])).
% 2.03/0.64  fof(f907,plain,(
% 2.03/0.64    r2_hidden(sK2,sK1) | sK0 != sK0 | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | sK0 != sK0 | (spl5_4 | ~spl5_30)),
% 2.03/0.64    inference(superposition,[],[f733,f262])).
% 2.03/0.64  fof(f262,plain,(
% 2.03/0.64    ( ! [X0,X1] : (sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | sK0 != X0 | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0) | sK0 != X1) ) | spl5_4),
% 2.03/0.64    inference(equality_factoring,[],[f175])).
% 2.03/0.64  fof(f175,plain,(
% 2.03/0.64    ( ! [X0,X1] : (sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X0 | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0) | sK0 != X1) ) | spl5_4),
% 2.03/0.64    inference(equality_factoring,[],[f113])).
% 2.03/0.64  fof(f113,plain,(
% 2.03/0.64    ( ! [X0,X1] : (sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X1 | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) | k1_enumset1(X0,X0,X1) != k1_enumset1(sK0,sK0,sK0) | sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(X0,X0,X1)) = X0) ) | spl5_4),
% 2.03/0.64    inference(resolution,[],[f97,f49])).
% 2.03/0.64  fof(f97,plain,(
% 2.03/0.64    ( ! [X0] : (r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0),X0) | k1_enumset1(sK0,sK0,sK0) != X0 | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,X0)) ) | spl5_4),
% 2.03/0.64    inference(resolution,[],[f73,f49])).
% 2.03/0.64  fof(f73,plain,(
% 2.03/0.64    ( ! [X1] : (r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X1),k1_enumset1(sK0,sK0,sK2)) | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,X1),X1) | k1_enumset1(sK0,sK0,sK0) != X1) ) | spl5_4),
% 2.03/0.64    inference(superposition,[],[f70,f43])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f25,f17])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f2])).
% 2.03/0.64  fof(f733,plain,(
% 2.03/0.64    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) | ~spl5_30),
% 2.03/0.64    inference(avatar_component_clause,[],[f731])).
% 2.03/0.64  fof(f734,plain,(
% 2.03/0.64    spl5_28 | spl5_29 | spl5_30 | spl5_4 | ~spl5_15),
% 2.03/0.64    inference(avatar_split_clause,[],[f606,f404,f68,f731,f727,f723])).
% 2.03/0.64  fof(f404,plain,(
% 2.03/0.64    spl5_15 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.03/0.64  fof(f606,plain,(
% 2.03/0.64    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | (spl5_4 | ~spl5_15)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f603])).
% 2.03/0.64  fof(f603,plain,(
% 2.03/0.64    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | sK2 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | sK0 = sK4(k1_enumset1(sK0,sK0,sK2),sK1,k1_enumset1(sK0,sK0,sK0)) | (spl5_4 | ~spl5_15)),
% 2.03/0.64    inference(resolution,[],[f590,f97])).
% 2.03/0.64  fof(f590,plain,(
% 2.03/0.64    ( ! [X5] : (~r2_hidden(X5,k1_enumset1(sK0,sK0,sK0)) | r2_hidden(X5,sK1)) ) | ~spl5_15),
% 2.03/0.64    inference(superposition,[],[f52,f405])).
% 2.03/0.64  fof(f405,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl5_15),
% 2.03/0.64    inference(avatar_component_clause,[],[f404])).
% 2.03/0.64  fof(f52,plain,(
% 2.03/0.64    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f41])).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.03/0.64    inference(definition_unfolding,[],[f27,f17])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f2])).
% 2.03/0.64  fof(f581,plain,(
% 2.03/0.64    spl5_25),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f576])).
% 2.03/0.64  fof(f576,plain,(
% 2.03/0.64    $false | spl5_25),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f46,f573])).
% 2.03/0.64  fof(f573,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl5_25),
% 2.03/0.64    inference(avatar_component_clause,[],[f571])).
% 2.03/0.64  fof(f46,plain,(
% 2.03/0.64    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 2.03/0.64    inference(equality_resolution,[],[f45])).
% 2.03/0.64  fof(f45,plain,(
% 2.03/0.64    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 2.03/0.64    inference(equality_resolution,[],[f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 2.03/0.64    inference(definition_unfolding,[],[f23,f16])).
% 2.03/0.64  fof(f23,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f4])).
% 2.03/0.64  fof(f574,plain,(
% 2.03/0.64    ~spl5_1 | ~spl5_25 | spl5_15 | ~spl5_23),
% 2.03/0.64    inference(avatar_split_clause,[],[f551,f474,f404,f571,f54])).
% 2.03/0.64  fof(f474,plain,(
% 2.03/0.64    spl5_23 <=> sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.03/0.64  fof(f551,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl5_15 | ~spl5_23)),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f550])).
% 2.03/0.64  fof(f550,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK0,sK1) | (spl5_15 | ~spl5_23)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f549])).
% 2.03/0.64  fof(f549,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl5_15 | ~spl5_23)),
% 2.03/0.64    inference(superposition,[],[f505,f476])).
% 2.03/0.64  fof(f476,plain,(
% 2.03/0.64    sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl5_23),
% 2.03/0.64    inference(avatar_component_clause,[],[f474])).
% 2.03/0.64  fof(f505,plain,(
% 2.03/0.64    ( ! [X0] : (~r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != X0 | ~r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),X0) | ~r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X0),sK1)) ) | spl5_15),
% 2.03/0.64    inference(superposition,[],[f406,f44])).
% 2.03/0.64  fof(f406,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl5_15),
% 2.03/0.64    inference(avatar_component_clause,[],[f404])).
% 2.03/0.64  fof(f477,plain,(
% 2.03/0.64    spl5_23 | ~spl5_22),
% 2.03/0.64    inference(avatar_split_clause,[],[f471,f466,f474])).
% 2.03/0.64  fof(f466,plain,(
% 2.03/0.64    spl5_22 <=> r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.03/0.64  fof(f471,plain,(
% 2.03/0.64    sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl5_22),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f470])).
% 2.03/0.64  fof(f470,plain,(
% 2.03/0.64    sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | sK0 = sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl5_22),
% 2.03/0.64    inference(resolution,[],[f468,f49])).
% 2.03/0.64  fof(f468,plain,(
% 2.03/0.64    r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~spl5_22),
% 2.03/0.64    inference(avatar_component_clause,[],[f466])).
% 2.03/0.64  fof(f469,plain,(
% 2.03/0.64    spl5_22 | spl5_15),
% 2.03/0.64    inference(avatar_split_clause,[],[f463,f404,f466])).
% 2.03/0.64  fof(f463,plain,(
% 2.03/0.64    r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl5_15),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f462])).
% 2.03/0.64  fof(f462,plain,(
% 2.03/0.64    r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | spl5_15),
% 2.03/0.64    inference(factoring,[],[f410])).
% 2.03/0.64  fof(f410,plain,(
% 2.03/0.64    ( ! [X2] : (r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X2),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK4(sK1,k1_enumset1(sK0,sK0,sK0),X2),X2) | k1_enumset1(sK0,sK0,sK0) != X2) ) | spl5_15),
% 2.03/0.64    inference(superposition,[],[f406,f42])).
% 2.03/0.64  fof(f407,plain,(
% 2.03/0.64    ~spl5_15 | ~spl5_2 | spl5_5),
% 2.03/0.64    inference(avatar_split_clause,[],[f339,f78,f59,f404])).
% 2.03/0.64  fof(f78,plain,(
% 2.03/0.64    spl5_5 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.03/0.64  fof(f339,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | (~spl5_2 | spl5_5)),
% 2.03/0.64    inference(backward_demodulation,[],[f80,f61])).
% 2.03/0.64  fof(f61,plain,(
% 2.03/0.64    sK0 = sK2 | ~spl5_2),
% 2.03/0.64    inference(avatar_component_clause,[],[f59])).
% 2.03/0.64  fof(f80,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2))) | spl5_5),
% 2.03/0.64    inference(avatar_component_clause,[],[f78])).
% 2.03/0.64  fof(f307,plain,(
% 2.03/0.64    spl5_13),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f304])).
% 2.03/0.64  fof(f304,plain,(
% 2.03/0.64    $false | spl5_13),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f48,f302])).
% 2.03/0.64  fof(f302,plain,(
% 2.03/0.64    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK2)) | spl5_13),
% 2.03/0.64    inference(avatar_component_clause,[],[f300])).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 2.03/0.64    inference(equality_resolution,[],[f47])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 2.03/0.64    inference(equality_resolution,[],[f34])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 2.03/0.64    inference(definition_unfolding,[],[f22,f16])).
% 2.03/0.64  fof(f22,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f4])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    ~spl5_5 | spl5_4),
% 2.03/0.64    inference(avatar_split_clause,[],[f76,f68,f78])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK2))) | spl5_4),
% 2.03/0.64    inference(superposition,[],[f70,f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f15,f17,f17])).
% 2.03/0.64  fof(f15,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f1])).
% 2.03/0.64  fof(f1,axiom,(
% 2.03/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    ~spl5_4),
% 2.03/0.64    inference(avatar_split_clause,[],[f31,f68])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK2),k4_xboole_0(k1_enumset1(sK0,sK0,sK2),sK1))),
% 2.03/0.65    inference(definition_unfolding,[],[f13,f30,f17,f16])).
% 2.03/0.65  fof(f30,plain,(
% 2.03/0.65    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.03/0.65    inference(definition_unfolding,[],[f14,f16])).
% 2.03/0.65  fof(f14,plain,(
% 2.03/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f5])).
% 2.03/0.65  fof(f5,axiom,(
% 2.03/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.03/0.65  fof(f13,plain,(
% 2.03/0.65    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 2.03/0.65    inference(cnf_transformation,[],[f10])).
% 2.03/0.65  fof(f10,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.03/0.65    inference(flattening,[],[f9])).
% 2.03/0.65  fof(f9,plain,(
% 2.03/0.65    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 2.03/0.65    inference(ennf_transformation,[],[f8])).
% 2.03/0.65  fof(f8,negated_conjecture,(
% 2.03/0.65    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.03/0.65    inference(negated_conjecture,[],[f7])).
% 2.03/0.65  fof(f7,conjecture,(
% 2.03/0.65    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.03/0.65  fof(f66,plain,(
% 2.03/0.65    spl5_2 | ~spl5_3),
% 2.03/0.65    inference(avatar_split_clause,[],[f11,f63,f59])).
% 2.03/0.65  fof(f11,plain,(
% 2.03/0.65    ~r2_hidden(sK2,sK1) | sK0 = sK2),
% 2.03/0.65    inference(cnf_transformation,[],[f10])).
% 2.03/0.65  fof(f57,plain,(
% 2.03/0.65    spl5_1),
% 2.03/0.65    inference(avatar_split_clause,[],[f12,f54])).
% 2.03/0.65  fof(f12,plain,(
% 2.03/0.65    r2_hidden(sK0,sK1)),
% 2.03/0.65    inference(cnf_transformation,[],[f10])).
% 2.03/0.65  % SZS output end Proof for theBenchmark
% 2.03/0.65  % (21591)------------------------------
% 2.03/0.65  % (21591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.65  % (21591)Termination reason: Refutation
% 2.03/0.65  
% 2.03/0.65  % (21591)Memory used [KB]: 11129
% 2.03/0.65  % (21591)Time elapsed: 0.213 s
% 2.03/0.65  % (21591)------------------------------
% 2.03/0.65  % (21591)------------------------------
% 2.03/0.65  % (21562)Success in time 0.276 s
%------------------------------------------------------------------------------
