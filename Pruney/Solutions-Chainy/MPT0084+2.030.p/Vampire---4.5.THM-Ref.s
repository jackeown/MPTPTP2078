%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 138 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 326 expanded)
%              Number of equality atoms :    7 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f54,f59,f68,f72,f80,f88,f93,f111,f157,f171,f178,f181])).

fof(f181,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f179,f33])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f179,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(resolution,[],[f177,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f177,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_20
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f178,plain,
    ( spl3_20
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f172,f168,f78,f175])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f168,plain,
    ( spl3_19
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f172,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(resolution,[],[f170,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f170,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f171,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f164,f155,f51,f168])).

fof(f51,plain,
    ( spl3_5
  <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f155,plain,
    ( spl3_18
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f164,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(resolution,[],[f156,f53])).

fof(f53,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f156,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f123,f109,f57,f155])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f109,plain,
    ( spl3_14
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f123,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) )
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(resolution,[],[f110,f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f110,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl3_14
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f91,f70,f109])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f102,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f92,f71])).

fof(f71,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f92,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f89,f86,f36,f91])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f89,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f29,f86])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f80,plain,
    ( spl3_10
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f73,f70,f66,f78])).

fof(f66,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f67,f71])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f54,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f46,f41,f51])).

fof(f41,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (11413)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (11413)Refutation not found, incomplete strategy% (11413)------------------------------
% 0.20/0.41  % (11413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (11413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (11413)Memory used [KB]: 10618
% 0.20/0.41  % (11413)Time elapsed: 0.004 s
% 0.20/0.41  % (11413)------------------------------
% 0.20/0.41  % (11413)------------------------------
% 0.20/0.44  % (11408)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % (11408)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f182,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f54,f59,f68,f72,f80,f88,f93,f111,f157,f171,f178,f181])).
% 0.20/0.44  fof(f181,plain,(
% 0.20/0.44    spl3_1 | ~spl3_4 | ~spl3_20),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.44  fof(f180,plain,(
% 0.20/0.44    $false | (spl3_1 | ~spl3_4 | ~spl3_20)),
% 0.20/0.44    inference(subsumption_resolution,[],[f179,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f179,plain,(
% 0.20/0.44    r1_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_20)),
% 0.20/0.44    inference(resolution,[],[f177,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    spl3_4 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    r1_xboole_0(sK1,sK0) | ~spl3_20),
% 0.20/0.44    inference(avatar_component_clause,[],[f175])).
% 0.20/0.44  fof(f175,plain,(
% 0.20/0.44    spl3_20 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.44  fof(f178,plain,(
% 0.20/0.44    spl3_20 | ~spl3_10 | ~spl3_19),
% 0.20/0.44    inference(avatar_split_clause,[],[f172,f168,f78,f175])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    spl3_10 <=> ! [X1,X0] : (~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.44  fof(f168,plain,(
% 0.20/0.44    spl3_19 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.44  fof(f172,plain,(
% 0.20/0.44    r1_xboole_0(sK1,sK0) | (~spl3_10 | ~spl3_19)),
% 0.20/0.44    inference(resolution,[],[f170,f79])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f78])).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | ~spl3_19),
% 0.20/0.44    inference(avatar_component_clause,[],[f168])).
% 0.20/0.44  fof(f171,plain,(
% 0.20/0.44    spl3_19 | ~spl3_5 | ~spl3_18),
% 0.20/0.44    inference(avatar_split_clause,[],[f164,f155,f51,f168])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl3_5 <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f155,plain,(
% 0.20/0.44    spl3_18 <=> ! [X3,X2] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.44  fof(f164,plain,(
% 0.20/0.44    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | (~spl3_5 | ~spl3_18)),
% 0.20/0.44    inference(resolution,[],[f156,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f51])).
% 0.20/0.44  fof(f156,plain,(
% 0.20/0.44    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3)) ) | ~spl3_18),
% 0.20/0.44    inference(avatar_component_clause,[],[f155])).
% 0.20/0.44  fof(f157,plain,(
% 0.20/0.44    spl3_18 | ~spl3_6 | ~spl3_14),
% 0.20/0.44    inference(avatar_split_clause,[],[f123,f109,f57,f155])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    spl3_6 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    spl3_14 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3)) ) | (~spl3_6 | ~spl3_14)),
% 0.20/0.44    inference(resolution,[],[f110,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f57])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) ) | ~spl3_14),
% 0.20/0.44    inference(avatar_component_clause,[],[f109])).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    spl3_14 | ~spl3_9 | ~spl3_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f102,f91,f70,f109])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    spl3_9 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    spl3_12 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) ) | (~spl3_9 | ~spl3_12)),
% 0.20/0.44    inference(superposition,[],[f92,f71])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f70])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ) | ~spl3_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f91])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    spl3_12 | ~spl3_2 | ~spl3_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f89,f86,f36,f91])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ) | (~spl3_2 | ~spl3_11)),
% 0.20/0.45    inference(resolution,[],[f87,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f36])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) | ~spl3_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f86])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    spl3_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f29,f86])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f24,f21,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    spl3_10 | ~spl3_8 | ~spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f73,f70,f66,f78])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    spl3_8 <=> ! [X1,X0] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) | r1_xboole_0(X0,X1)) ) | (~spl3_8 | ~spl3_9)),
% 0.20/0.45    inference(superposition,[],[f67,f71])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f66])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f70])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f28,f66])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f23,f21])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f57])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f49,f46,f41,f51])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | (~spl3_3 | ~spl3_4)),
% 0.20/0.45    inference(resolution,[],[f47,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f41])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f22,f46])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f26,f41])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.45    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f18,f36])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    r1_tarski(sK0,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ~spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f17,f31])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (11408)------------------------------
% 0.20/0.45  % (11408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (11408)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (11408)Memory used [KB]: 6140
% 0.20/0.45  % (11408)Time elapsed: 0.039 s
% 0.20/0.45  % (11408)------------------------------
% 0.20/0.45  % (11408)------------------------------
% 0.20/0.45  % (11400)Success in time 0.095 s
%------------------------------------------------------------------------------
