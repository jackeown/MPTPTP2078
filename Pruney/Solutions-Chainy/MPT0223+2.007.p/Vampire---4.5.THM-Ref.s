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
% DateTime   : Thu Dec  3 12:35:51 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 108 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 282 expanded)
%              Number of equality atoms :  152 ( 206 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f103,f135,f153])).

fof(f153,plain,
    ( spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f81,f72,f145])).

fof(f145,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_enumset1(sK1,sK1,sK1,sK0))
        | sK1 = X5 )
    | ~ spl4_6 ),
    inference(superposition,[],[f70,f133])).

fof(f133,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_6
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f72,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

% (12123)Refutation not found, incomplete strategy% (12123)------------------------------
% (12123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12123)Termination reason: Refutation not found, incomplete strategy

% (12123)Memory used [KB]: 1663
% (12123)Time elapsed: 0.089 s
% (12123)------------------------------
% (12123)------------------------------
% (12136)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f81,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f135,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f126,f100,f131])).

fof(f100,plain,
    ( spl4_4
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f126,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f102,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f32,f47,f52])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f102,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f92,f84,f100])).

fof(f84,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(superposition,[],[f88,f86])).

fof(f86,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f87,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f54,f84])).

fof(f54,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f52,f52,f52])).

fof(f28,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f82,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:42:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (810975232)
% 0.20/0.37  ipcrm: permission denied for id (811008001)
% 0.20/0.37  ipcrm: permission denied for id (811073539)
% 0.20/0.37  ipcrm: permission denied for id (814284804)
% 0.20/0.37  ipcrm: permission denied for id (814317573)
% 0.20/0.37  ipcrm: permission denied for id (814350342)
% 0.20/0.37  ipcrm: permission denied for id (811204616)
% 0.20/0.38  ipcrm: permission denied for id (811237385)
% 0.20/0.38  ipcrm: permission denied for id (814481420)
% 0.20/0.38  ipcrm: permission denied for id (814546958)
% 0.20/0.38  ipcrm: permission denied for id (814579727)
% 0.20/0.39  ipcrm: permission denied for id (811368465)
% 0.20/0.39  ipcrm: permission denied for id (814645266)
% 0.20/0.39  ipcrm: permission denied for id (811434003)
% 0.20/0.39  ipcrm: permission denied for id (814710805)
% 0.20/0.39  ipcrm: permission denied for id (814809112)
% 0.20/0.40  ipcrm: permission denied for id (811565081)
% 0.20/0.40  ipcrm: permission denied for id (811597851)
% 0.20/0.40  ipcrm: permission denied for id (814874652)
% 0.20/0.40  ipcrm: permission denied for id (814907421)
% 0.20/0.40  ipcrm: permission denied for id (814940190)
% 0.20/0.40  ipcrm: permission denied for id (811663391)
% 0.20/0.40  ipcrm: permission denied for id (811696160)
% 0.20/0.41  ipcrm: permission denied for id (811728929)
% 0.20/0.41  ipcrm: permission denied for id (811761698)
% 0.20/0.41  ipcrm: permission denied for id (815005732)
% 0.20/0.41  ipcrm: permission denied for id (815038501)
% 0.20/0.41  ipcrm: permission denied for id (815071270)
% 0.20/0.41  ipcrm: permission denied for id (811892775)
% 0.20/0.41  ipcrm: permission denied for id (811925544)
% 0.20/0.42  ipcrm: permission denied for id (811958313)
% 0.20/0.42  ipcrm: permission denied for id (811991082)
% 0.20/0.42  ipcrm: permission denied for id (812023851)
% 0.20/0.42  ipcrm: permission denied for id (812056620)
% 0.20/0.42  ipcrm: permission denied for id (812089390)
% 0.20/0.43  ipcrm: permission denied for id (815202353)
% 0.20/0.43  ipcrm: permission denied for id (815235122)
% 0.20/0.43  ipcrm: permission denied for id (812220468)
% 0.20/0.43  ipcrm: permission denied for id (812253238)
% 0.20/0.43  ipcrm: permission denied for id (812286007)
% 0.21/0.44  ipcrm: permission denied for id (815366201)
% 0.21/0.44  ipcrm: permission denied for id (812384314)
% 0.21/0.44  ipcrm: permission denied for id (812449852)
% 0.21/0.44  ipcrm: permission denied for id (812482621)
% 0.21/0.44  ipcrm: permission denied for id (815431742)
% 0.21/0.44  ipcrm: permission denied for id (812548159)
% 0.21/0.45  ipcrm: permission denied for id (812580929)
% 0.21/0.45  ipcrm: permission denied for id (812646468)
% 0.21/0.45  ipcrm: permission denied for id (812679237)
% 0.21/0.45  ipcrm: permission denied for id (812712006)
% 0.21/0.45  ipcrm: permission denied for id (812744775)
% 0.21/0.45  ipcrm: permission denied for id (815562824)
% 0.21/0.46  ipcrm: permission denied for id (812810314)
% 0.21/0.46  ipcrm: permission denied for id (812843083)
% 0.21/0.46  ipcrm: permission denied for id (812875852)
% 0.21/0.46  ipcrm: permission denied for id (815661134)
% 0.21/0.47  ipcrm: permission denied for id (815759441)
% 0.21/0.47  ipcrm: permission denied for id (812974162)
% 0.21/0.47  ipcrm: permission denied for id (813039700)
% 0.21/0.47  ipcrm: permission denied for id (815857749)
% 0.21/0.47  ipcrm: permission denied for id (813105238)
% 0.21/0.47  ipcrm: permission denied for id (813138007)
% 0.21/0.47  ipcrm: permission denied for id (815890520)
% 0.21/0.48  ipcrm: permission denied for id (815923289)
% 0.21/0.48  ipcrm: permission denied for id (813236316)
% 0.21/0.48  ipcrm: permission denied for id (813269085)
% 0.21/0.48  ipcrm: permission denied for id (816021598)
% 0.21/0.48  ipcrm: permission denied for id (816054367)
% 0.21/0.48  ipcrm: permission denied for id (813367392)
% 0.21/0.49  ipcrm: permission denied for id (813432930)
% 0.21/0.49  ipcrm: permission denied for id (816185445)
% 0.21/0.49  ipcrm: permission denied for id (816250983)
% 0.21/0.49  ipcrm: permission denied for id (816283752)
% 0.21/0.50  ipcrm: permission denied for id (813629546)
% 0.21/0.50  ipcrm: permission denied for id (813662315)
% 0.21/0.50  ipcrm: permission denied for id (813695084)
% 0.21/0.50  ipcrm: permission denied for id (813727853)
% 0.21/0.50  ipcrm: permission denied for id (813760622)
% 0.21/0.50  ipcrm: permission denied for id (816382064)
% 0.21/0.51  ipcrm: permission denied for id (813858930)
% 0.21/0.51  ipcrm: permission denied for id (813957236)
% 0.21/0.51  ipcrm: permission denied for id (813990005)
% 0.21/0.51  ipcrm: permission denied for id (816578680)
% 0.21/0.52  ipcrm: permission denied for id (816644218)
% 0.21/0.52  ipcrm: permission denied for id (814153852)
% 0.21/0.52  ipcrm: permission denied for id (816709757)
% 0.21/0.52  ipcrm: permission denied for id (814186622)
% 0.21/0.52  ipcrm: permission denied for id (814219391)
% 1.25/0.69  % (12146)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.69  % (12144)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.25/0.70  % (12126)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.70  % (12123)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.70  % (12130)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.70  % (12146)Refutation found. Thanks to Tanya!
% 1.25/0.70  % SZS status Theorem for theBenchmark
% 1.25/0.70  % SZS output start Proof for theBenchmark
% 1.25/0.70  fof(f154,plain,(
% 1.25/0.70    $false),
% 1.25/0.70    inference(avatar_sat_refutation,[],[f82,f87,f103,f135,f153])).
% 1.25/0.70  fof(f153,plain,(
% 1.25/0.70    spl4_1 | ~spl4_6),
% 1.25/0.70    inference(avatar_contradiction_clause,[],[f149])).
% 1.25/0.70  fof(f149,plain,(
% 1.25/0.70    $false | (spl4_1 | ~spl4_6)),
% 1.25/0.70    inference(unit_resulting_resolution,[],[f81,f72,f145])).
% 1.25/0.70  fof(f145,plain,(
% 1.25/0.70    ( ! [X5] : (~r2_hidden(X5,k2_enumset1(sK1,sK1,sK1,sK0)) | sK1 = X5) ) | ~spl4_6),
% 1.25/0.70    inference(superposition,[],[f70,f133])).
% 1.25/0.70  fof(f133,plain,(
% 1.25/0.70    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0) | ~spl4_6),
% 1.25/0.70    inference(avatar_component_clause,[],[f131])).
% 1.25/0.70  fof(f131,plain,(
% 1.25/0.70    spl4_6 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0)),
% 1.25/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.25/0.70  fof(f70,plain,(
% 1.25/0.70    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.25/0.70    inference(equality_resolution,[],[f58])).
% 1.25/0.70  fof(f58,plain,(
% 1.25/0.70    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.25/0.70    inference(definition_unfolding,[],[f33,f52])).
% 1.25/0.70  fof(f52,plain,(
% 1.25/0.70    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.70    inference(definition_unfolding,[],[f37,f51])).
% 1.25/0.70  fof(f51,plain,(
% 1.25/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.70    inference(definition_unfolding,[],[f48,f47])).
% 1.25/0.70  fof(f47,plain,(
% 1.25/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.25/0.70    inference(cnf_transformation,[],[f9])).
% 1.25/0.70  fof(f9,axiom,(
% 1.25/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.25/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.70  fof(f48,plain,(
% 1.25/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.70    inference(cnf_transformation,[],[f8])).
% 1.25/0.70  fof(f8,axiom,(
% 1.25/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.70  fof(f37,plain,(
% 1.25/0.70    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.25/0.70    inference(cnf_transformation,[],[f7])).
% 1.25/0.70  fof(f7,axiom,(
% 1.25/0.70    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.25/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.70  fof(f33,plain,(
% 1.25/0.70    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.25/0.70    inference(cnf_transformation,[],[f22])).
% 1.25/0.70  fof(f22,plain,(
% 1.25/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.25/0.70  fof(f21,plain,(
% 1.25/0.70    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.25/0.70    introduced(choice_axiom,[])).
% 1.25/0.70  fof(f20,plain,(
% 1.25/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.70    inference(rectify,[],[f19])).
% 1.25/0.70  fof(f19,plain,(
% 1.25/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.70    inference(nnf_transformation,[],[f5])).
% 1.25/0.70  fof(f5,axiom,(
% 1.25/0.70    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.25/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.25/0.70  fof(f72,plain,(
% 1.25/0.70    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.25/0.70    inference(equality_resolution,[],[f71])).
% 1.25/0.70  fof(f71,plain,(
% 1.25/0.70    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.25/0.70    inference(equality_resolution,[],[f63])).
% 1.25/0.70  fof(f63,plain,(
% 1.25/0.70    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.25/0.70    inference(definition_unfolding,[],[f42,f47])).
% 1.25/0.70  fof(f42,plain,(
% 1.25/0.70    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.25/0.70    inference(cnf_transformation,[],[f27])).
% 1.25/0.70  % (12123)Refutation not found, incomplete strategy% (12123)------------------------------
% 1.25/0.70  % (12123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.70  % (12123)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.70  
% 1.25/0.70  % (12123)Memory used [KB]: 1663
% 1.25/0.71  % (12123)Time elapsed: 0.089 s
% 1.25/0.71  % (12123)------------------------------
% 1.25/0.71  % (12123)------------------------------
% 1.25/0.71  % (12136)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.71  fof(f27,plain,(
% 1.25/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.25/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.25/0.71  fof(f26,plain,(
% 1.25/0.71    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.25/0.71    introduced(choice_axiom,[])).
% 1.25/0.71  fof(f25,plain,(
% 1.25/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.25/0.71    inference(rectify,[],[f24])).
% 1.25/0.71  fof(f24,plain,(
% 1.25/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.25/0.71    inference(flattening,[],[f23])).
% 1.25/0.71  fof(f23,plain,(
% 1.25/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.25/0.71    inference(nnf_transformation,[],[f16])).
% 1.25/0.71  fof(f16,plain,(
% 1.25/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.25/0.71    inference(ennf_transformation,[],[f4])).
% 1.25/0.71  fof(f4,axiom,(
% 1.25/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.25/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.25/0.71  fof(f81,plain,(
% 1.25/0.71    sK0 != sK1 | spl4_1),
% 1.25/0.71    inference(avatar_component_clause,[],[f79])).
% 1.25/0.71  fof(f79,plain,(
% 1.25/0.71    spl4_1 <=> sK0 = sK1),
% 1.25/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.25/0.71  fof(f135,plain,(
% 1.25/0.71    spl4_6 | ~spl4_4),
% 1.25/0.71    inference(avatar_split_clause,[],[f126,f100,f131])).
% 1.25/0.71  fof(f100,plain,(
% 1.25/0.71    spl4_4 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.25/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.25/0.71  fof(f126,plain,(
% 1.25/0.71    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK0) | ~spl4_4),
% 1.25/0.71    inference(superposition,[],[f102,f53])).
% 1.25/0.71  fof(f53,plain,(
% 1.25/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 1.25/0.71    inference(definition_unfolding,[],[f32,f47,f52])).
% 1.25/0.71  fof(f32,plain,(
% 1.25/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.25/0.71    inference(cnf_transformation,[],[f6])).
% 1.25/0.71  fof(f6,axiom,(
% 1.25/0.71    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.25/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.25/0.71  fof(f102,plain,(
% 1.25/0.71    k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_4),
% 1.25/0.71    inference(avatar_component_clause,[],[f100])).
% 1.25/0.71  fof(f103,plain,(
% 1.25/0.71    spl4_4 | ~spl4_2),
% 1.25/0.71    inference(avatar_split_clause,[],[f92,f84,f100])).
% 1.25/0.71  fof(f84,plain,(
% 1.25/0.71    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.25/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.25/0.71  fof(f92,plain,(
% 1.25/0.71    k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_2),
% 1.25/0.71    inference(superposition,[],[f88,f86])).
% 1.25/0.71  fof(f86,plain,(
% 1.25/0.71    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_2),
% 1.25/0.71    inference(avatar_component_clause,[],[f84])).
% 1.25/0.71  fof(f88,plain,(
% 1.25/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 1.25/0.71    inference(superposition,[],[f30,f31])).
% 1.25/0.71  fof(f31,plain,(
% 1.25/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.25/0.71    inference(cnf_transformation,[],[f2])).
% 1.25/0.71  fof(f2,axiom,(
% 1.25/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.25/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.25/0.71  fof(f30,plain,(
% 1.25/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.25/0.71    inference(cnf_transformation,[],[f3])).
% 1.25/0.71  fof(f3,axiom,(
% 1.25/0.71    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.25/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.25/0.71  fof(f87,plain,(
% 1.25/0.71    spl4_2),
% 1.25/0.71    inference(avatar_split_clause,[],[f54,f84])).
% 1.25/0.71  fof(f54,plain,(
% 1.25/0.71    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.25/0.71    inference(definition_unfolding,[],[f28,f52,f52,f52])).
% 1.25/0.71  fof(f28,plain,(
% 1.25/0.71    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.25/0.71    inference(cnf_transformation,[],[f18])).
% 1.25/0.71  fof(f18,plain,(
% 1.25/0.71    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.25/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.25/0.71  fof(f17,plain,(
% 1.25/0.71    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.25/0.71    introduced(choice_axiom,[])).
% 1.25/0.71  fof(f15,plain,(
% 1.25/0.71    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.25/0.71    inference(ennf_transformation,[],[f14])).
% 1.25/0.71  fof(f14,negated_conjecture,(
% 1.25/0.71    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.25/0.71    inference(negated_conjecture,[],[f13])).
% 1.25/0.71  fof(f13,conjecture,(
% 1.25/0.71    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.25/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.25/0.71  fof(f82,plain,(
% 1.25/0.71    ~spl4_1),
% 1.25/0.71    inference(avatar_split_clause,[],[f29,f79])).
% 1.25/0.71  fof(f29,plain,(
% 1.25/0.71    sK0 != sK1),
% 1.25/0.71    inference(cnf_transformation,[],[f18])).
% 1.25/0.71  % SZS output end Proof for theBenchmark
% 1.25/0.71  % (12146)------------------------------
% 1.25/0.71  % (12146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.71  % (12146)Termination reason: Refutation
% 1.25/0.71  
% 1.25/0.71  % (12146)Memory used [KB]: 10746
% 1.25/0.71  % (12146)Time elapsed: 0.076 s
% 1.25/0.71  % (12146)------------------------------
% 1.25/0.71  % (12146)------------------------------
% 1.25/0.71  % (11985)Success in time 0.348 s
%------------------------------------------------------------------------------
