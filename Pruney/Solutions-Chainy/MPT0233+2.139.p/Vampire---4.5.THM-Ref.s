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
% DateTime   : Thu Dec  3 12:37:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 330 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  365 (1320 expanded)
%              Number of equality atoms :  210 ( 935 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f117,f191,f212,f221,f248,f256,f265,f280,f289,f352,f353,f372,f411,f412,f416])).

% (21512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f416,plain,
    ( sK1 != sK2
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f412,plain,
    ( sK0 != sK1
    | sK1 != sK3
    | sK0 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f411,plain,
    ( spl5_13
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl5_13
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f255,f73,f390])).

fof(f390,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1 )
    | ~ spl5_20 ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1
        | sK1 = X1
        | sK1 = X1 )
    | ~ spl5_20 ),
    inference(superposition,[],[f74,f371])).

% (21501)Refutation not found, incomplete strategy% (21501)------------------------------
% (21501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21501)Termination reason: Refutation not found, incomplete strategy

% (21501)Memory used [KB]: 10618
% (21501)Time elapsed: 0.118 s
% (21501)------------------------------
% (21501)------------------------------
fof(f371,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl5_20
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f74,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

% (21509)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

% (21493)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f73,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

% (21492)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f255,plain,
    ( sK0 != sK1
    | spl5_13 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_13
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f372,plain,
    ( spl5_20
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f355,f286,f262,f369])).

fof(f262,plain,
    ( spl5_14
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f286,plain,
    ( spl5_15
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f355,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f264,f288])).

fof(f288,plain,
    ( sK1 = sK3
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f286])).

fof(f264,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f262])).

fof(f353,plain,
    ( sK1 != sK3
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f352,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f78,f35,f307])).

fof(f307,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_xboole_0,k3_enumset1(X3,X3,X3,X3,X3))
        | sK0 = X3 )
    | ~ spl5_5 ),
    inference(superposition,[],[f50,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_5
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f27,f47,f48])).

% (21497)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,
    ( sK0 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f289,plain,
    ( spl5_15
    | spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f284,f245,f81,f286])).

fof(f81,plain,
    ( spl5_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f245,plain,
    ( spl5_12
  <=> r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f284,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl5_12 ),
    inference(resolution,[],[f247,f74])).

fof(f247,plain,
    ( r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f245])).

fof(f280,plain,
    ( spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f271,f262,f245])).

fof(f271,plain,
    ( r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_14 ),
    inference(superposition,[],[f69,f264])).

fof(f69,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f265,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f257,f218,f102,f262])).

fof(f102,plain,
    ( spl5_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f218,plain,
    ( spl5_11
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f257,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f104,f220])).

fof(f220,plain,
    ( sK1 = sK2
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f104,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f256,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f251,f218,f76,f253])).

fof(f251,plain,
    ( sK0 != sK1
    | spl5_1
    | ~ spl5_11 ),
    inference(superposition,[],[f78,f220])).

fof(f248,plain,
    ( spl5_12
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f229,f114,f245])).

fof(f114,plain,
    ( spl5_7
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f229,plain,
    ( r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f73,f116])).

fof(f116,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f221,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f216,f188,f76,f218])).

fof(f188,plain,
    ( spl5_10
  <=> r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f216,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl5_10 ),
    inference(resolution,[],[f190,f74])).

fof(f190,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f188])).

fof(f212,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f197,f110,f188])).

fof(f110,plain,
    ( spl5_6
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f197,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_6 ),
    inference(superposition,[],[f73,f112])).

fof(f112,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f191,plain,
    ( spl5_10
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f176,f102,f188])).

fof(f176,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f73,f104])).

fof(f117,plain,
    ( spl5_4
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f97,f86,f114,f110,f106,f102])).

fof(f86,plain,
    ( spl5_3
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f97,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f88])).

fof(f88,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X2,X2,X2,X2,X2) = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f30,f47,f48,f48,f47])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f89,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f24,f47,f47])).

fof(f24,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f84,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f76])).

fof(f25,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21498)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (21490)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (21490)Refutation not found, incomplete strategy% (21490)------------------------------
% 0.20/0.50  % (21490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21490)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21490)Memory used [KB]: 1663
% 0.20/0.50  % (21490)Time elapsed: 0.087 s
% 0.20/0.50  % (21490)------------------------------
% 0.20/0.50  % (21490)------------------------------
% 0.20/0.50  % (21496)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (21507)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (21513)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (21504)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (21513)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (21495)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21500)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (21489)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (21510)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (21501)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (21494)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f417,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f79,f84,f89,f117,f191,f212,f221,f248,f256,f265,f280,f289,f352,f353,f372,f411,f412,f416])).
% 0.20/0.53  % (21512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  fof(f416,plain,(
% 0.20/0.53    sK1 != sK2 | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f412,plain,(
% 0.20/0.53    sK0 != sK1 | sK1 != sK3 | sK0 = sK3),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f411,plain,(
% 0.20/0.53    spl5_13 | ~spl5_20),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f403])).
% 0.20/0.53  fof(f403,plain,(
% 0.20/0.53    $false | (spl5_13 | ~spl5_20)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f255,f73,f390])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X1) ) | ~spl5_20),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f377])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X1 | sK1 = X1 | sK1 = X1) ) | ~spl5_20),
% 0.20/0.53    inference(superposition,[],[f74,f371])).
% 0.20/0.53  % (21501)Refutation not found, incomplete strategy% (21501)------------------------------
% 0.20/0.53  % (21501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21501)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21501)Memory used [KB]: 10618
% 0.20/0.53  % (21501)Time elapsed: 0.118 s
% 0.20/0.53  % (21501)------------------------------
% 0.20/0.53  % (21501)------------------------------
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl5_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f369])).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    spl5_20 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.20/0.53    inference(equality_resolution,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.53    inference(definition_unfolding,[],[f36,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f44,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  % (21509)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (21493)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.53    inference(rectify,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.53    inference(nnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 0.20/0.53    inference(equality_resolution,[],[f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 0.20/0.53    inference(equality_resolution,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.53    inference(definition_unfolding,[],[f37,f46])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  % (21492)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    sK0 != sK1 | spl5_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f253])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    spl5_13 <=> sK0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    spl5_20 | ~spl5_14 | ~spl5_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f355,f286,f262,f369])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    spl5_14 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    spl5_15 <=> sK1 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl5_14 | ~spl5_15)),
% 0.20/0.53    inference(forward_demodulation,[],[f264,f288])).
% 0.20/0.53  fof(f288,plain,(
% 0.20/0.53    sK1 = sK3 | ~spl5_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f286])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3) | ~spl5_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f262])).
% 0.20/0.53  fof(f353,plain,(
% 0.20/0.53    sK1 != sK3 | k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f352,plain,(
% 0.20/0.53    spl5_1 | ~spl5_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.53  fof(f348,plain,(
% 0.20/0.53    $false | (spl5_1 | ~spl5_5)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f78,f35,f307])).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    ( ! [X3] : (~r1_tarski(k1_xboole_0,k3_enumset1(X3,X3,X3,X3,X3)) | sK0 = X3) ) | ~spl5_5),
% 0.20/0.53    inference(superposition,[],[f50,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~spl5_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl5_5 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) | X0 = X2) )),
% 0.20/0.53    inference(definition_unfolding,[],[f27,f47,f48])).
% 0.20/0.53  % (21497)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f29,f47])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f28,f46])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    sK0 != sK2 | spl5_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl5_1 <=> sK0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    spl5_15 | spl5_2 | ~spl5_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f284,f245,f81,f286])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl5_2 <=> sK0 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    spl5_12 <=> r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    sK0 = sK3 | sK1 = sK3 | ~spl5_12),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f281])).
% 0.20/0.53  fof(f281,plain,(
% 0.20/0.53    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl5_12),
% 0.20/0.53    inference(resolution,[],[f247,f74])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f245])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    spl5_12 | ~spl5_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f271,f262,f245])).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_14),
% 0.20/0.53    inference(superposition,[],[f69,f264])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 0.20/0.53    inference(equality_resolution,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.53    inference(definition_unfolding,[],[f39,f46])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    spl5_14 | ~spl5_4 | ~spl5_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f257,f218,f102,f262])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl5_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    spl5_11 <=> sK1 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3) | (~spl5_4 | ~spl5_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f104,f220])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    sK1 = sK2 | ~spl5_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f218])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) | ~spl5_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~spl5_13 | spl5_1 | ~spl5_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f251,f218,f76,f253])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    sK0 != sK1 | (spl5_1 | ~spl5_11)),
% 0.20/0.53    inference(superposition,[],[f78,f220])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    spl5_12 | ~spl5_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f229,f114,f245])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl5_7 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_7),
% 0.20/0.53    inference(superposition,[],[f73,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl5_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    spl5_11 | spl5_1 | ~spl5_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f216,f188,f76,f218])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    spl5_10 <=> r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    sK0 = sK2 | sK1 = sK2 | ~spl5_10),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f213])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl5_10),
% 0.20/0.53    inference(resolution,[],[f190,f74])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f188])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    spl5_10 | ~spl5_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f197,f110,f188])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    spl5_6 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_6),
% 0.20/0.53    inference(superposition,[],[f73,f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    spl5_10 | ~spl5_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f176,f102,f188])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_4),
% 0.20/0.53    inference(superposition,[],[f73,f104])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    spl5_4 | spl5_5 | spl5_6 | spl5_7 | ~spl5_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f97,f86,f114,f110,f106,f102])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl5_3 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) | ~spl5_3),
% 0.20/0.53    inference(resolution,[],[f55,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl5_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f86])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X2) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f30,f47,f48,f48,f47])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.53    inference(nnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl5_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f49,f86])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 0.20/0.53    inference(definition_unfolding,[],[f24,f47,f47])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ~spl5_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f81])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    sK0 != sK3),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ~spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f76])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    sK0 != sK2),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (21513)------------------------------
% 0.20/0.53  % (21513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21513)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (21513)Memory used [KB]: 11001
% 0.20/0.53  % (21513)Time elapsed: 0.065 s
% 0.20/0.53  % (21513)------------------------------
% 0.20/0.53  % (21513)------------------------------
% 0.20/0.54  % (21485)Success in time 0.177 s
%------------------------------------------------------------------------------
