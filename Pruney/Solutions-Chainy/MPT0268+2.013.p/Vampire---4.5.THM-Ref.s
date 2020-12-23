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
% DateTime   : Thu Dec  3 12:40:37 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 210 expanded)
%              Number of equality atoms :   57 (  95 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f104,f144,f173,f327,f328])).

fof(f328,plain,
    ( sK1 != sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f327,plain,
    ( spl7_7
    | ~ spl7_6
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f322,f141,f91,f141,f324])).

fof(f324,plain,
    ( spl7_7
  <=> sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f91,plain,
    ( spl7_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f141,plain,
    ( spl7_6
  <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f322,plain,
    ( ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl7_1
    | ~ spl7_6 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl7_1
    | ~ spl7_6 ),
    inference(resolution,[],[f259,f143])).

fof(f143,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f259,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0)
        | ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1
        | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1) )
    | spl7_1 ),
    inference(resolution,[],[f178,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f178,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | sK0 != X0
        | ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0)
        | ~ r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0) )
    | spl7_1 ),
    inference(superposition,[],[f93,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f93,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f173,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f97,f88,f154])).

fof(f154,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl7_1 ),
    inference(superposition,[],[f78,f92])).

fof(f92,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f97,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f144,plain,
    ( spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f139,f91,f141])).

fof(f139,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | spl7_1 ),
    inference(factoring,[],[f102])).

fof(f102,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0)
        | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1 )
    | spl7_1 ),
    inference(superposition,[],[f93,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f32,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f54,f95,f91])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f17,f23,f52])).

fof(f17,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f98,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f53,f95,f91])).

fof(f53,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f18,f23,f52])).

fof(f18,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3402)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (3418)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (3416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (3402)Refutation not found, incomplete strategy% (3402)------------------------------
% 0.20/0.50  % (3402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (3399)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (3408)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (3410)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (3402)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3402)Memory used [KB]: 10746
% 0.20/0.51  % (3402)Time elapsed: 0.095 s
% 0.20/0.51  % (3402)------------------------------
% 0.20/0.51  % (3402)------------------------------
% 0.20/0.51  % (3396)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (3414)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (3397)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (3406)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (3400)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.53  % (3414)Refutation not found, incomplete strategy% (3414)------------------------------
% 1.39/0.53  % (3414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (3414)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (3414)Memory used [KB]: 10746
% 1.39/0.53  % (3414)Time elapsed: 0.122 s
% 1.39/0.53  % (3414)------------------------------
% 1.39/0.53  % (3414)------------------------------
% 1.39/0.53  % (3416)Refutation found. Thanks to Tanya!
% 1.39/0.53  % SZS status Theorem for theBenchmark
% 1.39/0.53  % (3413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.53  % (3420)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.53  % (3396)Refutation not found, incomplete strategy% (3396)------------------------------
% 1.39/0.53  % (3396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (3394)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.53  % (3401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.53  % (3412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.53  % (3396)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (3396)Memory used [KB]: 10746
% 1.39/0.53  % (3396)Time elapsed: 0.127 s
% 1.39/0.53  % (3396)------------------------------
% 1.39/0.53  % (3396)------------------------------
% 1.39/0.53  % (3423)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f329,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(avatar_sat_refutation,[],[f98,f104,f144,f173,f327,f328])).
% 1.39/0.54  fof(f328,plain,(
% 1.39/0.54    sK1 != sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | r2_hidden(sK1,sK0)),
% 1.39/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.54  fof(f327,plain,(
% 1.39/0.54    spl7_7 | ~spl7_6 | spl7_1 | ~spl7_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f322,f141,f91,f141,f324])).
% 1.39/0.54  fof(f324,plain,(
% 1.39/0.54    spl7_7 <=> sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.39/0.54  fof(f91,plain,(
% 1.39/0.54    spl7_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.39/0.54  fof(f141,plain,(
% 1.39/0.54    spl7_6 <=> r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.39/0.54  fof(f322,plain,(
% 1.39/0.54    ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl7_1 | ~spl7_6)),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f295])).
% 1.39/0.54  fof(f295,plain,(
% 1.39/0.54    ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl7_1 | ~spl7_6)),
% 1.39/0.54    inference(resolution,[],[f259,f143])).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | ~spl7_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f141])).
% 1.39/0.54  fof(f259,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0) | ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1 | sK1 = sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1)) ) | spl7_1),
% 1.39/0.54    inference(resolution,[],[f178,f74])).
% 1.39/0.54  fof(f74,plain,(
% 1.39/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 1.39/0.54    inference(equality_resolution,[],[f58])).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.39/0.54    inference(definition_unfolding,[],[f27,f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f20,f51])).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f22,f30])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.39/0.54  fof(f178,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 != X0 | ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0) | ~r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0)) ) | spl7_1),
% 1.39/0.54    inference(superposition,[],[f93,f65])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f31,f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.39/0.54  fof(f93,plain,(
% 1.39/0.54    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | spl7_1),
% 1.39/0.54    inference(avatar_component_clause,[],[f91])).
% 1.39/0.54  fof(f173,plain,(
% 1.39/0.54    ~spl7_1 | ~spl7_2),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f159])).
% 1.39/0.54  fof(f159,plain,(
% 1.39/0.54    $false | (~spl7_1 | ~spl7_2)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f97,f88,f154])).
% 1.39/0.54  fof(f154,plain,(
% 1.39/0.54    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X4,sK0)) ) | ~spl7_1),
% 1.39/0.54    inference(superposition,[],[f78,f92])).
% 1.39/0.54  fof(f92,plain,(
% 1.39/0.54    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl7_1),
% 1.39/0.54    inference(avatar_component_clause,[],[f91])).
% 1.39/0.54  fof(f78,plain,(
% 1.39/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f61])).
% 1.39/0.54  fof(f61,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.39/0.54    inference(definition_unfolding,[],[f35,f23])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f88,plain,(
% 1.39/0.54    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f87])).
% 1.39/0.54  fof(f87,plain,(
% 1.39/0.54    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 1.39/0.54    inference(equality_resolution,[],[f68])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.39/0.54    inference(definition_unfolding,[],[f48,f30])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.39/0.54  fof(f97,plain,(
% 1.39/0.54    r2_hidden(sK1,sK0) | ~spl7_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f95])).
% 1.39/0.54  fof(f95,plain,(
% 1.39/0.54    spl7_2 <=> r2_hidden(sK1,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    spl7_6 | spl7_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f139,f91,f141])).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | spl7_1),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f136])).
% 1.39/0.54  fof(f136,plain,(
% 1.39/0.54    r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | spl7_1),
% 1.39/0.54    inference(factoring,[],[f102])).
% 1.39/0.54  fof(f102,plain,(
% 1.39/0.54    ( ! [X1] : (r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0) | r2_hidden(sK4(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1) ) | spl7_1),
% 1.39/0.54    inference(superposition,[],[f93,f64])).
% 1.39/0.54  fof(f64,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f32,f23])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    spl7_1 | ~spl7_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f54,f95,f91])).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.39/0.54    inference(definition_unfolding,[],[f17,f23,f52])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.39/0.54    inference(negated_conjecture,[],[f12])).
% 1.39/0.54  fof(f12,conjecture,(
% 1.39/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    ~spl7_1 | spl7_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f53,f95,f91])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.39/0.54    inference(definition_unfolding,[],[f18,f23,f52])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (3416)------------------------------
% 1.39/0.54  % (3416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (3416)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (3416)Memory used [KB]: 10874
% 1.39/0.54  % (3416)Time elapsed: 0.073 s
% 1.39/0.54  % (3416)------------------------------
% 1.39/0.54  % (3416)------------------------------
% 1.39/0.54  % (3393)Success in time 0.181 s
%------------------------------------------------------------------------------
