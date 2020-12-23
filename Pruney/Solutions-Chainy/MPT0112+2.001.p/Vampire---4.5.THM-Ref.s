%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 143 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :  218 ( 327 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f69,f80,f97,f110,f133,f261,f296,f359,f369,f373])).

fof(f373,plain,
    ( ~ spl2_38
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl2_38
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f371,f295])).

fof(f295,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl2_38
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f371,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl2_45
    | ~ spl2_47 ),
    inference(resolution,[],[f368,f358])).

fof(f358,plain,
    ( ! [X0] :
        ( r2_xboole_0(sK0,X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl2_45
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_xboole_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f368,plain,
    ( ! [X2] :
        ( ~ r2_xboole_0(X2,sK0)
        | ~ r1_tarski(sK1,X2) )
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl2_47
  <=> ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r2_xboole_0(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f369,plain,
    ( spl2_47
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f361,f357,f59,f367])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X1,X0)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f361,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r2_xboole_0(X2,sK0) )
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(resolution,[],[f358,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f359,plain,
    ( spl2_45
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f355,f67,f34,f357])).

fof(f34,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r2_xboole_0(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_xboole_0(sK0,X0) )
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r2_xboole_0(X0,X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f296,plain,
    ( spl2_38
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f284,f258,f130,f293])).

fof(f130,plain,
    ( spl2_19
  <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f258,plain,
    ( spl2_32
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f284,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(superposition,[],[f131,f260])).

fof(f260,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f258])).

fof(f131,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f261,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f256,f92,f55,f51,f29,f258])).

fof(f29,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f256,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f255,f93])).

fof(f93,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f255,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f242,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f242,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f56,f31])).

fof(f31,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f56,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f133,plain,
    ( spl2_19
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f123,f108,f51,f130])).

fof(f108,plain,
    ( spl2_15
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f123,plain,
    ( ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3))
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(superposition,[],[f109,f52])).

fof(f109,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f102,f78,f63,f108])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f78,plain,
    ( spl2_12
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f102,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f97,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f90,f51,f43,f92])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f90,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f44,f52])).

fof(f44,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f80,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f47,f39,f78])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f48,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f69,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

% (21923)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:14:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (21922)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (21922)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f374,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f69,f80,f97,f110,f133,f261,f296,f359,f369,f373])).
% 0.22/0.42  fof(f373,plain,(
% 0.22/0.42    ~spl2_38 | ~spl2_45 | ~spl2_47),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f372])).
% 0.22/0.42  fof(f372,plain,(
% 0.22/0.42    $false | (~spl2_38 | ~spl2_45 | ~spl2_47)),
% 0.22/0.42    inference(subsumption_resolution,[],[f371,f295])).
% 0.22/0.42  fof(f295,plain,(
% 0.22/0.42    r1_tarski(sK1,sK0) | ~spl2_38),
% 0.22/0.42    inference(avatar_component_clause,[],[f293])).
% 0.22/0.42  fof(f293,plain,(
% 0.22/0.42    spl2_38 <=> r1_tarski(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.22/0.42  fof(f371,plain,(
% 0.22/0.42    ~r1_tarski(sK1,sK0) | (~spl2_45 | ~spl2_47)),
% 0.22/0.42    inference(duplicate_literal_removal,[],[f370])).
% 0.22/0.42  fof(f370,plain,(
% 0.22/0.42    ~r1_tarski(sK1,sK0) | ~r1_tarski(sK1,sK0) | (~spl2_45 | ~spl2_47)),
% 0.22/0.42    inference(resolution,[],[f368,f358])).
% 0.22/0.42  fof(f358,plain,(
% 0.22/0.42    ( ! [X0] : (r2_xboole_0(sK0,X0) | ~r1_tarski(sK1,X0)) ) | ~spl2_45),
% 0.22/0.42    inference(avatar_component_clause,[],[f357])).
% 0.22/0.42  fof(f357,plain,(
% 0.22/0.42    spl2_45 <=> ! [X0] : (~r1_tarski(sK1,X0) | r2_xboole_0(sK0,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.42  fof(f368,plain,(
% 0.22/0.42    ( ! [X2] : (~r2_xboole_0(X2,sK0) | ~r1_tarski(sK1,X2)) ) | ~spl2_47),
% 0.22/0.42    inference(avatar_component_clause,[],[f367])).
% 0.22/0.42  fof(f367,plain,(
% 0.22/0.42    spl2_47 <=> ! [X2] : (~r1_tarski(sK1,X2) | ~r2_xboole_0(X2,sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.22/0.42  fof(f369,plain,(
% 0.22/0.42    spl2_47 | ~spl2_8 | ~spl2_45),
% 0.22/0.42    inference(avatar_split_clause,[],[f361,f357,f59,f367])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl2_8 <=> ! [X1,X0] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.42  fof(f361,plain,(
% 0.22/0.42    ( ! [X2] : (~r1_tarski(sK1,X2) | ~r2_xboole_0(X2,sK0)) ) | (~spl2_8 | ~spl2_45)),
% 0.22/0.42    inference(resolution,[],[f358,f60])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) ) | ~spl2_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f59])).
% 0.22/0.42  fof(f359,plain,(
% 0.22/0.42    spl2_45 | ~spl2_2 | ~spl2_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f355,f67,f34,f357])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl2_2 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl2_10 <=> ! [X1,X0,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.42  fof(f355,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_xboole_0(sK0,X0)) ) | (~spl2_2 | ~spl2_10)),
% 0.22/0.42    inference(resolution,[],[f68,f36])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    r2_xboole_0(sK0,sK1) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r2_xboole_0(X0,X1) | ~r1_tarski(X1,X2) | r2_xboole_0(X0,X2)) ) | ~spl2_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f296,plain,(
% 0.22/0.42    spl2_38 | ~spl2_19 | ~spl2_32),
% 0.22/0.42    inference(avatar_split_clause,[],[f284,f258,f130,f293])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    spl2_19 <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.42  fof(f258,plain,(
% 0.22/0.42    spl2_32 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.42  fof(f284,plain,(
% 0.22/0.42    r1_tarski(sK1,sK0) | (~spl2_19 | ~spl2_32)),
% 0.22/0.42    inference(superposition,[],[f131,f260])).
% 0.22/0.42  fof(f260,plain,(
% 0.22/0.42    sK0 = k2_xboole_0(sK0,sK1) | ~spl2_32),
% 0.22/0.42    inference(avatar_component_clause,[],[f258])).
% 0.22/0.42  fof(f131,plain,(
% 0.22/0.42    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | ~spl2_19),
% 0.22/0.42    inference(avatar_component_clause,[],[f130])).
% 0.22/0.42  fof(f261,plain,(
% 0.22/0.42    spl2_32 | ~spl2_1 | ~spl2_6 | ~spl2_7 | ~spl2_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f256,f92,f55,f51,f29,f258])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    spl2_14 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.42  fof(f256,plain,(
% 0.22/0.42    sK0 = k2_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 0.22/0.42    inference(forward_demodulation,[],[f255,f93])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f92])).
% 0.22/0.42  fof(f255,plain,(
% 0.22/0.42    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_6 | ~spl2_7)),
% 0.22/0.42    inference(forward_demodulation,[],[f242,f52])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f51])).
% 0.22/0.42  fof(f242,plain,(
% 0.22/0.42    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.42    inference(superposition,[],[f56,f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f133,plain,(
% 0.22/0.42    spl2_19 | ~spl2_6 | ~spl2_15),
% 0.22/0.42    inference(avatar_split_clause,[],[f123,f108,f51,f130])).
% 0.22/0.42  fof(f108,plain,(
% 0.22/0.42    spl2_15 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.42  fof(f123,plain,(
% 0.22/0.42    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X4,X3))) ) | (~spl2_6 | ~spl2_15)),
% 0.22/0.42    inference(superposition,[],[f109,f52])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f108])).
% 0.22/0.42  fof(f110,plain,(
% 0.22/0.42    spl2_15 | ~spl2_9 | ~spl2_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f102,f78,f63,f108])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl2_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    spl2_12 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_9 | ~spl2_12)),
% 0.22/0.42    inference(resolution,[],[f64,f79])).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f78])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f63])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    spl2_14 | ~spl2_4 | ~spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f90,f51,f43,f92])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl2_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_4 | ~spl2_6)),
% 0.22/0.42    inference(superposition,[],[f44,f52])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f43])).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    spl2_12 | ~spl2_3 | ~spl2_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f71,f47,f39,f78])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl2_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl2_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_3 | ~spl2_5)),
% 0.22/0.42    inference(superposition,[],[f48,f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f39])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f47])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl2_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl2_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl2_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl2_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f55])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  % (21923)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f43])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f39])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f34])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    r2_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f29])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (21922)------------------------------
% 0.22/0.43  % (21922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (21922)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (21922)Memory used [KB]: 10746
% 0.22/0.43  % (21922)Time elapsed: 0.011 s
% 0.22/0.43  % (21922)------------------------------
% 0.22/0.43  % (21922)------------------------------
% 0.22/0.43  % (21915)Success in time 0.069 s
%------------------------------------------------------------------------------
