%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 113 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  226 ( 370 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f50,f54,f58,f62,f66,f71,f76,f81,f89,f109])).

fof(f109,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f107,f35])).

fof(f35,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f106,f40])).

fof(f40,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f92,f49])).

fof(f49,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f92,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(superposition,[],[f70,f88])).

fof(f88,plain,
    ( k1_xboole_0 = u1_pre_topc(sK0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl1_13
  <=> k1_xboole_0 = u1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_pre_topc(X0),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_tarski(u1_pre_topc(X0),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f89,plain,
    ( spl1_13
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f84,f79,f38,f33,f28,f86])).

fof(f28,plain,
    ( spl1_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f79,plain,
    ( spl1_12
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | k1_xboole_0 = u1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f84,plain,
    ( k1_xboole_0 = u1_pre_topc(sK0)
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 = u1_pre_topc(sK0)
    | spl1_1
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f30,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f82,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = u1_pre_topc(sK0)
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(resolution,[],[f80,f35])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | k1_xboole_0 = u1_pre_topc(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f77,f74,f56,f79])).

fof(f56,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f74,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f77,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | k1_xboole_0 = u1_pre_topc(X0) )
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f75,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_pre_topc(X0))
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl1_11
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f72,f60,f52,f74])).

fof(f52,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f60,plain,
    ( spl1_8
  <=> ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f72,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f71,plain,
    ( spl1_10
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f67,f64,f60,f69])).

fof(f64,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_tarski(u1_pre_topc(X0),k1_xboole_0) )
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(resolution,[],[f61,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f62,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f58,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f50,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f41,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f36,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f21,f28])).

fof(f21,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (28555)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (28553)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (28554)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (28553)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f31,f36,f41,f50,f54,f58,f62,f66,f71,f76,f81,f89,f109])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ~spl1_2 | ~spl1_3 | ~spl1_5 | ~spl1_10 | ~spl1_13),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    $false | (~spl1_2 | ~spl1_3 | ~spl1_5 | ~spl1_10 | ~spl1_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f107,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    l1_pre_topc(sK0) | ~spl1_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl1_2 <=> l1_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    ~l1_pre_topc(sK0) | (~spl1_3 | ~spl1_5 | ~spl1_10 | ~spl1_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f106,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    v2_pre_topc(sK0) | ~spl1_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl1_3 <=> v2_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl1_5 | ~spl1_10 | ~spl1_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f92,f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl1_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl1_10 | ~spl1_13)),
% 0.20/0.42    inference(superposition,[],[f70,f88])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    k1_xboole_0 = u1_pre_topc(sK0) | ~spl1_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f86])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    spl1_13 <=> k1_xboole_0 = u1_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),k1_xboole_0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl1_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f69])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl1_10 <=> ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(u1_pre_topc(X0),k1_xboole_0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl1_13 | spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f84,f79,f38,f33,f28,f86])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    spl1_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl1_12 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k1_xboole_0 = u1_pre_topc(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    k1_xboole_0 = u1_pre_topc(sK0) | (spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_12)),
% 0.20/0.42    inference(subsumption_resolution,[],[f83,f40])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ~v2_pre_topc(sK0) | k1_xboole_0 = u1_pre_topc(sK0) | (spl1_1 | ~spl1_2 | ~spl1_12)),
% 0.20/0.42    inference(subsumption_resolution,[],[f82,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl1_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f28])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | k1_xboole_0 = u1_pre_topc(sK0) | (~spl1_2 | ~spl1_12)),
% 0.20/0.42    inference(resolution,[],[f80,f35])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~v2_pre_topc(X0) | k1_xboole_0 = u1_pre_topc(X0)) ) | ~spl1_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f79])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    spl1_12 | ~spl1_7 | ~spl1_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f77,f74,f56,f79])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl1_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl1_11 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k1_xboole_0 = u1_pre_topc(X0)) ) | (~spl1_7 | ~spl1_11)),
% 0.20/0.42    inference(resolution,[],[f75,f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f56])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(u1_pre_topc(X0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl1_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f74])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl1_11 | ~spl1_6 | ~spl1_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f72,f60,f52,f74])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl1_6 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl1_8 <=> ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl1_6 | ~spl1_8)),
% 0.20/0.42    inference(resolution,[],[f53,f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl1_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f60])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) ) | ~spl1_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f52])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl1_10 | ~spl1_8 | ~spl1_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f67,f64,f60,f69])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl1_9 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(u1_pre_topc(X0),k1_xboole_0)) ) | (~spl1_8 | ~spl1_9)),
% 0.20/0.42    inference(resolution,[],[f61,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl1_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f64])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl1_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl1_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f60])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl1_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f56])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl1_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl1_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f48])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl1_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f38])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl1_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f33])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ~spl1_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f28])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (28553)------------------------------
% 0.20/0.42  % (28553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (28553)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (28553)Memory used [KB]: 10618
% 0.20/0.42  % (28553)Time elapsed: 0.006 s
% 0.20/0.42  % (28553)------------------------------
% 0.20/0.42  % (28553)------------------------------
% 0.20/0.43  % (28557)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (28547)Success in time 0.077 s
%------------------------------------------------------------------------------
