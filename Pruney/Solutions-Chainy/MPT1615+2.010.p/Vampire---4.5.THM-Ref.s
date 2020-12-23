%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:43 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 108 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 323 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f56,f60,f65,f70,f75,f81,f85])).

fof(f85,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f37])).

% (27502)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f37,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK0)
    | spl1_1
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f29,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_12
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f77,f73,f54,f50,f79])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( spl1_7
  <=> ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f73,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f77,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f76,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f76,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f75,plain,
    ( spl1_11
    | ~ spl1_7
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f71,f68,f54,f73])).

fof(f68,plain,
    ( spl1_10
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_7
    | ~ spl1_10 ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl1_10
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f66,f63,f58,f68])).

fof(f58,plain,
    ( spl1_8
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f63,plain,
    ( spl1_9
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(resolution,[],[f59,f64])).

fof(f64,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f61,f46,f42,f63])).

fof(f42,plain,
    ( spl1_4
  <=> ! [X0] : k2_subset_1(X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f46,plain,
    ( spl1_5
  <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f61,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(backward_demodulation,[],[f47,f43])).

fof(f43,plain,
    ( ! [X0] : k2_subset_1(X0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f47,plain,
    ( ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f60,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f56,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
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

fof(f52,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f48,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f44,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f7])).

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

fof(f35,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (27506)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.13/0.42  % (27506)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f86,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f56,f60,f65,f70,f75,f81,f85])).
% 0.13/0.42  fof(f85,plain,(
% 0.13/0.42    spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_12),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f84])).
% 0.13/0.42  fof(f84,plain,(
% 0.13/0.42    $false | (spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_12)),
% 0.13/0.42    inference(subsumption_resolution,[],[f83,f39])).
% 0.13/0.42  fof(f39,plain,(
% 0.13/0.42    v2_pre_topc(sK0) | ~spl1_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f37])).
% 0.13/0.42  % (27502)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.42  fof(f37,plain,(
% 0.13/0.42    spl1_3 <=> v2_pre_topc(sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.13/0.42  fof(f83,plain,(
% 0.13/0.42    ~v2_pre_topc(sK0) | (spl1_1 | ~spl1_2 | ~spl1_12)),
% 0.13/0.42    inference(subsumption_resolution,[],[f82,f29])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl1_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f27])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    spl1_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.13/0.42  fof(f82,plain,(
% 0.13/0.42    k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl1_2 | ~spl1_12)),
% 0.13/0.42    inference(resolution,[],[f80,f34])).
% 0.13/0.42  fof(f34,plain,(
% 0.13/0.42    l1_pre_topc(sK0) | ~spl1_2),
% 0.13/0.42    inference(avatar_component_clause,[],[f32])).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    spl1_2 <=> l1_pre_topc(sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.13/0.42  fof(f80,plain,(
% 0.13/0.42    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~v2_pre_topc(X0)) ) | ~spl1_12),
% 0.13/0.42    inference(avatar_component_clause,[],[f79])).
% 0.13/0.42  fof(f79,plain,(
% 0.13/0.42    spl1_12 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.13/0.42  fof(f81,plain,(
% 0.13/0.42    spl1_12 | ~spl1_6 | ~spl1_7 | ~spl1_11),
% 0.13/0.42    inference(avatar_split_clause,[],[f77,f73,f54,f50,f79])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    spl1_6 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.13/0.42  fof(f54,plain,(
% 0.13/0.42    spl1_7 <=> ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    spl1_11 <=> ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.13/0.42  fof(f77,plain,(
% 0.13/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl1_6 | ~spl1_7 | ~spl1_11)),
% 0.13/0.42    inference(subsumption_resolution,[],[f76,f74])).
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl1_11),
% 0.13/0.42    inference(avatar_component_clause,[],[f73])).
% 0.13/0.42  fof(f76,plain,(
% 0.13/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl1_6 | ~spl1_7)),
% 0.13/0.42    inference(resolution,[],[f51,f55])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl1_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f54])).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) ) | ~spl1_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f50])).
% 0.13/0.42  fof(f75,plain,(
% 0.13/0.42    spl1_11 | ~spl1_7 | ~spl1_10),
% 0.13/0.42    inference(avatar_split_clause,[],[f71,f68,f54,f73])).
% 0.13/0.42  fof(f68,plain,(
% 0.13/0.42    spl1_10 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl1_7 | ~spl1_10)),
% 0.13/0.42    inference(resolution,[],[f69,f55])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl1_10),
% 0.13/0.42    inference(avatar_component_clause,[],[f68])).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    spl1_10 | ~spl1_8 | ~spl1_9),
% 0.13/0.42    inference(avatar_split_clause,[],[f66,f63,f58,f68])).
% 0.13/0.42  fof(f58,plain,(
% 0.13/0.42    spl1_8 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.13/0.42  fof(f63,plain,(
% 0.13/0.42    spl1_9 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.13/0.42  fof(f66,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | (~spl1_8 | ~spl1_9)),
% 0.13/0.42    inference(resolution,[],[f59,f64])).
% 0.13/0.42  fof(f64,plain,(
% 0.13/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl1_9),
% 0.13/0.42    inference(avatar_component_clause,[],[f63])).
% 0.13/0.42  fof(f59,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) ) | ~spl1_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f58])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    spl1_9 | ~spl1_4 | ~spl1_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f61,f46,f42,f63])).
% 0.13/0.42  fof(f42,plain,(
% 0.13/0.42    spl1_4 <=> ! [X0] : k2_subset_1(X0) = X0),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    spl1_5 <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl1_4 | ~spl1_5)),
% 0.13/0.42    inference(backward_demodulation,[],[f47,f43])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) ) | ~spl1_4),
% 0.13/0.42    inference(avatar_component_clause,[],[f42])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) ) | ~spl1_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f46])).
% 0.13/0.42  fof(f60,plain,(
% 0.13/0.42    spl1_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f25,f58])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.13/0.42  fof(f56,plain,(
% 0.13/0.42    spl1_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f24,f54])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.13/0.42    inference(flattening,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).
% 0.13/0.42  fof(f52,plain,(
% 0.13/0.42    spl1_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f23,f50])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.13/0.42    inference(flattening,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    spl1_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f22,f46])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.13/0.42  fof(f44,plain,(
% 0.13/0.42    spl1_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f21,f42])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    spl1_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f18,f37])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    v2_pre_topc(sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.13/0.42    inference(flattening,[],[f9])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.13/0.42    inference(pure_predicate_removal,[],[f7])).
% 0.13/0.42  fof(f7,negated_conjecture,(
% 0.13/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.13/0.42    inference(negated_conjecture,[],[f6])).
% 0.13/0.42  fof(f6,conjecture,(
% 0.13/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    spl1_2),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f32])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    l1_pre_topc(sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    ~spl1_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f20,f27])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (27506)------------------------------
% 0.13/0.42  % (27506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (27506)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (27506)Memory used [KB]: 6140
% 0.13/0.42  % (27506)Time elapsed: 0.005 s
% 0.13/0.42  % (27506)------------------------------
% 0.13/0.42  % (27506)------------------------------
% 0.21/0.42  % (27494)Success in time 0.063 s
%------------------------------------------------------------------------------
