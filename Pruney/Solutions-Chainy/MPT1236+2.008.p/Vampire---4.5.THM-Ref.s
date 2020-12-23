%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 105 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f35,f42,f52])).

fof(f52,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | spl1_4 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | spl1_4 ),
    inference(subsumption_resolution,[],[f50,f41])).

fof(f41,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f50,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f49,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f49,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0))
    | ~ spl1_2 ),
    inference(resolution,[],[f29,f26])).

fof(f26,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f42,plain,
    ( ~ spl1_4
    | spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f36,f32,f19,f39])).

fof(f19,plain,
    ( spl1_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f36,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f21,f34])).

fof(f21,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f35,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f30,f24,f32])).

fof(f30,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f15,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f27,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (17694)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  % (17694)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f22,f27,f35,f42,f52])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    ~spl1_2 | ~spl1_3 | spl1_4),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    $false | (~spl1_2 | ~spl1_3 | spl1_4)),
% 0.21/0.41    inference(subsumption_resolution,[],[f50,f41])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | spl1_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl1_4 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.21/0.42    inference(forward_demodulation,[],[f49,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl1_3 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) | ~spl1_2),
% 0.21/0.42    inference(resolution,[],[f29,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0))) )),
% 0.21/0.42    inference(resolution,[],[f17,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ~spl1_4 | spl1_1 | ~spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f32,f19,f39])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    spl1_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl1_1 | ~spl1_3)),
% 0.21/0.42    inference(superposition,[],[f21,f34])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f19])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl1_3 | ~spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f24,f32])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_2),
% 0.21/0.42    inference(resolution,[],[f28,f26])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.42    inference(resolution,[],[f15,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f24])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f19])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (17694)------------------------------
% 0.21/0.42  % (17694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (17694)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (17694)Memory used [KB]: 10490
% 0.21/0.42  % (17694)Time elapsed: 0.005 s
% 0.21/0.42  % (17694)------------------------------
% 0.21/0.42  % (17694)------------------------------
% 0.21/0.42  % (17692)Success in time 0.063 s
%------------------------------------------------------------------------------
