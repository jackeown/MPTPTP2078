%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  75 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f48,f54,f56])).

fof(f56,plain,
    ( ~ spl1_2
    | ~ spl1_5
    | spl1_6 ),
    inference(avatar_split_clause,[],[f55,f51,f45,f29])).

fof(f29,plain,
    ( spl1_2
  <=> v1_finset_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f45,plain,
    ( spl1_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f51,plain,
    ( spl1_6
  <=> v8_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f55,plain,
    ( ~ v1_finset_1(u1_struct_0(sK0))
    | ~ spl1_5
    | spl1_6 ),
    inference(unit_resulting_resolution,[],[f47,f53,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).

fof(f53,plain,
    ( ~ v8_struct_0(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f47,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f54,plain,
    ( ~ spl1_6
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f49,f39,f34,f24,f51])).

fof(f24,plain,
    ( spl1_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f34,plain,
    ( spl1_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f39,plain,
    ( spl1_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,
    ( ~ v8_struct_0(sK0)
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f36,f26,f41,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v8_struct_0(X0) )
       => ( v1_compts_1(X0)
          & v2_pre_topc(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).

fof(f41,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f26,plain,
    ( ~ v1_compts_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f36,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f48,plain,
    ( spl1_5
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f43,f34,f45])).

fof(f43,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f36,f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v1_compts_1(sK0)
    & v1_finset_1(u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ~ v1_compts_1(X0)
        & v1_finset_1(u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v1_compts_1(sK0)
      & v1_finset_1(u1_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( v1_finset_1(u1_struct_0(X0))
         => v1_compts_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_finset_1(u1_struct_0(X0))
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).

fof(f37,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    v1_finset_1(u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f24])).

fof(f18,plain,(
    ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

% (12164)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (12176)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (12176)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f48,f54,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~spl1_2 | ~spl1_5 | spl1_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f51,f45,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    spl1_2 <=> v1_finset_1(u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl1_5 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl1_6 <=> v8_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v1_finset_1(u1_struct_0(sK0)) | (~spl1_5 | spl1_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f53,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_finset_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v8_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (~v1_finset_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v8_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (~v1_finset_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v8_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v8_struct_0(X0)) => ~v1_finset_1(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ~v8_struct_0(sK0) | spl1_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl1_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~spl1_6 | spl1_1 | ~spl1_3 | ~spl1_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f39,f34,f24,f51])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    spl1_1 <=> v1_compts_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    spl1_3 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl1_4 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v8_struct_0(sK0) | (spl1_1 | ~spl1_3 | ~spl1_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f36,f26,f41,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : ((v1_compts_1(X0) & v2_pre_topc(X0)) | ~v2_pre_topc(X0) | ~v8_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (((v1_compts_1(X0) & v2_pre_topc(X0)) | (~v2_pre_topc(X0) | ~v8_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v8_struct_0(X0)) => (v1_compts_1(X0) & v2_pre_topc(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl1_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~v1_compts_1(sK0) | spl1_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f24])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl1_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f34])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl1_5 | ~spl1_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f34,f45])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl1_3),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f36,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl1_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ~v1_compts_1(sK0) & v1_finset_1(u1_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (~v1_compts_1(X0) & v1_finset_1(u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (~v1_compts_1(sK0) & v1_finset_1(u1_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (~v1_compts_1(X0) & v1_finset_1(u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : ((~v1_compts_1(X0) & v1_finset_1(u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_finset_1(u1_struct_0(X0)) => v1_compts_1(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_finset_1(u1_struct_0(X0)) => v1_compts_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl1_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    spl1_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    v1_finset_1(u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ~spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f24])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ~v1_compts_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % (12164)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12176)------------------------------
% 0.21/0.50  % (12176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12176)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (12176)Memory used [KB]: 5373
% 0.21/0.50  % (12176)Time elapsed: 0.072 s
% 0.21/0.50  % (12176)------------------------------
% 0.21/0.50  % (12176)------------------------------
% 0.21/0.51  % (12162)Success in time 0.144 s
%------------------------------------------------------------------------------
