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
% DateTime   : Thu Dec  3 13:10:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 269 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f36,f37,f43,f49,f53,f64,f67,f82])).

fof(f82,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_7 ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | spl2_7 ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f30,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f70,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_7 ),
    inference(superposition,[],[f59,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f59,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_7
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( ~ spl2_2
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_2
    | spl2_8 ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(resolution,[],[f63,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f63,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_8
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f64,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | ~ spl2_1
    | spl2_4 ),
    inference(avatar_split_clause,[],[f55,f33,f19,f61,f57])).

fof(f19,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f33,plain,
    ( spl2_4
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f55,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl2_1
    | spl2_4 ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f21,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f54,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(resolution,[],[f35,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f35,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f53,plain,
    ( ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f51,f26])).

fof(f51,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f50,f34])).

fof(f34,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f50,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f48,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_6
  <=> ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f49,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f45,f41,f47])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f45,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f44,f16])).

fof(f44,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_5 ),
    inference(superposition,[],[f42,f17])).

fof(f42,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f43,plain,
    ( spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f39,f19,f41])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f15,f21])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f10,f33,f29])).

fof(f10,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f36,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f11,f33,f29])).

fof(f11,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (2810)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (2816)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (2810)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f83,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f22,f27,f36,f37,f43,f49,f53,f64,f67,f82])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    ~spl2_2 | ~spl2_3 | spl2_7),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    $false | (~spl2_2 | ~spl2_3 | spl2_7)),
% 0.20/0.41    inference(subsumption_resolution,[],[f80,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | spl2_7)),
% 0.20/0.41    inference(subsumption_resolution,[],[f70,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_7),
% 0.20/0.41    inference(superposition,[],[f59,f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | spl2_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    spl2_7 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    ~spl2_2 | spl2_8),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    $false | (~spl2_2 | spl2_8)),
% 0.20/0.41    inference(subsumption_resolution,[],[f65,f26])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.20/0.41    inference(resolution,[],[f63,f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f61])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    spl2_8 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    ~spl2_7 | ~spl2_8 | ~spl2_1 | spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f55,f33,f19,f61,f57])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    spl2_1 <=> l1_pre_topc(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    spl2_4 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl2_1 | spl2_4)),
% 0.20/0.41    inference(subsumption_resolution,[],[f54,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f19])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0) | spl2_4),
% 0.20/0.41    inference(resolution,[],[f35,f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f33])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    $false | (~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.20/0.41    inference(subsumption_resolution,[],[f51,f26])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.20/0.41    inference(subsumption_resolution,[],[f50,f34])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f33])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_3 | ~spl2_6)),
% 0.20/0.41    inference(resolution,[],[f48,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ~v3_pre_topc(sK1,sK0) | spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f29])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    spl2_6 <=> ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    spl2_6 | ~spl2_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f45,f41,f47])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    spl2_5 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_5),
% 0.20/0.41    inference(subsumption_resolution,[],[f44,f16])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_5),
% 0.20/0.41    inference(superposition,[],[f42,f17])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ( ! [X0] : (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl2_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f41])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    spl2_5 | ~spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f39,f19,f41])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0)) ) | ~spl2_1),
% 0.20/0.41    inference(resolution,[],[f15,f21])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    spl2_3 | spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f10,f33,f29])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.41    inference(negated_conjecture,[],[f4])).
% 0.20/0.41  fof(f4,conjecture,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ~spl2_3 | ~spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f11,f33,f29])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    spl2_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f12,f24])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f13,f19])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    l1_pre_topc(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (2810)------------------------------
% 0.20/0.41  % (2810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (2810)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (2810)Memory used [KB]: 10618
% 0.20/0.41  % (2810)Time elapsed: 0.007 s
% 0.20/0.41  % (2810)------------------------------
% 0.20/0.41  % (2810)------------------------------
% 0.20/0.42  % (2808)Success in time 0.064 s
%------------------------------------------------------------------------------
