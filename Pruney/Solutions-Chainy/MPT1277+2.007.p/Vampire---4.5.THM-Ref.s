%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 119 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  205 ( 351 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f62,f68,f96,f111,f129,f135,f179])).

fof(f179,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | spl2_18 ),
    inference(subsumption_resolution,[],[f177,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f177,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | spl2_18 ),
    inference(subsumption_resolution,[],[f167,f45])).

fof(f45,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f167,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_18 ),
    inference(superposition,[],[f134,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f134,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl2_18
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f135,plain,
    ( ~ spl2_18
    | ~ spl2_14
    | ~ spl2_1
    | spl2_15 ),
    inference(avatar_split_clause,[],[f130,f108,f28,f104,f132])).

fof(f104,plain,
    ( spl2_14
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f28,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f108,plain,
    ( spl2_15
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f130,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl2_1
    | spl2_15 ),
    inference(subsumption_resolution,[],[f126,f30])).

fof(f30,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f126,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_15 ),
    inference(resolution,[],[f110,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f110,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f129,plain,
    ( ~ spl2_5
    | spl2_14 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl2_5
    | spl2_14 ),
    inference(subsumption_resolution,[],[f127,f50])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_14 ),
    inference(resolution,[],[f106,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f106,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ spl2_14
    | ~ spl2_15
    | spl2_3
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f102,f93,f66,f38,f108,f104])).

fof(f38,plain,
    ( spl2_3
  <=> v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f93,plain,
    ( spl2_12
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f102,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f40,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f101,plain,
    ( v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(superposition,[],[f67,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f67,plain,
    ( ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f96,plain,
    ( spl2_12
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f90,f60,f48,f93])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f68,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f33,f28,f66])).

fof(f33,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,X0),sK0) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,X0),sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v3_tops_1(k2_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).

fof(f62,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f58,f28,f60])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f21,f30])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f28])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (32529)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (32538)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (32529)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f62,f68,f96,f111,f129,f135,f179])).
% 0.21/0.42  fof(f179,plain,(
% 0.21/0.42    ~spl2_4 | ~spl2_5 | spl2_18),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.42  fof(f178,plain,(
% 0.21/0.42    $false | (~spl2_4 | ~spl2_5 | spl2_18)),
% 0.21/0.42    inference(subsumption_resolution,[],[f177,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f177,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | spl2_18)),
% 0.21/0.42    inference(subsumption_resolution,[],[f167,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f167,plain,(
% 0.21/0.42    ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_18),
% 0.21/0.42    inference(superposition,[],[f134,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | spl2_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl2_18 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    ~spl2_18 | ~spl2_14 | ~spl2_1 | spl2_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f108,f28,f104,f132])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl2_14 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl2_1 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl2_15 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl2_1 | spl2_15)),
% 0.21/0.42    inference(subsumption_resolution,[],[f126,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0) | spl2_15),
% 0.21/0.42    inference(resolution,[],[f110,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f108])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    ~spl2_5 | spl2_14),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    $false | (~spl2_5 | spl2_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f127,f50])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_14),
% 0.21/0.42    inference(resolution,[],[f106,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f104])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    ~spl2_14 | ~spl2_15 | spl2_3 | ~spl2_8 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f102,f93,f66,f38,f108,f104])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_3 <=> v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,X0),sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl2_12 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_3 | ~spl2_8 | ~spl2_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f101,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0) | spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    v3_tops_1(k2_tops_1(sK0,sK1),sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_8 | ~spl2_12)),
% 0.21/0.42    inference(superposition,[],[f67,f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl2_12 | ~spl2_5 | ~spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f90,f60,f48,f93])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl2_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_5 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f61,f50])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_8 | ~spl2_1 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f33,f28,f66])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl2_2 <=> v2_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,X0),sK0)) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,X0),sK0)) ) | ~spl2_2),
% 0.21/0.42    inference(resolution,[],[f24,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    v2_pre_topc(sK0) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_tops_1(k2_tops_1(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl2_7 | ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f58,f28,f60])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl2_1),
% 0.21/0.42    inference(resolution,[],[f21,f30])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f48])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f43])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v4_pre_topc(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ~spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f33])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    v2_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f28])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (32529)------------------------------
% 0.21/0.42  % (32529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (32529)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (32529)Memory used [KB]: 10618
% 0.21/0.42  % (32529)Time elapsed: 0.009 s
% 0.21/0.42  % (32529)------------------------------
% 0.21/0.42  % (32529)------------------------------
% 0.21/0.42  % (32527)Success in time 0.066 s
%------------------------------------------------------------------------------
