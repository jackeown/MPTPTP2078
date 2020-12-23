%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  210 ( 342 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f54,f62,f69,f73])).

fof(f73,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f71,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f37,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_3
  <=> v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f70,plain,
    ( v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_8
  <=> ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f69,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f65,f60,f25,f67])).

fof(f25,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f65,plain,
    ( ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f27,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f64,plain,
    ( ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_7 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_7 ),
    inference(superposition,[],[f61,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f61,plain,
    ( ! [X0] :
        ( v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f58,f52,f30,f25,f60])).

fof(f30,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f57,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f32,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) )
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f55,f27])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) )
    | ~ spl2_6 ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v3_tops_1(k2_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

fof(f53,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f30,f25,f52])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f49,f32])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f23,f27])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tops_1)).

fof(f48,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f25])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (27535)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.42  % (27535)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f54,f62,f69,f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    $false | (spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8)),
% 0.22/0.42    inference(subsumption_resolution,[],[f71,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.22/0.42    inference(subsumption_resolution,[],[f70,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0) | spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl2_3 <=> v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    v3_tops_1(k2_tops_1(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_8)),
% 0.22/0.42    inference(resolution,[],[f68,f42])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X0] : (~v4_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl2_8 <=> ! [X0] : (v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl2_8 | ~spl2_1 | ~spl2_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f65,f60,f25,f67])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl2_1 <=> l1_pre_topc(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    spl2_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X0] : (v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_7)),
% 0.22/0.42    inference(subsumption_resolution,[],[f64,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0] : (v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_7),
% 0.22/0.42    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    ( ! [X0] : (v3_tops_1(k2_tops_1(sK0,X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_7),
% 0.22/0.42    inference(superposition,[],[f61,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    ( ! [X0] : (v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f60])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f58,f52,f30,f25,f60])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl2_2 <=> v2_pre_topc(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl2_6 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 0.22/0.42    inference(subsumption_resolution,[],[f57,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 0.22/0.42    inference(subsumption_resolution,[],[f56,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    v2_pre_topc(sK0) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0)) ) | (~spl2_1 | ~spl2_6)),
% 0.22/0.42    inference(subsumption_resolution,[],[f55,f27])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0)) ) | ~spl2_6),
% 0.22/0.42    inference(resolution,[],[f53,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_tops_1(k2_tops_1(X0,X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.42    inference(flattening,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0] : (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f52])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl2_6 | ~spl2_1 | ~spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f50,f30,f25,f52])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | (~spl2_1 | ~spl2_2)),
% 0.22/0.42    inference(subsumption_resolution,[],[f49,f32])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (~v2_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | ~spl2_1),
% 0.22/0.42    inference(resolution,[],[f23,f27])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.42    inference(flattening,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tops_1)).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl2_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f45])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : ((~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl2_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f40])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    v4_pre_topc(sK1,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    ~spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f35])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f30])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    v2_pre_topc(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl2_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f25])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    l1_pre_topc(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (27535)------------------------------
% 0.22/0.42  % (27535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (27535)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (27535)Memory used [KB]: 10618
% 0.22/0.42  % (27535)Time elapsed: 0.007 s
% 0.22/0.42  % (27535)------------------------------
% 0.22/0.42  % (27535)------------------------------
% 0.22/0.42  % (27533)Success in time 0.064 s
%------------------------------------------------------------------------------
