%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 259 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f42,f56,f61,f87,f117,f125,f132])).

fof(f132,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f130,f35])).

fof(f35,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f130,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f129,f55])).

fof(f55,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_6
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f129,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f128,f26])).

fof(f26,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f128,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f126,f73])).

fof(f73,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_9
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f126,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(resolution,[],[f40,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f40,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_4
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f125,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f124,f72,f59,f53,f38])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f124,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(global_subsumption,[],[f13,f123])).

fof(f123,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f94,f73])).

fof(f94,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f60,f55])).

fof(f60,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f13,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f117,plain,
    ( ~ spl2_2
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl2_2
    | spl2_11 ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_11 ),
    inference(subsumption_resolution,[],[f114,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f114,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_11 ),
    inference(superposition,[],[f86,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f86,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_11
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f87,plain,
    ( ~ spl2_11
    | spl2_9 ),
    inference(avatar_split_clause,[],[f81,f72,f84])).

fof(f81,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl2_9 ),
    inference(resolution,[],[f74,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f61,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f57,f24,f59])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f17,f26])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f29,f53])).

fof(f50,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f20,f31])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f42,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f12,f38,f34])).

fof(f12,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (17664)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (17659)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (17659)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f136,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f27,f32,f42,f56,f61,f87,f117,f125,f132])).
% 0.20/0.42  fof(f132,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_9),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.42  fof(f131,plain,(
% 0.20/0.42    $false | (~spl2_1 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f130,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    ~v3_pre_topc(sK1,sK0) | (~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.42    inference(forward_demodulation,[],[f129,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_6 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl2_1 | spl2_4 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f128,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    spl2_1 <=> l1_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0) | (spl2_4 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f126,f73])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    spl2_9 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0) | spl2_4),
% 0.20/0.42    inference(resolution,[],[f40,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_4 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f124,f72,f59,f53,f38])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl2_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_7 | ~spl2_9)),
% 0.20/0.42    inference(global_subsumption,[],[f13,f123])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_7 | ~spl2_9)),
% 0.20/0.42    inference(subsumption_resolution,[],[f94,f73])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_7)),
% 0.20/0.42    inference(superposition,[],[f60,f55])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0] : (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f59])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    ~spl2_2 | spl2_11),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    $false | (~spl2_2 | spl2_11)),
% 0.20/0.42    inference(subsumption_resolution,[],[f115,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_11),
% 0.20/0.42    inference(subsumption_resolution,[],[f114,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_11),
% 0.20/0.42    inference(superposition,[],[f86,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f84])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_11 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    ~spl2_11 | spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f81,f72,f84])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl2_9),
% 0.20/0.42    inference(resolution,[],[f74,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f72])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_7 | ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f57,f24,f59])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0)) ) | ~spl2_1),
% 0.20/0.42    inference(resolution,[],[f17,f26])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl2_6 | ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f50,f29,f53])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_2),
% 0.20/0.42    inference(resolution,[],[f20,f31])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_3 | spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f12,f38,f34])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f29])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f24])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (17659)------------------------------
% 0.20/0.42  % (17659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (17659)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (17659)Memory used [KB]: 10618
% 0.20/0.42  % (17659)Time elapsed: 0.006 s
% 0.20/0.42  % (17659)------------------------------
% 0.20/0.42  % (17659)------------------------------
% 0.20/0.43  % (17665)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (17657)Success in time 0.072 s
%------------------------------------------------------------------------------
