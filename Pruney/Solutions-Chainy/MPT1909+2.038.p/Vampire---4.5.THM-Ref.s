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
% DateTime   : Thu Dec  3 13:22:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 308 expanded)
%              Number of leaves         :   34 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  682 (1820 expanded)
%              Number of equality atoms :   52 ( 194 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f88,f94,f99,f104,f109,f117,f122,f129,f140,f148,f153,f163,f168,f172,f181,f190,f243,f265,f274,f277])).

fof(f277,plain,
    ( ~ spl5_6
    | spl5_36 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl5_6
    | spl5_36 ),
    inference(subsumption_resolution,[],[f275,f72])).

fof(f72,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f275,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_36 ),
    inference(resolution,[],[f273,f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f273,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl5_36
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f274,plain,
    ( ~ spl5_36
    | spl5_3
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f269,f160,f55,f271])).

fof(f55,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f160,plain,
    ( spl5_22
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f269,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_3
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f268,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f268,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_22 ),
    inference(resolution,[],[f162,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f265,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_25
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_25
    | spl5_33 ),
    inference(subsumption_resolution,[],[f263,f242])).

fof(f242,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl5_33
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

% (19078)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f263,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f262,f189])).

fof(f189,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_25
  <=> m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f262,plain,
    ( ~ m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_24 ),
    inference(resolution,[],[f238,f180])).

fof(f180,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl5_24
  <=> m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f237,f108])).

fof(f108,plain,
    ( v3_borsuk_1(sK2,sK0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_13
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f236,f128])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f235,f103])).

fof(f103,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_12
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f234,f62])).

fof(f62,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f233,f57])).

fof(f233,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f232,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f231,f82])).

fof(f82,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_8
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f230,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f230,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f229,f72])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f228,f67])).

fof(f67,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_5
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f89,f116])).

fof(f116,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_tex_2(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v3_borsuk_1(sK2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | X3 != X4
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(f47,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f243,plain,
    ( ~ spl5_33
    | ~ spl5_17
    | spl5_19
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f174,f156,f145,f133,f240])).

fof(f133,plain,
    ( spl5_17
  <=> k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f145,plain,
    ( spl5_19
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f156,plain,
    ( spl5_21
  <=> k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f174,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))
    | ~ spl5_17
    | spl5_19
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f173,f158])).

fof(f158,plain,
    ( k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f156])).

fof(f173,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3))
    | ~ spl5_17
    | spl5_19 ),
    inference(superposition,[],[f147,f135])).

fof(f135,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f147,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f190,plain,
    ( spl5_25
    | ~ spl5_15
    | ~ spl5_21
    | spl5_22 ),
    inference(avatar_split_clause,[],[f185,f160,f156,f119,f187])).

fof(f119,plain,
    ( spl5_15
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f185,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15
    | ~ spl5_21
    | spl5_22 ),
    inference(forward_demodulation,[],[f184,f158])).

fof(f184,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15
    | spl5_22 ),
    inference(subsumption_resolution,[],[f123,f161])).

fof(f161,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f123,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15 ),
    inference(resolution,[],[f121,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f121,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f181,plain,
    ( spl5_24
    | ~ spl5_11
    | ~ spl5_17
    | spl5_18 ),
    inference(avatar_split_clause,[],[f176,f137,f133,f96,f178])).

fof(f96,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f137,plain,
    ( spl5_18
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f176,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_11
    | ~ spl5_17
    | spl5_18 ),
    inference(forward_demodulation,[],[f175,f135])).

fof(f175,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_11
    | spl5_18 ),
    inference(subsumption_resolution,[],[f111,f138])).

fof(f138,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f111,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_11 ),
    inference(resolution,[],[f98,f42])).

fof(f98,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f172,plain,
    ( ~ spl5_6
    | ~ spl5_9
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_9
    | spl5_23 ),
    inference(subsumption_resolution,[],[f170,f72])).

fof(f170,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_23 ),
    inference(resolution,[],[f169,f87])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_23 ),
    inference(resolution,[],[f167,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f167,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_23
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f168,plain,
    ( ~ spl5_23
    | spl5_20 ),
    inference(avatar_split_clause,[],[f154,f150,f165])).

fof(f150,plain,
    ( spl5_20
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f154,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_20 ),
    inference(resolution,[],[f152,f37])).

fof(f152,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f150])).

fof(f163,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f124,f119,f160,f156])).

fof(f124,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3)
    | ~ spl5_15 ),
    inference(resolution,[],[f121,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f153,plain,
    ( ~ spl5_20
    | spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f143,f137,f50,f150])).

fof(f143,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f142,f52])).

fof(f142,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f139,f40])).

fof(f139,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f148,plain,
    ( ~ spl5_19
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f141,f75,f145])).

fof(f75,plain,
    ( spl5_7
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f141,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f23,f77])).

fof(f77,plain,
    ( sK3 = sK4
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f23,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(f140,plain,
    ( spl5_17
    | spl5_18
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f112,f96,f137,f133])).

fof(f112,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f98,f41])).

fof(f129,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f28,f126])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f122,plain,
    ( spl5_15
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f110,f91,f75,f119])).

fof(f91,plain,
    ( spl5_10
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f110,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f93,f77])).

fof(f93,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f117,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f26,f114])).

fof(f26,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f29,f106])).

fof(f29,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f27,f101])).

fof(f27,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f24,f96])).

fof(f24,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f21,f91])).

fof(f21,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f22,f75])).

fof(f22,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:44:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (19074)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (19068)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (19080)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (19080)Refutation not found, incomplete strategy% (19080)------------------------------
% 0.21/0.48  % (19080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19080)Memory used [KB]: 10618
% 0.21/0.48  % (19080)Time elapsed: 0.032 s
% 0.21/0.48  % (19080)------------------------------
% 0.21/0.48  % (19080)------------------------------
% 0.21/0.48  % (19065)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (19062)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (19060)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19060)Refutation not found, incomplete strategy% (19060)------------------------------
% 0.21/0.49  % (19060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19060)Memory used [KB]: 6268
% 0.21/0.49  % (19060)Time elapsed: 0.067 s
% 0.21/0.49  % (19060)------------------------------
% 0.21/0.49  % (19060)------------------------------
% 0.21/0.49  % (19063)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (19075)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (19063)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f88,f94,f99,f104,f109,f117,f122,f129,f140,f148,f153,f163,f168,f172,f181,f190,f243,f265,f274,f277])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ~spl5_6 | spl5_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    $false | (~spl5_6 | spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f275,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl5_6 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl5_36),
% 0.21/0.50    inference(resolution,[],[f273,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | spl5_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl5_36 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~spl5_36 | spl5_3 | ~spl5_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f269,f160,f55,f271])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl5_3 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl5_22 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | (spl5_3 | ~spl5_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f268,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_22),
% 0.21/0.50    inference(resolution,[],[f162,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_16 | ~spl5_24 | ~spl5_25 | spl5_33),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_16 | ~spl5_24 | ~spl5_25 | spl5_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f263,f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) | spl5_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl5_33 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.50  % (19078)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_16 | ~spl5_24 | ~spl5_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f262,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl5_25 <=> m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_16 | ~spl5_24)),
% 0.21/0.50    inference(resolution,[],[f238,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl5_24 <=> m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f237,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v3_borsuk_1(sK2,sK0,sK1) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl5_13 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl5_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_12 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f235,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    v5_pre_topc(sK2,sK0,sK1) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl5_12 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f234,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl5_4 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f233,f57])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f232,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl5_9 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f231,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v4_tex_2(sK1,sK0) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_8 <=> v4_tex_2(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | spl5_2 | ~spl5_5 | ~spl5_6 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f230,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl5_2 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | ~spl5_5 | ~spl5_6 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f229,f72])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | ~spl5_5 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f228,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    v3_tdlat_3(sK0) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl5_5 <=> v3_tdlat_3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_1 | ~spl5_14)),
% 0.21/0.50    inference(resolution,[],[f89,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl5_14 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2)) ) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f47,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 0.21/0.50    inference(equality_resolution,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~spl5_33 | ~spl5_17 | spl5_19 | ~spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f174,f156,f145,f133,f240])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl5_17 <=> k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl5_19 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl5_21 <=> k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) | (~spl5_17 | spl5_19 | ~spl5_21)),
% 0.21/0.50    inference(forward_demodulation,[],[f173,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3) | ~spl5_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k1_tarski(sK3)) | (~spl5_17 | spl5_19)),
% 0.21/0.50    inference(superposition,[],[f147,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f133])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) | spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl5_25 | ~spl5_15 | ~spl5_21 | spl5_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f185,f160,f156,f119,f187])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl5_15 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_15 | ~spl5_21 | spl5_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f184,f158])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_15 | spl5_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_15),
% 0.21/0.50    inference(resolution,[],[f121,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl5_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    spl5_24 | ~spl5_11 | ~spl5_17 | spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f176,f137,f133,f96,f178])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_11 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl5_18 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_11 | ~spl5_17 | spl5_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f175,f135])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_11 | spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f111,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK1)) | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_11),
% 0.21/0.50    inference(resolution,[],[f98,f42])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_9 | spl5_23),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false | (~spl5_6 | ~spl5_9 | spl5_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f72])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | (~spl5_9 | spl5_23)),
% 0.21/0.50    inference(resolution,[],[f169,f87])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl5_23),
% 0.21/0.50    inference(resolution,[],[f167,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl5_23 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~spl5_23 | spl5_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f154,f150,f165])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl5_20 <=> l1_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | spl5_20),
% 0.21/0.50    inference(resolution,[],[f152,f37])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl5_21 | spl5_22 | ~spl5_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f124,f119,f160,f156])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK3) = k6_domain_1(u1_struct_0(sK0),sK3) | ~spl5_15),
% 0.21/0.50    inference(resolution,[],[f121,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ~spl5_20 | spl5_2 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f143,f137,f50,f150])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | (spl5_2 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f52])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_18),
% 0.21/0.50    inference(resolution,[],[f139,f40])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~spl5_19 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f141,f75,f145])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl5_7 <=> sK3 = sK4),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) | ~spl5_7),
% 0.21/0.50    inference(forward_demodulation,[],[f23,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    sK3 = sK4 | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl5_17 | spl5_18 | ~spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f112,f96,f137,f133])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) | ~spl5_11),
% 0.21/0.50    inference(resolution,[],[f98,f41])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl5_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f126])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl5_15 | ~spl5_7 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f91,f75,f119])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl5_10 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl5_7 | ~spl5_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f93,f77])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f114])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f106])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f101])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f96])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f91])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f85])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f80])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v4_tex_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f75])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    sK3 = sK4),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f70])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f65])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v3_tdlat_3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f60])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f55])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f50])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f45])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (19063)------------------------------
% 0.21/0.50  % (19063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19063)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (19063)Memory used [KB]: 10874
% 0.21/0.50  % (19063)Time elapsed: 0.075 s
% 0.21/0.50  % (19063)------------------------------
% 0.21/0.50  % (19063)------------------------------
% 0.21/0.50  % (19058)Success in time 0.137 s
%------------------------------------------------------------------------------
