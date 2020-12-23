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
% DateTime   : Thu Dec  3 13:19:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 487 expanded)
%              Number of leaves         :   47 ( 225 expanded)
%              Depth                    :   13
%              Number of atoms          :  988 (2262 expanded)
%              Number of equality atoms :  145 ( 361 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f102,f106,f110,f114,f118,f127,f132,f205,f246,f252,f266,f274,f309,f315,f321,f329,f337,f351,f353,f360,f361,f365,f368,f403,f417,f469,f478,f525,f531,f534,f538,f543,f643])).

fof(f643,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_6
    | spl3_59
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_67
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f642,f541,f529,f349,f203,f91,f442,f112,f116,f108])).

fof(f108,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f116,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f112,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f442,plain,
    ( spl3_59
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f91,plain,
    ( spl3_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f203,plain,
    ( spl3_23
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f349,plain,
    ( spl3_50
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f529,plain,
    ( spl3_67
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f541,plain,
    ( spl3_68
  <=> k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f642,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_67
    | ~ spl3_68 ),
    inference(forward_demodulation,[],[f641,f542])).

fof(f542,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f541])).

fof(f641,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_50
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f640,f530])).

fof(f530,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f529])).

fof(f640,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f639,f204])).

fof(f204,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f639,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f638,f366])).

fof(f366,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f349])).

fof(f638,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f632,f97])).

fof(f97,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f632,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f121,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k8_tmap_1(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k8_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f80,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f543,plain,
    ( ~ spl3_9
    | spl3_68
    | ~ spl3_2
    | ~ spl3_66
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f539,f529,f523,f91,f541,f130])).

fof(f130,plain,
    ( spl3_9
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f523,plain,
    ( spl3_66
  <=> ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v3_pre_topc(u1_struct_0(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f539,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_2
    | ~ spl3_66
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f535,f530])).

fof(f535,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_2
    | ~ spl3_66 ),
    inference(resolution,[],[f524,f97])).

fof(f524,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK0) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f523])).

fof(f538,plain,
    ( ~ spl3_9
    | spl3_57
    | ~ spl3_2
    | ~ spl3_59
    | ~ spl3_66
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f537,f529,f523,f442,f91,f401,f130])).

fof(f401,plain,
    ( spl3_57
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f537,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_2
    | ~ spl3_59
    | ~ spl3_66
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f536,f530])).

fof(f536,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_2
    | ~ spl3_59
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f535,f501])).

fof(f501,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f442])).

fof(f534,plain,
    ( ~ spl3_57
    | spl3_3
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f532,f529,f94,f401])).

fof(f94,plain,
    ( spl3_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f532,plain,
    ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k2_struct_0(sK0))
    | spl3_3
    | ~ spl3_67 ),
    inference(superposition,[],[f95,f530])).

fof(f95,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f531,plain,
    ( ~ spl3_32
    | spl3_67
    | ~ spl3_30
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f521,f363,f241,f529,f250])).

fof(f250,plain,
    ( spl3_32
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f241,plain,
    ( spl3_30
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f363,plain,
    ( spl3_52
  <=> ! [X1] :
        ( ~ v3_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f521,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_30
    | ~ spl3_52 ),
    inference(resolution,[],[f364,f242])).

fof(f242,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f364,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f363])).

fof(f525,plain,
    ( ~ spl3_5
    | spl3_66
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f519,f363,f523,f108])).

fof(f519,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_52 ),
    inference(resolution,[],[f364,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f478,plain,
    ( ~ spl3_30
    | ~ spl3_32
    | spl3_50
    | ~ spl3_45
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f476,f467,f319,f349,f250,f241])).

fof(f319,plain,
    ( spl3_45
  <=> ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f467,plain,
    ( spl3_62
  <=> u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f476,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_45
    | ~ spl3_62 ),
    inference(superposition,[],[f320,f468])).

fof(f468,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f467])).

fof(f320,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f319])).

fof(f469,plain,
    ( ~ spl3_30
    | spl3_62
    | ~ spl3_36
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f454,f401,f272,f467,f241])).

fof(f272,plain,
    ( spl3_36
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f454,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_36
    | ~ spl3_57 ),
    inference(superposition,[],[f273,f402])).

fof(f402,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f401])).

fof(f273,plain,
    ( ! [X1] :
        ( k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f272])).

fof(f417,plain,
    ( ~ spl3_2
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f97,f265])).

fof(f265,plain,
    ( ! [X0] : ~ m1_pre_topc(X0,sK0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_34
  <=> ! [X0] : ~ m1_pre_topc(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f403,plain,
    ( ~ spl3_32
    | spl3_57
    | ~ spl3_30
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f394,f358,f241,f401,f250])).

fof(f358,plain,
    ( spl3_51
  <=> ! [X1] :
        ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f394,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_30
    | ~ spl3_51 ),
    inference(resolution,[],[f359,f242])).

fof(f359,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f358])).

fof(f368,plain,
    ( ~ spl3_49
    | ~ spl3_9
    | spl3_50
    | ~ spl3_43
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f322,f319,f307,f349,f130,f346])).

fof(f346,plain,
    ( spl3_49
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f307,plain,
    ( spl3_43
  <=> u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f322,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_43
    | ~ spl3_45 ),
    inference(superposition,[],[f320,f308])).

fof(f308,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f307])).

fof(f365,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_52
    | spl3_7 ),
    inference(avatar_split_clause,[],[f355,f116,f363,f108,f112])).

fof(f355,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) )
    | spl3_7 ),
    inference(resolution,[],[f73,f117])).

fof(f117,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f361,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | ~ spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f133,f130,f88,f91,f108])).

fof(f88,plain,
    ( spl3_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f131,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f63,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f131,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f360,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_51
    | ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f356,f116,f94,f358,f108,f112])).

fof(f356,plain,
    ( ! [X1] :
        ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_3
    | spl3_7 ),
    inference(forward_demodulation,[],[f355,f98])).

fof(f98,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f353,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_49 ),
    inference(avatar_split_clause,[],[f352,f346,f91,f108])).

fof(f352,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_49 ),
    inference(resolution,[],[f347,f63])).

fof(f347,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f346])).

fof(f351,plain,
    ( ~ spl3_49
    | ~ spl3_50
    | spl3_9
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f344,f335,f307,f130,f349,f346])).

fof(f335,plain,
    ( spl3_47
  <=> ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f344,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f339,f308])).

fof(f339,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9
    | ~ spl3_47 ),
    inference(resolution,[],[f336,f131])).

fof(f336,plain,
    ( ! [X1] :
        ( v3_pre_topc(X1,sK0)
        | u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( ~ spl3_5
    | spl3_47
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f332,f327,f335,f108])).

fof(f327,plain,
    ( spl3_46
  <=> ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | r2_hidden(X1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f332,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_46 ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_46 ),
    inference(resolution,[],[f328,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f328,plain,
    ( ! [X1] :
        ( r2_hidden(X1,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_46
    | spl3_7 ),
    inference(avatar_split_clause,[],[f325,f116,f327,f108,f112])).

fof(f325,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_hidden(X1,u1_pre_topc(sK0)) )
    | spl3_7 ),
    inference(resolution,[],[f76,f117])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f321,plain,
    ( ~ spl3_5
    | spl3_45
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f317,f313,f319,f108])).

fof(f313,plain,
    ( spl3_44
  <=> ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f317,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_44 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_44 ),
    inference(resolution,[],[f314,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f313])).

fof(f315,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_44
    | spl3_7 ),
    inference(avatar_split_clause,[],[f311,f116,f313,f108,f112])).

fof(f311,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) )
    | spl3_7 ),
    inference(resolution,[],[f75,f117])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f309,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_4
    | spl3_43
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f305,f91,f307,f104,f108,f112,f116])).

fof(f104,plain,
    ( spl3_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f305,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f120,f97])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f63,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f274,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_36
    | spl3_7 ),
    inference(avatar_split_clause,[],[f260,f116,f272,f108,f112])).

fof(f260,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1)) )
    | spl3_7 ),
    inference(resolution,[],[f72,f117])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f266,plain,
    ( ~ spl3_5
    | spl3_34
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f261,f244,f264,f108])).

fof(f244,plain,
    ( spl3_31
  <=> ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_31 ),
    inference(resolution,[],[f245,f63])).

fof(f245,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f244])).

fof(f252,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_32
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f247,f241,f250,f108,f112])).

fof(f247,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f242,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(superposition,[],[f83,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f246,plain,
    ( spl3_30
    | ~ spl3_6
    | ~ spl3_5
    | spl3_31
    | spl3_7 ),
    inference(avatar_split_clause,[],[f239,f116,f244,f108,f112,f241])).

fof(f239,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_7 ),
    inference(resolution,[],[f207,f117])).

fof(f207,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f205,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_4
    | spl3_23
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f199,f91,f203,f104,f108,f112,f116])).

fof(f199,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f77,f97])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_1
    | ~ spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f128,f125,f130,f88,f91,f108])).

fof(f125,plain,
    ( spl3_8
  <=> u1_struct_0(sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(superposition,[],[f67,f126])).

fof(f126,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f122,f88,f125,f91,f108])).

fof(f122,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f66,f89])).

fof(f89,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f54,f116])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f114,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f56,f108])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f58,f91])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f59,f94,f88])).

fof(f59,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f94,f91,f88])).

fof(f61,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (27623)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.44  % (27623)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f644,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f96,f101,f102,f106,f110,f114,f118,f127,f132,f205,f246,f252,f266,f274,f309,f315,f321,f329,f337,f351,f353,f360,f361,f365,f368,f403,f417,f469,f478,f525,f531,f534,f538,f543,f643])).
% 0.21/0.44  fof(f643,plain,(
% 0.21/0.44    ~spl3_5 | spl3_7 | ~spl3_6 | spl3_59 | ~spl3_2 | ~spl3_23 | ~spl3_50 | ~spl3_67 | ~spl3_68),
% 0.21/0.44    inference(avatar_split_clause,[],[f642,f541,f529,f349,f203,f91,f442,f112,f116,f108])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl3_5 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl3_7 <=> v2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    spl3_6 <=> v2_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f442,plain,(
% 0.21/0.44    spl3_59 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl3_2 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f203,plain,(
% 0.21/0.44    spl3_23 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.44  fof(f349,plain,(
% 0.21/0.44    spl3_50 <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.44  fof(f529,plain,(
% 0.21/0.44    spl3_67 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.21/0.44  fof(f541,plain,(
% 0.21/0.44    spl3_68 <=> k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.21/0.44  fof(f642,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_23 | ~spl3_50 | ~spl3_67 | ~spl3_68)),
% 0.21/0.44    inference(forward_demodulation,[],[f641,f542])).
% 0.21/0.44  fof(f542,plain,(
% 0.21/0.44    k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~spl3_68),
% 0.21/0.44    inference(avatar_component_clause,[],[f541])).
% 0.21/0.44  fof(f641,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_23 | ~spl3_50 | ~spl3_67)),
% 0.21/0.44    inference(forward_demodulation,[],[f640,f530])).
% 0.21/0.44  fof(f530,plain,(
% 0.21/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~spl3_67),
% 0.21/0.44    inference(avatar_component_clause,[],[f529])).
% 0.21/0.44  fof(f640,plain,(
% 0.21/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_23 | ~spl3_50)),
% 0.21/0.44    inference(forward_demodulation,[],[f639,f204])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl3_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f203])).
% 0.21/0.44  fof(f639,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_50)),
% 0.21/0.44    inference(forward_demodulation,[],[f638,f366])).
% 0.21/0.44  fof(f366,plain,(
% 0.21/0.44    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl3_50),
% 0.21/0.44    inference(avatar_component_clause,[],[f349])).
% 0.21/0.44  fof(f638,plain,(
% 0.21/0.44    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.44    inference(resolution,[],[f632,f97])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f632,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f631])).
% 0.21/0.44  fof(f631,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(resolution,[],[f121,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(k8_tmap_1(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k8_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.44    inference(resolution,[],[f80,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f37])).
% 0.21/0.44  fof(f543,plain,(
% 0.21/0.44    ~spl3_9 | spl3_68 | ~spl3_2 | ~spl3_66 | ~spl3_67),
% 0.21/0.44    inference(avatar_split_clause,[],[f539,f529,f523,f91,f541,f130])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_9 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f523,plain,(
% 0.21/0.44    spl3_66 <=> ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v3_pre_topc(u1_struct_0(X0),sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.44  fof(f539,plain,(
% 0.21/0.44    k6_tmap_1(sK0,u1_struct_0(sK1)) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_2 | ~spl3_66 | ~spl3_67)),
% 0.21/0.44    inference(forward_demodulation,[],[f535,f530])).
% 0.21/0.44  fof(f535,plain,(
% 0.21/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_2 | ~spl3_66)),
% 0.21/0.44    inference(resolution,[],[f524,f97])).
% 0.21/0.44  fof(f524,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK0)) ) | ~spl3_66),
% 0.21/0.44    inference(avatar_component_clause,[],[f523])).
% 0.21/0.44  fof(f538,plain,(
% 0.21/0.44    ~spl3_9 | spl3_57 | ~spl3_2 | ~spl3_59 | ~spl3_66 | ~spl3_67),
% 0.21/0.44    inference(avatar_split_clause,[],[f537,f529,f523,f442,f91,f401,f130])).
% 0.21/0.44  fof(f401,plain,(
% 0.21/0.44    spl3_57 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.44  fof(f537,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_2 | ~spl3_59 | ~spl3_66 | ~spl3_67)),
% 0.21/0.44    inference(forward_demodulation,[],[f536,f530])).
% 0.21/0.44  fof(f536,plain,(
% 0.21/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_2 | ~spl3_59 | ~spl3_66)),
% 0.21/0.44    inference(forward_demodulation,[],[f535,f501])).
% 0.21/0.44  fof(f501,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl3_59),
% 0.21/0.44    inference(avatar_component_clause,[],[f442])).
% 0.21/0.44  fof(f534,plain,(
% 0.21/0.44    ~spl3_57 | spl3_3 | ~spl3_67),
% 0.21/0.44    inference(avatar_split_clause,[],[f532,f529,f94,f401])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl3_3 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f532,plain,(
% 0.21/0.44    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k2_struct_0(sK0)) | (spl3_3 | ~spl3_67)),
% 0.21/0.44    inference(superposition,[],[f95,f530])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f94])).
% 0.21/0.44  fof(f531,plain,(
% 0.21/0.44    ~spl3_32 | spl3_67 | ~spl3_30 | ~spl3_52),
% 0.21/0.44    inference(avatar_split_clause,[],[f521,f363,f241,f529,f250])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    spl3_32 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.45  fof(f241,plain,(
% 0.21/0.45    spl3_30 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.45  fof(f363,plain,(
% 0.21/0.45    spl3_52 <=> ! [X1] : (~v3_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.45  fof(f521,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_30 | ~spl3_52)),
% 0.21/0.45    inference(resolution,[],[f364,f242])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_30),
% 0.21/0.45    inference(avatar_component_clause,[],[f241])).
% 0.21/0.45  fof(f364,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) ) | ~spl3_52),
% 0.21/0.45    inference(avatar_component_clause,[],[f363])).
% 0.21/0.45  fof(f525,plain,(
% 0.21/0.45    ~spl3_5 | spl3_66 | ~spl3_52),
% 0.21/0.45    inference(avatar_split_clause,[],[f519,f363,f523,f108])).
% 0.21/0.45  fof(f519,plain,(
% 0.21/0.45    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_52),
% 0.21/0.45    inference(resolution,[],[f364,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.45  fof(f478,plain,(
% 0.21/0.45    ~spl3_30 | ~spl3_32 | spl3_50 | ~spl3_45 | ~spl3_62),
% 0.21/0.45    inference(avatar_split_clause,[],[f476,f467,f319,f349,f250,f241])).
% 0.21/0.45  fof(f319,plain,(
% 0.21/0.45    spl3_45 <=> ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.45  fof(f467,plain,(
% 0.21/0.45    spl3_62 <=> u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.45  fof(f476,plain,(
% 0.21/0.45    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_45 | ~spl3_62)),
% 0.21/0.45    inference(superposition,[],[f320,f468])).
% 0.21/0.45  fof(f468,plain,(
% 0.21/0.45    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0)) | ~spl3_62),
% 0.21/0.45    inference(avatar_component_clause,[],[f467])).
% 0.21/0.45  fof(f320,plain,(
% 0.21/0.45    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_45),
% 0.21/0.45    inference(avatar_component_clause,[],[f319])).
% 0.21/0.45  fof(f469,plain,(
% 0.21/0.45    ~spl3_30 | spl3_62 | ~spl3_36 | ~spl3_57),
% 0.21/0.45    inference(avatar_split_clause,[],[f454,f401,f272,f467,f241])).
% 0.21/0.45  fof(f272,plain,(
% 0.21/0.45    spl3_36 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.45  fof(f454,plain,(
% 0.21/0.45    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_36 | ~spl3_57)),
% 0.21/0.45    inference(superposition,[],[f273,f402])).
% 0.21/0.45  fof(f402,plain,(
% 0.21/0.45    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~spl3_57),
% 0.21/0.45    inference(avatar_component_clause,[],[f401])).
% 0.21/0.45  fof(f273,plain,(
% 0.21/0.45    ( ! [X1] : (k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_36),
% 0.21/0.45    inference(avatar_component_clause,[],[f272])).
% 0.21/0.45  fof(f417,plain,(
% 0.21/0.45    ~spl3_2 | ~spl3_34),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.45  fof(f416,plain,(
% 0.21/0.45    $false | (~spl3_2 | ~spl3_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f97,f265])).
% 0.21/0.45  fof(f265,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK0)) ) | ~spl3_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f264])).
% 0.21/0.45  fof(f264,plain,(
% 0.21/0.45    spl3_34 <=> ! [X0] : ~m1_pre_topc(X0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.45  fof(f403,plain,(
% 0.21/0.45    ~spl3_32 | spl3_57 | ~spl3_30 | ~spl3_51),
% 0.21/0.45    inference(avatar_split_clause,[],[f394,f358,f241,f401,f250])).
% 0.21/0.45  fof(f358,plain,(
% 0.21/0.45    spl3_51 <=> ! [X1] : (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.45  fof(f394,plain,(
% 0.21/0.45    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k2_struct_0(sK0)) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_30 | ~spl3_51)),
% 0.21/0.45    inference(resolution,[],[f359,f242])).
% 0.21/0.45  fof(f359,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) ) | ~spl3_51),
% 0.21/0.45    inference(avatar_component_clause,[],[f358])).
% 0.21/0.45  fof(f368,plain,(
% 0.21/0.45    ~spl3_49 | ~spl3_9 | spl3_50 | ~spl3_43 | ~spl3_45),
% 0.21/0.45    inference(avatar_split_clause,[],[f322,f319,f307,f349,f130,f346])).
% 0.21/0.45  fof(f346,plain,(
% 0.21/0.45    spl3_49 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    spl3_43 <=> u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.45  fof(f322,plain,(
% 0.21/0.45    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_43 | ~spl3_45)),
% 0.21/0.45    inference(superposition,[],[f320,f308])).
% 0.21/0.45  fof(f308,plain,(
% 0.21/0.45    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~spl3_43),
% 0.21/0.45    inference(avatar_component_clause,[],[f307])).
% 0.21/0.45  fof(f365,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_52 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f355,f116,f363,f108,f112])).
% 0.21/0.45  fof(f355,plain,(
% 0.21/0.45    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)) ) | spl3_7),
% 0.21/0.45    inference(resolution,[],[f73,f117])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ~v2_struct_0(sK0) | spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f116])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.45  fof(f361,plain,(
% 0.21/0.45    ~spl3_5 | ~spl3_2 | ~spl3_1 | spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f133,f130,f88,f91,f108])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl3_1 <=> v1_tsep_1(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_9),
% 0.21/0.45    inference(resolution,[],[f131,f119])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(global_subsumption,[],[f63,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(rectify,[],[f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ~v3_pre_topc(u1_struct_0(sK1),sK0) | spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f130])).
% 0.21/0.45  fof(f360,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_51 | ~spl3_3 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f356,f116,f94,f358,f108,f112])).
% 0.21/0.45  fof(f356,plain,(
% 0.21/0.45    ( ! [X1] : (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_3 | spl3_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f355,f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f353,plain,(
% 0.21/0.45    ~spl3_5 | ~spl3_2 | spl3_49),
% 0.21/0.45    inference(avatar_split_clause,[],[f352,f346,f91,f108])).
% 0.21/0.45  fof(f352,plain,(
% 0.21/0.45    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_49),
% 0.21/0.45    inference(resolution,[],[f347,f63])).
% 0.21/0.45  fof(f347,plain,(
% 0.21/0.45    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_49),
% 0.21/0.45    inference(avatar_component_clause,[],[f346])).
% 0.21/0.45  fof(f351,plain,(
% 0.21/0.45    ~spl3_49 | ~spl3_50 | spl3_9 | ~spl3_43 | ~spl3_47),
% 0.21/0.45    inference(avatar_split_clause,[],[f344,f335,f307,f130,f349,f346])).
% 0.21/0.45  fof(f335,plain,(
% 0.21/0.45    spl3_47 <=> ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.45  fof(f344,plain,(
% 0.21/0.45    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_9 | ~spl3_43 | ~spl3_47)),
% 0.21/0.45    inference(forward_demodulation,[],[f339,f308])).
% 0.21/0.45  fof(f339,plain,(
% 0.21/0.45    u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_9 | ~spl3_47)),
% 0.21/0.45    inference(resolution,[],[f336,f131])).
% 0.21/0.45  fof(f336,plain,(
% 0.21/0.45    ( ! [X1] : (v3_pre_topc(X1,sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_47),
% 0.21/0.45    inference(avatar_component_clause,[],[f335])).
% 0.21/0.45  fof(f337,plain,(
% 0.21/0.45    ~spl3_5 | spl3_47 | ~spl3_46),
% 0.21/0.45    inference(avatar_split_clause,[],[f332,f327,f335,f108])).
% 0.21/0.45  fof(f327,plain,(
% 0.21/0.45    spl3_46 <=> ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | r2_hidden(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.45  fof(f332,plain,(
% 0.21/0.45    ( ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_46),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f331])).
% 0.21/0.45  fof(f331,plain,(
% 0.21/0.45    ( ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_46),
% 0.21/0.45    inference(resolution,[],[f328,f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.45  fof(f328,plain,(
% 0.21/0.45    ( ! [X1] : (r2_hidden(X1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_46),
% 0.21/0.45    inference(avatar_component_clause,[],[f327])).
% 0.21/0.45  fof(f329,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_46 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f325,f116,f327,f108,f112])).
% 0.21/0.45  fof(f325,plain,(
% 0.21/0.45    ( ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X1,u1_pre_topc(sK0))) ) | spl3_7),
% 0.21/0.45    inference(resolution,[],[f76,f117])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.45  fof(f321,plain,(
% 0.21/0.45    ~spl3_5 | spl3_45 | ~spl3_44),
% 0.21/0.45    inference(avatar_split_clause,[],[f317,f313,f319,f108])).
% 0.21/0.45  fof(f313,plain,(
% 0.21/0.45    spl3_44 <=> ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.45  fof(f317,plain,(
% 0.21/0.45    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_44),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f316])).
% 0.21/0.45  fof(f316,plain,(
% 0.21/0.45    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_44),
% 0.21/0.45    inference(resolution,[],[f314,f68])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f51])).
% 0.21/0.45  fof(f314,plain,(
% 0.21/0.45    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_44),
% 0.21/0.45    inference(avatar_component_clause,[],[f313])).
% 0.21/0.45  fof(f315,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_44 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f311,f116,f313,f108,f112])).
% 0.21/0.45  fof(f311,plain,(
% 0.21/0.45    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)) ) | spl3_7),
% 0.21/0.45    inference(resolution,[],[f75,f117])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f53])).
% 0.21/0.45  fof(f309,plain,(
% 0.21/0.45    spl3_7 | ~spl3_6 | ~spl3_5 | spl3_4 | spl3_43 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f305,f91,f307,f104,f108,f112,f116])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl3_4 <=> v2_struct_0(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f305,plain,(
% 0.21/0.45    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.45    inference(resolution,[],[f120,f97])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(global_subsumption,[],[f63,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.21/0.45  fof(f274,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_36 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f260,f116,f272,f108,f112])).
% 0.21/0.45  fof(f260,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k5_tmap_1(sK0,X1) = u1_pre_topc(k6_tmap_1(sK0,X1))) ) | spl3_7),
% 0.21/0.45    inference(resolution,[],[f72,f117])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.45  fof(f266,plain,(
% 0.21/0.45    ~spl3_5 | spl3_34 | ~spl3_31),
% 0.21/0.45    inference(avatar_split_clause,[],[f261,f244,f264,f108])).
% 0.21/0.45  fof(f244,plain,(
% 0.21/0.45    spl3_31 <=> ! [X1] : ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.45  fof(f261,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_31),
% 0.21/0.45    inference(resolution,[],[f245,f63])).
% 0.21/0.45  fof(f245,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_31),
% 0.21/0.45    inference(avatar_component_clause,[],[f244])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_5 | spl3_32 | ~spl3_30),
% 0.21/0.45    inference(avatar_split_clause,[],[f247,f241,f250,f108,f112])).
% 0.21/0.45  fof(f247,plain,(
% 0.21/0.45    v3_pre_topc(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_30),
% 0.21/0.45    inference(resolution,[],[f242,f137])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(superposition,[],[f83,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.45  fof(f246,plain,(
% 0.21/0.45    spl3_30 | ~spl3_6 | ~spl3_5 | spl3_31 | spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f239,f116,f244,f108,f112,f241])).
% 0.21/0.45  fof(f239,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl3_7),
% 0.21/0.45    inference(resolution,[],[f207,f117])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f206])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(resolution,[],[f84,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m2_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    spl3_7 | ~spl3_6 | ~spl3_5 | spl3_4 | spl3_23 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f199,f91,f203,f104,f108,f112,f116])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.45    inference(resolution,[],[f77,f97])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ~spl3_5 | ~spl3_2 | spl3_1 | ~spl3_9 | ~spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f128,f125,f130,f88,f91,f108])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    spl3_8 <=> u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_8),
% 0.21/0.45    inference(superposition,[],[f67,f126])).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    u1_struct_0(sK1) = sK2(sK0,sK1) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f125])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f50])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ~spl3_5 | ~spl3_2 | spl3_8 | spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f122,f88,f125,f91,f108])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    u1_struct_0(sK1) = sK2(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.45    inference(resolution,[],[f66,f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    ~v1_tsep_1(sK1,sK0) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f88])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f50])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ~spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f54,f116])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ~v2_struct_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f14])).
% 0.21/0.45  fof(f14,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f55,f112])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f108])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ~spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f57,f104])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ~v2_struct_0(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f58,f91])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    m1_pre_topc(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    spl3_1 | spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f59,f94,f88])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f61,f94,f91,f88])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (27623)------------------------------
% 0.21/0.45  % (27623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (27623)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (27623)Memory used [KB]: 11001
% 0.21/0.45  % (27623)Time elapsed: 0.027 s
% 0.21/0.45  % (27623)------------------------------
% 0.21/0.45  % (27623)------------------------------
% 0.21/0.45  % (27616)Success in time 0.096 s
%------------------------------------------------------------------------------
