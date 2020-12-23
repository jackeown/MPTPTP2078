%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 225 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :    8
%              Number of atoms          :  371 ( 735 expanded)
%              Number of equality atoms :   24 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f42,f47,f52,f56,f60,f64,f68,f72,f76,f80,f86,f92,f99,f104,f111,f119,f143,f154,f172,f182,f193,f194])).

fof(f194,plain,
    ( ~ spl2_14
    | spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f173,f89,f38,f96])).

fof(f96,plain,
    ( spl2_14
  <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f38,plain,
    ( spl2_2
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,
    ( spl2_13
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f173,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_2
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f40,f91])).

fof(f91,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f40,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f193,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f192,f180,f116,f101,f34,f96])).

fof(f34,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f101,plain,
    ( spl2_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f116,plain,
    ( spl2_17
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f180,plain,
    ( spl2_26
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f192,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f191,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f191,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f184,f35])).

fof(f35,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f184,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(superposition,[],[f181,f118])).

fof(f118,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f181,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl2_26
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f178,f141,f89,f70,f49,f180])).

fof(f49,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f141,plain,
    ( spl2_22
  <=> ! [X3] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f178,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f177,f142])).

fof(f142,plain,
    ( ! [X3] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f141])).

fof(f177,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f175,f51])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f175,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(superposition,[],[f71,f91])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f172,plain,
    ( spl2_1
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f171,f152,f116,f101,f96,f34])).

fof(f152,plain,
    ( spl2_23
  <=> ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f171,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f155,f103])).

fof(f155,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(superposition,[],[f153,f118])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl2_23
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f150,f141,f89,f66,f49,f152])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f149,f142])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(superposition,[],[f67,f91])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f143,plain,
    ( spl2_22
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f131,f108,f78,f141])).

fof(f78,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f108,plain,
    ( spl2_16
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f131,plain,
    ( ! [X3] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(resolution,[],[f79,f110])).

fof(f110,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f119,plain,
    ( spl2_17
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f112,f101,f74,f116])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f112,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(resolution,[],[f75,f103])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f111,plain,
    ( spl2_16
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f106,f89,f83,f62,f108])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X0] :
        ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f83,plain,
    ( spl2_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f106,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f105,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(superposition,[],[f63,f91])).

fof(f63,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f104,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f94,f89,f44,f101])).

fof(f44,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f46,f91])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f99,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f93,f89,f38,f96])).

fof(f93,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f39,f91])).

fof(f39,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f92,plain,
    ( spl2_13
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f87,f83,f58,f89])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f87,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(resolution,[],[f59,f85])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f81,f54,f49,f83])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f55,f51])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f80,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f76,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (13414)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f24,f38,f34])).

fof(f24,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f38,f34])).

fof(f25,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:11:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (13423)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (13417)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (13423)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f41,f42,f47,f52,f56,f60,f64,f68,f72,f76,f80,f86,f92,f99,f104,f111,f119,f143,f154,f172,f182,f193,f194])).
% 0.21/0.42  fof(f194,plain,(
% 0.21/0.42    ~spl2_14 | spl2_2 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f173,f89,f38,f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl2_14 <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_2 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl2_13 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl2_2 | ~spl2_13)),
% 0.21/0.42    inference(forward_demodulation,[],[f40,f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    spl2_14 | ~spl2_1 | ~spl2_15 | ~spl2_17 | ~spl2_26),
% 0.21/0.42    inference(avatar_split_clause,[],[f192,f180,f116,f101,f34,f96])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl2_15 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl2_17 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    spl2_26 <=> ! [X0] : (v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.42  fof(f192,plain,(
% 0.21/0.42    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_1 | ~spl2_15 | ~spl2_17 | ~spl2_26)),
% 0.21/0.42    inference(subsumption_resolution,[],[f191,f103])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f101])).
% 0.21/0.42  fof(f191,plain,(
% 0.21/0.42    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_1 | ~spl2_17 | ~spl2_26)),
% 0.21/0.42    inference(subsumption_resolution,[],[f184,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f184,plain,(
% 0.21/0.42    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_17 | ~spl2_26)),
% 0.21/0.42    inference(superposition,[],[f181,f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) | ~spl2_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f116])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    ( ! [X0] : (v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_26),
% 0.21/0.42    inference(avatar_component_clause,[],[f180])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    spl2_26 | ~spl2_4 | ~spl2_9 | ~spl2_13 | ~spl2_22),
% 0.21/0.42    inference(avatar_split_clause,[],[f178,f141,f89,f70,f49,f180])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl2_9 <=> ! [X1,X0] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f141,plain,(
% 0.21/0.42    spl2_22 <=> ! [X3] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.42  fof(f178,plain,(
% 0.21/0.42    ( ! [X0] : (v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_9 | ~spl2_13 | ~spl2_22)),
% 0.21/0.42    inference(forward_demodulation,[],[f177,f142])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    ( ! [X3] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)) ) | ~spl2_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f141])).
% 0.21/0.42  fof(f177,plain,(
% 0.21/0.42    ( ! [X0] : (v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_9 | ~spl2_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f175,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    ( ! [X0] : (v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_9 | ~spl2_13)),
% 0.21/0.42    inference(superposition,[],[f71,f91])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    spl2_1 | ~spl2_14 | ~spl2_15 | ~spl2_17 | ~spl2_23),
% 0.21/0.42    inference(avatar_split_clause,[],[f171,f152,f116,f101,f96,f34])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    spl2_23 <=> ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | (~spl2_15 | ~spl2_17 | ~spl2_23)),
% 0.21/0.42    inference(subsumption_resolution,[],[f155,f103])).
% 0.21/0.42  fof(f155,plain,(
% 0.21/0.42    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_17 | ~spl2_23)),
% 0.21/0.42    inference(superposition,[],[f153,f118])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f152])).
% 0.21/0.42  fof(f154,plain,(
% 0.21/0.42    spl2_23 | ~spl2_4 | ~spl2_8 | ~spl2_13 | ~spl2_22),
% 0.21/0.42    inference(avatar_split_clause,[],[f150,f141,f89,f66,f49,f152])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_8 | ~spl2_13 | ~spl2_22)),
% 0.21/0.42    inference(forward_demodulation,[],[f149,f142])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_8 | ~spl2_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f148,f51])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_8 | ~spl2_13)),
% 0.21/0.42    inference(superposition,[],[f67,f91])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    spl2_22 | ~spl2_11 | ~spl2_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f131,f108,f78,f141])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl2_11 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl2_16 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    ( ! [X3] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)) ) | (~spl2_11 | ~spl2_16)),
% 0.21/0.42    inference(resolution,[],[f79,f110])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f108])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl2_17 | ~spl2_10 | ~spl2_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f112,f101,f74,f116])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) | (~spl2_10 | ~spl2_15)),
% 0.21/0.42    inference(resolution,[],[f75,f103])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl2_16 | ~spl2_7 | ~spl2_12 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f106,f89,f83,f62,f108])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl2_7 <=> ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_12 <=> l1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_7 | ~spl2_12 | ~spl2_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f105,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | (~spl2_7 | ~spl2_13)),
% 0.21/0.42    inference(superposition,[],[f63,f91])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl2_15 | ~spl2_3 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f94,f89,f44,f101])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_3 | ~spl2_13)),
% 0.21/0.43    inference(backward_demodulation,[],[f46,f91])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f93,f89,f38,f96])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_2 | ~spl2_13)),
% 0.21/0.43    inference(backward_demodulation,[],[f39,f91])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl2_13 | ~spl2_6 | ~spl2_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f87,f83,f58,f89])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl2_6 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl2_6 | ~spl2_12)),
% 0.21/0.43    inference(resolution,[],[f59,f85])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl2_12 | ~spl2_4 | ~spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f81,f54,f49,f83])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl2_5 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    l1_struct_0(sK0) | (~spl2_4 | ~spl2_5)),
% 0.21/0.43    inference(resolution,[],[f55,f51])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl2_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl2_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f74])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  % (13414)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl2_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f44])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f38,f34])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f38,f34])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (13423)------------------------------
% 0.21/0.43  % (13423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13423)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (13423)Memory used [KB]: 6140
% 0.21/0.43  % (13423)Time elapsed: 0.009 s
% 0.21/0.43  % (13423)------------------------------
% 0.21/0.43  % (13423)------------------------------
% 0.21/0.43  % (13412)Success in time 0.069 s
%------------------------------------------------------------------------------
