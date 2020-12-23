%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1221+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 233 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :    8
%              Number of atoms          :  393 ( 761 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f42,f47,f52,f56,f60,f64,f68,f72,f76,f80,f86,f92,f99,f104,f111,f121,f149,f161,f170,f172,f189,f194])).

fof(f194,plain,
    ( ~ spl2_1
    | spl2_14
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl2_1
    | spl2_14
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f192,f97])).

fof(f97,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_14
  <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f192,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f191,f120])).

fof(f120,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_17
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f191,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f190,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f190,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(resolution,[],[f188,f35])).

fof(f35,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl2_26
  <=> ! [X0] :
        ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f189,plain,
    ( spl2_26
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f185,f147,f89,f70,f49,f187])).

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

fof(f89,plain,
    ( spl2_13
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f147,plain,
    ( spl2_22
  <=> ! [X4] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X4) = k4_xboole_0(k2_struct_0(sK0),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f185,plain,
    ( ! [X0] :
        ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f184,f148])).

fof(f148,plain,
    ( ! [X4] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X4) = k4_xboole_0(k2_struct_0(sK0),X4)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f184,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f183,f91])).

fof(f91,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f182,f91])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f172,plain,
    ( ~ spl2_14
    | spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f171,f89,f38,f96])).

fof(f38,plain,
    ( spl2_2
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f171,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_2
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f40,f91])).

fof(f40,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f170,plain,
    ( spl2_1
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f169,f159,f118,f101,f96,f34])).

fof(f159,plain,
    ( spl2_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f169,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f162,f103])).

fof(f162,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_17
    | ~ spl2_23 ),
    inference(superposition,[],[f160,f120])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl2_23
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f157,f147,f89,f66,f49,f159])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f156,f91])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f155,f148])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f154,f91])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X1,X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f149,plain,
    ( spl2_22
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f135,f108,f78,f147])).

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

fof(f135,plain,
    ( ! [X4] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X4) = k4_xboole_0(k2_struct_0(sK0),X4)
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

fof(f121,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f116,f89,f74,f44,f118])).

fof(f44,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f116,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f112,f91])).

fof(f112,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f75,f46])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

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

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(superposition,[],[f46,f91])).

fof(f99,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f93,f89,f38,f96])).

fof(f93,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(superposition,[],[f39,f91])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
