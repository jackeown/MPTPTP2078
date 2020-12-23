%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:19 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 235 expanded)
%              Number of leaves         :   31 (  99 expanded)
%              Depth                    :    7
%              Number of atoms          :  541 ( 918 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f75,f79,f96,f104,f108,f120,f128,f136,f144,f148,f153,f159,f165,f174,f188,f196,f203,f210,f217])).

fof(f217,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f215,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f215,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f214,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f212,f58])).

fof(f58,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f212,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(resolution,[],[f187,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_14
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_struct_0(sK2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f187,plain,
    ( v2_struct_0(sK2(sK0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_31
  <=> v2_struct_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f210,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | spl3_32 ),
    inference(subsumption_resolution,[],[f208,f54])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | spl3_32 ),
    inference(subsumption_resolution,[],[f207,f62])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_19
    | spl3_32 ),
    inference(subsumption_resolution,[],[f205,f58])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_19
    | spl3_32 ),
    inference(resolution,[],[f202,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( m1_pre_topc(sK2(X0),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_19
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | m1_pre_topc(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f202,plain,
    ( ~ m1_pre_topc(sK2(sK0),sK0)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_32
  <=> m1_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f203,plain,
    ( ~ spl3_32
    | ~ spl3_4
    | ~ spl3_21
    | spl3_30 ),
    inference(avatar_split_clause,[],[f199,f183,f134,f61,f201])).

fof(f134,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f183,plain,
    ( spl3_30
  <=> m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f199,plain,
    ( ~ m1_pre_topc(sK2(sK0),sK0)
    | ~ spl3_4
    | ~ spl3_21
    | spl3_30 ),
    inference(subsumption_resolution,[],[f197,f62])).

fof(f197,plain,
    ( ~ m1_pre_topc(sK2(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21
    | spl3_30 ),
    inference(resolution,[],[f184,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f184,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f183])).

fof(f196,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_17
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_17
    | spl3_29 ),
    inference(subsumption_resolution,[],[f194,f54])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_17
    | spl3_29 ),
    inference(subsumption_resolution,[],[f193,f62])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_17
    | spl3_29 ),
    inference(subsumption_resolution,[],[f190,f58])).

fof(f190,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_17
    | spl3_29 ),
    inference(resolution,[],[f181,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( v1_tdlat_3(sK2(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_17
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v1_tdlat_3(sK2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f181,plain,
    ( ~ v1_tdlat_3(sK2(sK0))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_29
  <=> v1_tdlat_3(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f188,plain,
    ( ~ spl3_29
    | ~ spl3_30
    | spl3_31
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f178,f172,f126,f61,f57,f53,f186,f183,f180])).

fof(f172,plain,
    ( spl3_28
  <=> ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f178,plain,
    ( v2_struct_0(sK2(sK0))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK2(sK0))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f177,plain,
    ( v2_struct_0(sK2(sK0))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK2(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f176,plain,
    ( v2_struct_0(sK2(sK0))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK2(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f175,f58])).

fof(f175,plain,
    ( v2_struct_0(sK2(sK0))
    | ~ m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK2(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(resolution,[],[f173,f127])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl3_28
    | spl3_2
    | ~ spl3_4
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f170,f163,f142,f61,f53,f172])).

fof(f142,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tdlat_3(X1)
        | v2_tex_2(u1_struct_0(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f163,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0) )
    | spl3_2
    | ~ spl3_4
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f169,f54])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(sK0) )
    | ~ spl3_4
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f166,f62])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(sK0) )
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(resolution,[],[f164,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(u1_struct_0(X1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tdlat_3(X1)
        | v2_struct_0(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f142])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl3_27
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f161,f157,f102,f73,f163])).

fof(f73,plain,
    ( spl3_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f102,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f157,plain,
    ( spl3_26
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f160,f74])).

fof(f74,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(resolution,[],[f158,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl3_26
    | ~ spl3_7
    | spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f155,f151,f94,f73,f157])).

fof(f94,plain,
    ( spl3_11
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f151,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_7
    | spl3_11
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f154,f74])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_xboole_0,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_11
    | ~ spl3_25 ),
    inference(resolution,[],[f152,f95])).

fof(f95,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl3_25
    | ~ spl3_4
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f149,f146,f61,f151])).

fof(f146,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X2,X1)
        | ~ v2_tex_2(X1,X0)
        | v2_tex_2(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X1,sK0) )
    | ~ spl3_4
    | ~ spl3_24 ),
    inference(resolution,[],[f147,f62])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X2,X1)
        | ~ v2_tex_2(X1,X0)
        | v2_tex_2(X2,X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f32,f146])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f144,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f47,f142])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(subsumption_resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f136,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f31,f134])).

fof(f128,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f35,f126])).

fof(f35,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc11_tex_2)).

fof(f120,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f39,f118])).

fof(f39,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f36,f106])).

fof(f36,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_struct_0(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f42,f102])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f82,f77,f65,f49,f94])).

fof(f49,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( spl3_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl3_1
    | spl3_5
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f66,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f66,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f79,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f67,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_vampire %s %d
% 0.09/0.29  % Computer   : n021.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 11:31:49 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.15/0.40  % (18191)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.15/0.41  % (18199)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.15/0.41  % (18193)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.15/0.41  % (18199)Refutation found. Thanks to Tanya!
% 0.15/0.41  % SZS status Theorem for theBenchmark
% 0.15/0.41  % SZS output start Proof for theBenchmark
% 0.15/0.41  fof(f218,plain,(
% 0.15/0.41    $false),
% 0.15/0.41    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f75,f79,f96,f104,f108,f120,f128,f136,f144,f148,f153,f159,f165,f174,f188,f196,f203,f210,f217])).
% 0.15/0.41  fof(f217,plain,(
% 0.15/0.41    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_14 | ~spl3_31),
% 0.15/0.41    inference(avatar_contradiction_clause,[],[f216])).
% 0.15/0.41  fof(f216,plain,(
% 0.15/0.41    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_14 | ~spl3_31)),
% 0.15/0.41    inference(subsumption_resolution,[],[f215,f54])).
% 0.15/0.41  fof(f54,plain,(
% 0.15/0.41    ~v2_struct_0(sK0) | spl3_2),
% 0.15/0.41    inference(avatar_component_clause,[],[f53])).
% 0.15/0.41  fof(f53,plain,(
% 0.15/0.41    spl3_2 <=> v2_struct_0(sK0)),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.15/0.41  fof(f215,plain,(
% 0.15/0.41    v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_14 | ~spl3_31)),
% 0.15/0.41    inference(subsumption_resolution,[],[f214,f62])).
% 0.15/0.41  fof(f62,plain,(
% 0.15/0.41    l1_pre_topc(sK0) | ~spl3_4),
% 0.15/0.41    inference(avatar_component_clause,[],[f61])).
% 0.15/0.41  fof(f61,plain,(
% 0.15/0.41    spl3_4 <=> l1_pre_topc(sK0)),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.15/0.41  fof(f214,plain,(
% 0.15/0.41    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_14 | ~spl3_31)),
% 0.15/0.41    inference(subsumption_resolution,[],[f212,f58])).
% 0.15/0.41  fof(f58,plain,(
% 0.15/0.41    v2_pre_topc(sK0) | ~spl3_3),
% 0.15/0.41    inference(avatar_component_clause,[],[f57])).
% 0.15/0.41  fof(f57,plain,(
% 0.15/0.41    spl3_3 <=> v2_pre_topc(sK0)),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.15/0.41  fof(f212,plain,(
% 0.15/0.41    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_14 | ~spl3_31)),
% 0.15/0.41    inference(resolution,[],[f187,f107])).
% 0.15/0.41  fof(f107,plain,(
% 0.15/0.41    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_14),
% 0.15/0.41    inference(avatar_component_clause,[],[f106])).
% 0.15/0.41  fof(f106,plain,(
% 0.15/0.41    spl3_14 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_struct_0(sK2(X0)))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.15/0.41  fof(f187,plain,(
% 0.15/0.41    v2_struct_0(sK2(sK0)) | ~spl3_31),
% 0.15/0.41    inference(avatar_component_clause,[],[f186])).
% 0.15/0.41  fof(f186,plain,(
% 0.15/0.41    spl3_31 <=> v2_struct_0(sK2(sK0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.15/0.41  fof(f210,plain,(
% 0.15/0.41    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_19 | spl3_32),
% 0.15/0.41    inference(avatar_contradiction_clause,[],[f209])).
% 0.15/0.41  fof(f209,plain,(
% 0.15/0.41    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_19 | spl3_32)),
% 0.15/0.41    inference(subsumption_resolution,[],[f208,f54])).
% 0.15/0.41  fof(f208,plain,(
% 0.15/0.41    v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_19 | spl3_32)),
% 0.15/0.41    inference(subsumption_resolution,[],[f207,f62])).
% 0.15/0.41  fof(f207,plain,(
% 0.15/0.41    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_19 | spl3_32)),
% 0.15/0.41    inference(subsumption_resolution,[],[f205,f58])).
% 0.15/0.41  fof(f205,plain,(
% 0.15/0.41    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_19 | spl3_32)),
% 0.15/0.41    inference(resolution,[],[f202,f127])).
% 0.15/0.41  fof(f127,plain,(
% 0.15/0.41    ( ! [X0] : (m1_pre_topc(sK2(X0),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_19),
% 0.15/0.41    inference(avatar_component_clause,[],[f126])).
% 0.15/0.41  fof(f126,plain,(
% 0.15/0.41    spl3_19 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_pre_topc(sK2(X0),X0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.15/0.41  fof(f202,plain,(
% 0.15/0.41    ~m1_pre_topc(sK2(sK0),sK0) | spl3_32),
% 0.15/0.41    inference(avatar_component_clause,[],[f201])).
% 0.15/0.41  fof(f201,plain,(
% 0.15/0.41    spl3_32 <=> m1_pre_topc(sK2(sK0),sK0)),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.15/0.41  fof(f203,plain,(
% 0.15/0.41    ~spl3_32 | ~spl3_4 | ~spl3_21 | spl3_30),
% 0.15/0.41    inference(avatar_split_clause,[],[f199,f183,f134,f61,f201])).
% 0.15/0.41  fof(f134,plain,(
% 0.15/0.41    spl3_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.15/0.41  fof(f183,plain,(
% 0.15/0.41    spl3_30 <=> m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.15/0.41  fof(f199,plain,(
% 0.15/0.41    ~m1_pre_topc(sK2(sK0),sK0) | (~spl3_4 | ~spl3_21 | spl3_30)),
% 0.15/0.41    inference(subsumption_resolution,[],[f197,f62])).
% 0.15/0.41  fof(f197,plain,(
% 0.15/0.41    ~m1_pre_topc(sK2(sK0),sK0) | ~l1_pre_topc(sK0) | (~spl3_21 | spl3_30)),
% 0.15/0.41    inference(resolution,[],[f184,f135])).
% 0.15/0.41  fof(f135,plain,(
% 0.15/0.41    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_21),
% 0.15/0.41    inference(avatar_component_clause,[],[f134])).
% 0.15/0.41  fof(f184,plain,(
% 0.15/0.41    ~m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_30),
% 0.15/0.41    inference(avatar_component_clause,[],[f183])).
% 0.15/0.41  fof(f196,plain,(
% 0.15/0.41    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_17 | spl3_29),
% 0.15/0.41    inference(avatar_contradiction_clause,[],[f195])).
% 0.15/0.41  fof(f195,plain,(
% 0.15/0.41    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_17 | spl3_29)),
% 0.15/0.41    inference(subsumption_resolution,[],[f194,f54])).
% 0.15/0.41  fof(f194,plain,(
% 0.15/0.41    v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_17 | spl3_29)),
% 0.15/0.41    inference(subsumption_resolution,[],[f193,f62])).
% 0.15/0.41  fof(f193,plain,(
% 0.15/0.41    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_17 | spl3_29)),
% 0.15/0.41    inference(subsumption_resolution,[],[f190,f58])).
% 0.15/0.41  fof(f190,plain,(
% 0.15/0.41    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_17 | spl3_29)),
% 0.15/0.41    inference(resolution,[],[f181,f119])).
% 0.15/0.41  fof(f119,plain,(
% 0.15/0.41    ( ! [X0] : (v1_tdlat_3(sK2(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_17),
% 0.15/0.41    inference(avatar_component_clause,[],[f118])).
% 0.15/0.41  fof(f118,plain,(
% 0.15/0.41    spl3_17 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_tdlat_3(sK2(X0)))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.15/0.41  fof(f181,plain,(
% 0.15/0.41    ~v1_tdlat_3(sK2(sK0)) | spl3_29),
% 0.15/0.41    inference(avatar_component_clause,[],[f180])).
% 0.15/0.41  fof(f180,plain,(
% 0.15/0.41    spl3_29 <=> v1_tdlat_3(sK2(sK0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.15/0.41  fof(f188,plain,(
% 0.15/0.41    ~spl3_29 | ~spl3_30 | spl3_31 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_19 | ~spl3_28),
% 0.15/0.41    inference(avatar_split_clause,[],[f178,f172,f126,f61,f57,f53,f186,f183,f180])).
% 0.15/0.41  fof(f172,plain,(
% 0.15/0.41    spl3_28 <=> ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.15/0.41  fof(f178,plain,(
% 0.15/0.41    v2_struct_0(sK2(sK0)) | ~m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK2(sK0)) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_19 | ~spl3_28)),
% 0.15/0.41    inference(subsumption_resolution,[],[f177,f54])).
% 0.15/0.41  fof(f177,plain,(
% 0.15/0.41    v2_struct_0(sK2(sK0)) | ~m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK2(sK0)) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_19 | ~spl3_28)),
% 0.15/0.41    inference(subsumption_resolution,[],[f176,f62])).
% 0.15/0.41  fof(f176,plain,(
% 0.15/0.41    v2_struct_0(sK2(sK0)) | ~m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK2(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_19 | ~spl3_28)),
% 0.15/0.41    inference(subsumption_resolution,[],[f175,f58])).
% 0.15/0.41  fof(f175,plain,(
% 0.15/0.41    v2_struct_0(sK2(sK0)) | ~m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK2(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_19 | ~spl3_28)),
% 0.15/0.41    inference(resolution,[],[f173,f127])).
% 0.15/0.41  fof(f173,plain,(
% 0.15/0.41    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(X0)) ) | ~spl3_28),
% 0.15/0.41    inference(avatar_component_clause,[],[f172])).
% 0.15/0.41  fof(f174,plain,(
% 0.15/0.41    spl3_28 | spl3_2 | ~spl3_4 | ~spl3_23 | ~spl3_27),
% 0.15/0.41    inference(avatar_split_clause,[],[f170,f163,f142,f61,f53,f172])).
% 0.15/0.41  fof(f142,plain,(
% 0.15/0.41    spl3_23 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.15/0.41  fof(f163,plain,(
% 0.15/0.41    spl3_27 <=> ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.15/0.41  fof(f170,plain,(
% 0.15/0.41    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0)) ) | (spl3_2 | ~spl3_4 | ~spl3_23 | ~spl3_27)),
% 0.15/0.41    inference(subsumption_resolution,[],[f169,f54])).
% 0.15/0.41  fof(f169,plain,(
% 0.15/0.41    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(sK0)) ) | (~spl3_4 | ~spl3_23 | ~spl3_27)),
% 0.15/0.41    inference(subsumption_resolution,[],[f166,f62])).
% 0.15/0.41  fof(f166,plain,(
% 0.15/0.41    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(sK0)) ) | (~spl3_23 | ~spl3_27)),
% 0.15/0.41    inference(resolution,[],[f164,f143])).
% 0.15/0.41  fof(f143,plain,(
% 0.15/0.41    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X0)) ) | ~spl3_23),
% 0.15/0.41    inference(avatar_component_clause,[],[f142])).
% 0.15/0.41  fof(f164,plain,(
% 0.15/0.41    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_27),
% 0.15/0.41    inference(avatar_component_clause,[],[f163])).
% 0.15/0.41  fof(f165,plain,(
% 0.15/0.41    spl3_27 | ~spl3_7 | ~spl3_13 | ~spl3_26),
% 0.15/0.41    inference(avatar_split_clause,[],[f161,f157,f102,f73,f163])).
% 0.15/0.41  fof(f73,plain,(
% 0.15/0.41    spl3_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.15/0.41  fof(f102,plain,(
% 0.15/0.41    spl3_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.15/0.41  fof(f157,plain,(
% 0.15/0.41    spl3_26 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.15/0.41  fof(f161,plain,(
% 0.15/0.41    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_7 | ~spl3_13 | ~spl3_26)),
% 0.15/0.41    inference(subsumption_resolution,[],[f160,f74])).
% 0.15/0.41  fof(f74,plain,(
% 0.15/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.15/0.41    inference(avatar_component_clause,[],[f73])).
% 0.15/0.41  fof(f160,plain,(
% 0.15/0.41    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl3_13 | ~spl3_26)),
% 0.15/0.41    inference(resolution,[],[f158,f103])).
% 0.15/0.41  fof(f103,plain,(
% 0.15/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_13),
% 0.15/0.41    inference(avatar_component_clause,[],[f102])).
% 0.15/0.41  fof(f158,plain,(
% 0.15/0.41    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_26),
% 0.15/0.41    inference(avatar_component_clause,[],[f157])).
% 0.15/0.41  fof(f159,plain,(
% 0.15/0.41    spl3_26 | ~spl3_7 | spl3_11 | ~spl3_25),
% 0.15/0.41    inference(avatar_split_clause,[],[f155,f151,f94,f73,f157])).
% 0.15/0.41  fof(f94,plain,(
% 0.15/0.41    spl3_11 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.15/0.41  fof(f151,plain,(
% 0.15/0.41    spl3_25 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | v2_tex_2(X1,sK0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.15/0.41  fof(f155,plain,(
% 0.15/0.41    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_7 | spl3_11 | ~spl3_25)),
% 0.15/0.41    inference(subsumption_resolution,[],[f154,f74])).
% 0.15/0.41  fof(f154,plain,(
% 0.15/0.41    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_11 | ~spl3_25)),
% 0.15/0.41    inference(resolution,[],[f152,f95])).
% 0.15/0.41  fof(f95,plain,(
% 0.15/0.41    ~v2_tex_2(k1_xboole_0,sK0) | spl3_11),
% 0.15/0.41    inference(avatar_component_clause,[],[f94])).
% 0.15/0.41  fof(f152,plain,(
% 0.15/0.41    ( ! [X0,X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_25),
% 0.15/0.41    inference(avatar_component_clause,[],[f151])).
% 0.15/0.41  fof(f153,plain,(
% 0.15/0.41    spl3_25 | ~spl3_4 | ~spl3_24),
% 0.15/0.41    inference(avatar_split_clause,[],[f149,f146,f61,f151])).
% 0.15/0.41  fof(f146,plain,(
% 0.15/0.41    spl3_24 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0))),
% 0.15/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.15/0.41  fof(f149,plain,(
% 0.15/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | v2_tex_2(X1,sK0)) ) | (~spl3_4 | ~spl3_24)),
% 0.15/0.41    inference(resolution,[],[f147,f62])).
% 0.15/0.41  fof(f147,plain,(
% 0.15/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) ) | ~spl3_24),
% 0.15/0.41    inference(avatar_component_clause,[],[f146])).
% 0.15/0.41  fof(f148,plain,(
% 0.15/0.41    spl3_24),
% 0.15/0.41    inference(avatar_split_clause,[],[f32,f146])).
% 0.15/0.41  fof(f32,plain,(
% 0.15/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 0.15/0.41    inference(cnf_transformation,[],[f16])).
% 0.15/0.42  fof(f16,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.15/0.42    inference(flattening,[],[f15])).
% 0.15/0.42  fof(f15,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.15/0.42    inference(ennf_transformation,[],[f8])).
% 0.15/0.42  fof(f8,axiom,(
% 0.15/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.15/0.42  fof(f144,plain,(
% 0.15/0.42    spl3_23),
% 0.15/0.42    inference(avatar_split_clause,[],[f47,f142])).
% 0.15/0.42  fof(f47,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.15/0.42    inference(subsumption_resolution,[],[f45,f31])).
% 0.15/0.42  fof(f31,plain,(
% 0.15/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f14])).
% 0.15/0.42  fof(f14,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.15/0.42    inference(ennf_transformation,[],[f5])).
% 0.15/0.42  fof(f5,axiom,(
% 0.15/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).
% 0.15/0.42  fof(f45,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.15/0.42    inference(equality_resolution,[],[f33])).
% 0.15/0.42  fof(f33,plain,(
% 0.15/0.42    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f18])).
% 0.15/0.42  fof(f18,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.15/0.42    inference(flattening,[],[f17])).
% 0.15/0.42  fof(f17,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.15/0.42    inference(ennf_transformation,[],[f7])).
% 0.15/0.42  fof(f7,axiom,(
% 0.15/0.42    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.15/0.42  fof(f136,plain,(
% 0.15/0.42    spl3_21),
% 0.15/0.42    inference(avatar_split_clause,[],[f31,f134])).
% 0.15/0.42  fof(f128,plain,(
% 0.15/0.42    spl3_19),
% 0.15/0.42    inference(avatar_split_clause,[],[f35,f126])).
% 0.15/0.42  fof(f35,plain,(
% 0.15/0.42    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_pre_topc(sK2(X0),X0)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f20])).
% 0.15/0.42  fof(f20,plain,(
% 0.15/0.42    ! [X0] : (? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.15/0.42    inference(flattening,[],[f19])).
% 0.15/0.42  fof(f19,plain,(
% 0.15/0.42    ! [X0] : (? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.15/0.42    inference(ennf_transformation,[],[f6])).
% 0.15/0.42  fof(f6,axiom,(
% 0.15/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc11_tex_2)).
% 0.15/0.42  fof(f120,plain,(
% 0.15/0.42    spl3_17),
% 0.15/0.42    inference(avatar_split_clause,[],[f39,f118])).
% 0.15/0.42  fof(f39,plain,(
% 0.15/0.42    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_tdlat_3(sK2(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f20])).
% 0.15/0.42  fof(f108,plain,(
% 0.15/0.42    spl3_14),
% 0.15/0.42    inference(avatar_split_clause,[],[f36,f106])).
% 0.15/0.42  fof(f36,plain,(
% 0.15/0.42    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_struct_0(sK2(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f20])).
% 0.15/0.42  fof(f104,plain,(
% 0.15/0.42    spl3_13),
% 0.15/0.42    inference(avatar_split_clause,[],[f42,f102])).
% 0.15/0.42  fof(f42,plain,(
% 0.15/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f3])).
% 0.15/0.42  fof(f3,axiom,(
% 0.15/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.15/0.42  fof(f96,plain,(
% 0.15/0.42    ~spl3_11 | ~spl3_1 | spl3_5 | ~spl3_8),
% 0.15/0.42    inference(avatar_split_clause,[],[f82,f77,f65,f49,f94])).
% 0.15/0.42  fof(f49,plain,(
% 0.15/0.42    spl3_1 <=> v1_xboole_0(sK1)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.15/0.42  fof(f65,plain,(
% 0.15/0.42    spl3_5 <=> v2_tex_2(sK1,sK0)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.15/0.42  fof(f77,plain,(
% 0.15/0.42    spl3_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.15/0.42  fof(f82,plain,(
% 0.15/0.42    ~v2_tex_2(k1_xboole_0,sK0) | (~spl3_1 | spl3_5 | ~spl3_8)),
% 0.15/0.42    inference(backward_demodulation,[],[f66,f80])).
% 0.15/0.42  fof(f80,plain,(
% 0.15/0.42    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_8)),
% 0.15/0.42    inference(resolution,[],[f78,f50])).
% 0.15/0.42  fof(f50,plain,(
% 0.15/0.42    v1_xboole_0(sK1) | ~spl3_1),
% 0.15/0.42    inference(avatar_component_clause,[],[f49])).
% 0.15/0.42  fof(f78,plain,(
% 0.15/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.15/0.42    inference(avatar_component_clause,[],[f77])).
% 0.15/0.42  fof(f66,plain,(
% 0.15/0.42    ~v2_tex_2(sK1,sK0) | spl3_5),
% 0.15/0.42    inference(avatar_component_clause,[],[f65])).
% 0.15/0.42  fof(f79,plain,(
% 0.15/0.42    spl3_8),
% 0.15/0.42    inference(avatar_split_clause,[],[f30,f77])).
% 0.15/0.42  fof(f30,plain,(
% 0.15/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.15/0.42    inference(cnf_transformation,[],[f13])).
% 0.15/0.42  fof(f13,plain,(
% 0.15/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.15/0.42    inference(ennf_transformation,[],[f1])).
% 0.15/0.42  fof(f1,axiom,(
% 0.15/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.15/0.42  fof(f75,plain,(
% 0.15/0.42    spl3_7),
% 0.15/0.42    inference(avatar_split_clause,[],[f29,f73])).
% 0.15/0.42  fof(f29,plain,(
% 0.15/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f2])).
% 0.15/0.42  fof(f2,axiom,(
% 0.15/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.15/0.42  fof(f67,plain,(
% 0.15/0.42    ~spl3_5),
% 0.15/0.42    inference(avatar_split_clause,[],[f25,f65])).
% 0.15/0.42  fof(f25,plain,(
% 0.15/0.42    ~v2_tex_2(sK1,sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f12,plain,(
% 0.15/0.42    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.15/0.42    inference(flattening,[],[f11])).
% 0.15/0.42  fof(f11,plain,(
% 0.15/0.42    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.15/0.42    inference(ennf_transformation,[],[f10])).
% 0.15/0.42  fof(f10,negated_conjecture,(
% 0.15/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.15/0.42    inference(negated_conjecture,[],[f9])).
% 0.15/0.42  fof(f9,conjecture,(
% 0.15/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.15/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.15/0.42  fof(f63,plain,(
% 0.15/0.42    spl3_4),
% 0.15/0.42    inference(avatar_split_clause,[],[f28,f61])).
% 0.15/0.42  fof(f28,plain,(
% 0.15/0.42    l1_pre_topc(sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f59,plain,(
% 0.15/0.42    spl3_3),
% 0.15/0.42    inference(avatar_split_clause,[],[f27,f57])).
% 0.15/0.42  fof(f27,plain,(
% 0.15/0.42    v2_pre_topc(sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f55,plain,(
% 0.15/0.42    ~spl3_2),
% 0.15/0.42    inference(avatar_split_clause,[],[f26,f53])).
% 0.15/0.42  fof(f26,plain,(
% 0.15/0.42    ~v2_struct_0(sK0)),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f51,plain,(
% 0.15/0.42    spl3_1),
% 0.15/0.42    inference(avatar_split_clause,[],[f23,f49])).
% 0.15/0.42  fof(f23,plain,(
% 0.15/0.42    v1_xboole_0(sK1)),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  % SZS output end Proof for theBenchmark
% 0.15/0.42  % (18199)------------------------------
% 0.15/0.42  % (18199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.42  % (18199)Termination reason: Refutation
% 0.15/0.42  
% 0.15/0.42  % (18199)Memory used [KB]: 10618
% 0.15/0.42  % (18199)Time elapsed: 0.041 s
% 0.15/0.42  % (18199)------------------------------
% 0.15/0.42  % (18199)------------------------------
% 0.15/0.42  % (18189)Success in time 0.116 s
%------------------------------------------------------------------------------
