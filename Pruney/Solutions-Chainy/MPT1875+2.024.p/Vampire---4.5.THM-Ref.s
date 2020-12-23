%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 246 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :    8
%              Number of atoms          :  576 ( 996 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f74,f78,f86,f98,f102,f106,f111,f116,f122,f126,f133,f139,f146,f155,f167,f195,f204,f209])).

fof(f209,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f57,f49,f45,f61,f65,f163,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(X1,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f163,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_25
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f45,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f204,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | spl3_33 ),
    inference(subsumption_resolution,[],[f202,f45])).

fof(f202,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | spl3_33 ),
    inference(subsumption_resolution,[],[f201,f53])).

fof(f53,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f201,plain,
    ( ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_11
    | spl3_33 ),
    inference(subsumption_resolution,[],[f197,f57])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_11
    | spl3_33 ),
    inference(resolution,[],[f194,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_11
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tdlat_3(X0)
        | v2_tex_2(u1_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f194,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_33
  <=> v2_tex_2(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f195,plain,
    ( ~ spl3_33
    | ~ spl3_8
    | ~ spl3_19
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f176,f165,f120,f72,f193])).

fof(f72,plain,
    ( spl3_8
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f120,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f165,plain,
    ( spl3_26
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f176,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl3_8
    | ~ spl3_19
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f175,f73])).

fof(f73,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f175,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19
    | ~ spl3_26 ),
    inference(resolution,[],[f166,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f166,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl3_25
    | spl3_26
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f160,f153,f100,f64,f56,f44,f165,f162])).

% (10578)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f100,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f153,plain,
    ( spl3_24
  <=> ! [X1] :
        ( r1_tarski(sK1,u1_struct_0(X1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f160,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f159,f45])).

fof(f159,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f158,f65])).

fof(f158,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f157,f57])).

fof(f157,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(resolution,[],[f154,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(sK2(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | r1_tarski(sK1,u1_struct_0(X1))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl3_24
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f150,f144,f76,f153])).

fof(f76,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( spl3_23
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f150,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,u1_struct_0(X1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(superposition,[],[f77,f145])).

fof(f145,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f146,plain,
    ( spl3_23
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f142,f137,f64,f56,f44,f144])).

fof(f137,plain,
    ( spl3_22
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f142,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f140,f57])).

fof(f140,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(resolution,[],[f138,f65])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl3_22
    | spl3_5
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f135,f131,f64,f60,f137])).

fof(f131,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_5
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f134,f65])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X0) )
    | spl3_5
    | ~ spl3_21 ),
    inference(resolution,[],[f132,f61])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl3_21
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f129,f124,f56,f48,f44,f131])).

fof(f124,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_tex_2(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f127,f57])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(resolution,[],[f125,f49])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_tex_2(X1,X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( spl3_20
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f107,f104,f96,f124])).

fof(f104,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_tex_2(X1,X2) )
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(resolution,[],[f105,f97])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(sK2(X0,X1)) = X1 )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f122,plain,
    ( spl3_19
    | spl3_5
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f118,f114,f64,f60,f120])).

fof(f114,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_5
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f117,f65])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_5
    | ~ spl3_18 ),
    inference(resolution,[],[f115,f61])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f112,f109,f56,f114])).

fof(f109,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X2,X1)
        | ~ v2_tex_2(X1,X0)
        | v2_tex_2(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X1,sK0) )
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(resolution,[],[f110,f57])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(X2,X1)
        | ~ v2_tex_2(X1,X0)
        | v2_tex_2(X2,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f30,f109])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f106,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f37,f104])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

% (10579)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f102,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f31,f96])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f86,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(u1_struct_0(X0),X0) ) ),
    inference(subsumption_resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f28,f27])).

fof(f27,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f39,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(u1_struct_0(X0),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != X1
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(f78,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f76])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f74,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f66,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f62,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10571)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (10565)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10573)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (10573)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f74,f78,f86,f98,f102,f106,f111,f116,f122,f126,f133,f139,f146,f155,f167,f195,f204,f209])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    spl3_1 | ~spl3_2 | ~spl3_4 | spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f207])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_25)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f57,f49,f45,f61,f65,f163,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) ) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl3_14 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~spl3_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    spl3_25 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~v2_tex_2(sK1,sK0) | spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_5 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl3_2 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_11 | spl3_33),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    $false | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_11 | spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f202,f45])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_11 | spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f201,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    v1_tdlat_3(sK0) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl3_3 <=> v1_tdlat_3(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_11 | spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f197,f57])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | (~spl3_11 | spl3_33)),
% 0.22/0.49    inference(resolution,[],[f194,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl3_11 <=> ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK0),sK0) | spl3_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f193])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl3_33 <=> v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ~spl3_33 | ~spl3_8 | ~spl3_19 | ~spl3_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f176,f165,f120,f72,f193])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl3_8 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl3_19 <=> ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl3_26 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK0),sK0) | (~spl3_8 | ~spl3_19 | ~spl3_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f175,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_19 | ~spl3_26)),
% 0.22/0.49    inference(resolution,[],[f166,f121])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f120])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f165])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl3_25 | spl3_26 | spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_15 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f160,f153,f100,f64,f56,f44,f165,f162])).
% 0.22/0.49  % (10578)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl3_15 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    spl3_24 <=> ! [X1] : (r1_tarski(sK1,u1_struct_0(X1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | v1_xboole_0(sK1) | (spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f159,f45])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | v1_xboole_0(sK1) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_6 | ~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f158,f65])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f157,f57])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(resolution,[],[f154,f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | r1_tarski(sK1,u1_struct_0(X1)) | ~l1_pre_topc(X1)) ) | ~spl3_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f153])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl3_24 | ~spl3_9 | ~spl3_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f144,f76,f153])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_9 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl3_23 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(sK1,u1_struct_0(X1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1)) ) | (~spl3_9 | ~spl3_23)),
% 0.22/0.49    inference(superposition,[],[f77,f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl3_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f144])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    spl3_23 | spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f142,f137,f64,f56,f44,f144])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl3_22 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f141,f45])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    sK1 = u1_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_6 | ~spl3_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f140,f57])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_6 | ~spl3_22)),
% 0.22/0.49    inference(resolution,[],[f138,f65])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl3_22 | spl3_5 | ~spl3_6 | ~spl3_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f135,f131,f64,f60,f137])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl3_21 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (spl3_5 | ~spl3_6 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f134,f65])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X0)) ) | (spl3_5 | ~spl3_21)),
% 0.22/0.49    inference(resolution,[],[f132,f61])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X0)) ) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl3_21 | spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f129,f124,f56,f48,f44,f131])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl3_20 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v2_tex_2(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f128,f45])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f57])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | (~spl3_2 | ~spl3_20)),
% 0.22/0.49    inference(resolution,[],[f125,f49])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X2) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v2_tex_2(X1,X2)) ) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f124])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl3_20 | ~spl3_14 | ~spl3_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f107,f104,f96,f124])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl3_16 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v2_tex_2(X1,X2)) ) | (~spl3_14 | ~spl3_16)),
% 0.22/0.49    inference(resolution,[],[f105,f97])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) ) | ~spl3_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl3_19 | spl3_5 | ~spl3_6 | ~spl3_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f118,f114,f64,f60,f120])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_18 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | v2_tex_2(X1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_5 | ~spl3_6 | ~spl3_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f117,f65])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_5 | ~spl3_18)),
% 0.22/0.49    inference(resolution,[],[f115,f61])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl3_18 | ~spl3_4 | ~spl3_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f109,f56,f114])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_17 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~v2_tex_2(X0,sK0) | v2_tex_2(X1,sK0)) ) | (~spl3_4 | ~spl3_17)),
% 0.22/0.49    inference(resolution,[],[f110,f57])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) ) | ~spl3_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f109])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl3_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f109])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl3_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f104])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  % (10579)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f100])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f96])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f84])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f39,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f28,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != X1 | ~v1_tdlat_3(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f76])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f72])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f64])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f60])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ~v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f52])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    v1_tdlat_3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f48])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10573)------------------------------
% 0.22/0.49  % (10573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10573)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10573)Memory used [KB]: 10746
% 0.22/0.49  % (10573)Time elapsed: 0.074 s
% 0.22/0.49  % (10573)------------------------------
% 0.22/0.49  % (10573)------------------------------
% 0.22/0.50  % (10561)Success in time 0.131 s
%------------------------------------------------------------------------------
