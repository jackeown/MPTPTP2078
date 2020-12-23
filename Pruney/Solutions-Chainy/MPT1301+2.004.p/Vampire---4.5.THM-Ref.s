%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 246 expanded)
%              Number of leaves         :   35 ( 114 expanded)
%              Depth                    :    8
%              Number of atoms          :  463 (1053 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f73,f77,f85,f89,f93,f97,f101,f105,f110,f122,f132,f140,f151,f156,f168,f175,f197,f203,f209,f213])).

fof(f213,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_1
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f211,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_1
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f210,f43])).

fof(f43,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_1
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f210,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_27
    | ~ spl4_33 ),
    inference(resolution,[],[f208,f174])).

fof(f174,plain,
    ( r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_27
  <=> r2_hidden(sK3(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK2)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_33
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK2)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f209,plain,
    ( spl4_33
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f205,f201,f71,f66,f207])).

fof(f66,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( v2_tops_2(X1,X0)
        | ~ v4_pre_topc(sK3(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f201,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK2)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f204,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK2)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(resolution,[],[f202,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(sK3(X0,X1),X0)
        | v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f202,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f201])).

fof(f203,plain,
    ( spl4_32
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f199,f195,f56,f46,f201])).

fof(f46,plain,
    ( spl4_2
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f195,plain,
    ( spl4_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f198,f58])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(resolution,[],[f196,f48])).

fof(f48,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl4_31
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f193,f108,f66,f195])).

fof(f108,plain,
    ( spl4_16
  <=> ! [X1,X3,X0] :
        ( v4_pre_topc(X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(resolution,[],[f109,f68])).

fof(f109,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ r2_hidden(X3,X1)
        | ~ v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v4_pre_topc(X3,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f175,plain,
    ( spl4_27
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f169,f165,f95,f172])).

fof(f95,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f165,plain,
    ( spl4_26
  <=> r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f169,plain,
    ( r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl4_13
    | ~ spl4_26 ),
    inference(resolution,[],[f167,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f167,plain,
    ( r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f168,plain,
    ( spl4_26
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f163,f154,f51,f165])).

fof(f51,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f154,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f163,plain,
    ( r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f155,f53])).

fof(f53,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl4_24
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f152,f148,f99,f154])).

fof(f99,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f148,plain,
    ( spl4_23
  <=> sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0) )
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(superposition,[],[f100,f150])).

fof(f150,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f151,plain,
    ( spl4_23
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f142,f137,f120,f148])).

fof(f120,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k2_xboole_0(k1_tarski(X0),X1) = X1
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f137,plain,
    ( spl4_21
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f142,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1)
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(resolution,[],[f139,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k2_xboole_0(k1_tarski(X0),X1) = X1 )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f139,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( spl4_21
    | spl4_1
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f135,f130,f61,f41,f137])).

fof(f130,plain,
    ( spl4_20
  <=> ! [X0] :
        ( r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f135,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | spl4_1
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f134,f43])).

fof(f134,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(resolution,[],[f131,f63])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK3(sK0,X0),X0)
        | v2_tops_2(X0,sK0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f128,f75,f66,f130])).

fof(f75,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( v2_tops_2(X1,X0)
        | r2_hidden(sK3(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f128,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f76,f68])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | r2_hidden(sK3(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f122,plain,
    ( spl4_18
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f113,f91,f87,f120])).

fof(f87,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f91,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) = X1
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f88,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f110,plain,
    ( spl4_16
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f106,f103,f83,f108])).

fof(f83,plain,
    ( spl4_10
  <=> ! [X1,X3,X0] :
        ( v4_pre_topc(X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f103,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f106,plain,
    ( ! [X0,X3,X1] :
        ( v4_pre_topc(X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f84,f104])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f84,plain,
    ( ! [X0,X3,X1] :
        ( v4_pre_topc(X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f105,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f39,f103])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f101,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f38,f99])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f97,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f36,f95])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f93,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f85,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tops_2(sK1,sK0)
    & v2_tops_2(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(X1,X0)
                & v2_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,sK0)
              & v2_tops_2(X2,sK0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(X1,sK0)
            & v2_tops_2(X2,sK0)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(sK1,sK0)
          & v2_tops_2(X2,sK0)
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(sK1,sK0)
        & v2_tops_2(X2,sK0)
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(sK1,sK0)
      & v2_tops_2(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v2_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f41])).

fof(f30,plain,(
    ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (5805)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (5807)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (5810)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (5805)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f214,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f73,f77,f85,f89,f93,f97,f101,f105,f110,f122,f132,f140,f151,f156,f168,f175,f197,f203,f209,f213])).
% 0.21/0.42  fof(f213,plain,(
% 0.21/0.42    spl4_1 | ~spl4_5 | ~spl4_27 | ~spl4_33),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.42  fof(f212,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_5 | ~spl4_27 | ~spl4_33)),
% 0.21/0.42    inference(subsumption_resolution,[],[f211,f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f211,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl4_1 | ~spl4_27 | ~spl4_33)),
% 0.21/0.42    inference(subsumption_resolution,[],[f210,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ~v2_tops_2(sK1,sK0) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl4_1 <=> v2_tops_2(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    v2_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl4_27 | ~spl4_33)),
% 0.21/0.42    inference(resolution,[],[f208,f174])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1),sK2) | ~spl4_27),
% 0.21/0.42    inference(avatar_component_clause,[],[f172])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    spl4_27 <=> r2_hidden(sK3(sK0,sK1),sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.42  fof(f208,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl4_33),
% 0.21/0.42    inference(avatar_component_clause,[],[f207])).
% 0.21/0.42  fof(f207,plain,(
% 0.21/0.42    spl4_33 <=> ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.42  fof(f209,plain,(
% 0.21/0.42    spl4_33 | ~spl4_6 | ~spl4_7 | ~spl4_32),
% 0.21/0.42    inference(avatar_split_clause,[],[f205,f201,f71,f66,f207])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl4_6 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0] : (v2_tops_2(X1,X0) | ~v4_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f201,plain,(
% 0.21/0.42    spl4_32 <=> ! [X0] : (~r2_hidden(X0,sK2) | v4_pre_topc(X0,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.42  fof(f205,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl4_6 | ~spl4_7 | ~spl4_32)),
% 0.21/0.42    inference(subsumption_resolution,[],[f204,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f204,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (~spl4_7 | ~spl4_32)),
% 0.21/0.42    inference(resolution,[],[f202,f72])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f71])).
% 0.21/0.42  fof(f202,plain,(
% 0.21/0.42    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK2)) ) | ~spl4_32),
% 0.21/0.42    inference(avatar_component_clause,[],[f201])).
% 0.21/0.42  fof(f203,plain,(
% 0.21/0.42    spl4_32 | ~spl4_2 | ~spl4_4 | ~spl4_31),
% 0.21/0.42    inference(avatar_split_clause,[],[f199,f195,f56,f46,f201])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl4_2 <=> v2_tops_2(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    spl4_31 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(X0,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.42  fof(f199,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK2) | v4_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_31)),
% 0.21/0.42    inference(subsumption_resolution,[],[f198,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f198,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_31)),
% 0.21/0.42    inference(resolution,[],[f196,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    v2_tops_2(sK2,sK0) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(X0,sK0)) ) | ~spl4_31),
% 0.21/0.42    inference(avatar_component_clause,[],[f195])).
% 0.21/0.42  fof(f197,plain,(
% 0.21/0.42    spl4_31 | ~spl4_6 | ~spl4_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f193,f108,f66,f195])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    spl4_16 <=> ! [X1,X3,X0] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(X0,sK0)) ) | (~spl4_6 | ~spl4_16)),
% 0.21/0.42    inference(resolution,[],[f109,f68])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v4_pre_topc(X3,X0)) ) | ~spl4_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f108])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    spl4_27 | ~spl4_13 | ~spl4_26),
% 0.21/0.42    inference(avatar_split_clause,[],[f169,f165,f95,f172])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl4_13 <=> ! [X1,X0] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f165,plain,(
% 0.21/0.42    spl4_26 <=> r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1),sK2) | (~spl4_13 | ~spl4_26)),
% 0.21/0.42    inference(resolution,[],[f167,f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f95])).
% 0.21/0.42  fof(f167,plain,(
% 0.21/0.42    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) | ~spl4_26),
% 0.21/0.42    inference(avatar_component_clause,[],[f165])).
% 0.21/0.42  fof(f168,plain,(
% 0.21/0.42    spl4_26 | ~spl4_3 | ~spl4_24),
% 0.21/0.42    inference(avatar_split_clause,[],[f163,f154,f51,f165])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f154,plain,(
% 0.21/0.42    spl4_24 <=> ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.42  fof(f163,plain,(
% 0.21/0.42    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) | (~spl4_3 | ~spl4_24)),
% 0.21/0.42    inference(resolution,[],[f155,f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f51])).
% 0.21/0.42  fof(f155,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0)) ) | ~spl4_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f154])).
% 0.21/0.42  fof(f156,plain,(
% 0.21/0.42    spl4_24 | ~spl4_14 | ~spl4_23),
% 0.21/0.42    inference(avatar_split_clause,[],[f152,f148,f99,f154])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl4_14 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    spl4_23 <=> sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK3(sK0,sK1)),X0)) ) | (~spl4_14 | ~spl4_23)),
% 0.21/0.42    inference(superposition,[],[f100,f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1) | ~spl4_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f148])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f99])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    spl4_23 | ~spl4_18 | ~spl4_21),
% 0.21/0.42    inference(avatar_split_clause,[],[f142,f137,f120,f148])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl4_18 <=> ! [X1,X0] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    spl4_21 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    sK1 = k2_xboole_0(k1_tarski(sK3(sK0,sK1)),sK1) | (~spl4_18 | ~spl4_21)),
% 0.21/0.42    inference(resolution,[],[f139,f121])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) ) | ~spl4_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f120])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1),sK1) | ~spl4_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f137])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    spl4_21 | spl4_1 | ~spl4_5 | ~spl4_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f135,f130,f61,f41,f137])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    spl4_20 <=> ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1),sK1) | (spl4_1 | ~spl4_5 | ~spl4_20)),
% 0.21/0.42    inference(subsumption_resolution,[],[f134,f43])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    r2_hidden(sK3(sK0,sK1),sK1) | v2_tops_2(sK1,sK0) | (~spl4_5 | ~spl4_20)),
% 0.21/0.42    inference(resolution,[],[f131,f63])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X0),X0) | v2_tops_2(X0,sK0)) ) | ~spl4_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f130])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl4_20 | ~spl4_6 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f128,f75,f66,f130])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X0] : (v2_tops_2(X1,X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl4_6 | ~spl4_8)),
% 0.21/0.42    inference(resolution,[],[f76,f68])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f75])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    spl4_18 | ~spl4_11 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f113,f91,f87,f120])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl4_12 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) ) | (~spl4_11 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f88,f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f87])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    spl4_16 | ~spl4_10 | ~spl4_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f106,f103,f83,f108])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X3,X0] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl4_15 <=> ! [X1,X0,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | (~spl4_10 | ~spl4_15)),
% 0.21/0.42    inference(subsumption_resolution,[],[f84,f104])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) ) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f103])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f83])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl4_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f39,f103])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl4_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f38,f99])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f95])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f91])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f87])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f83])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(rectify,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f75])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v2_tops_2(X1,X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v2_tops_2(X1,X0) | ~v4_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f66])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ((~v2_tops_2(sK1,sK0) & v2_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(X1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (~v2_tops_2(X1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(sK1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X2] : (~v2_tops_2(sK1,sK0) & v2_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(sK1,sK0) & v2_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(X1,X0) & (v2_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f61])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f51])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r1_tarski(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f46])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    v2_tops_2(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f41])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~v2_tops_2(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (5805)------------------------------
% 0.21/0.43  % (5805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (5805)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (5805)Memory used [KB]: 10618
% 0.21/0.43  % (5805)Time elapsed: 0.016 s
% 0.21/0.43  % (5805)------------------------------
% 0.21/0.43  % (5805)------------------------------
% 0.21/0.43  % (5799)Success in time 0.072 s
%------------------------------------------------------------------------------
