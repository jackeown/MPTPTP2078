%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 384 expanded)
%              Number of leaves         :   47 ( 187 expanded)
%              Depth                    :   10
%              Number of atoms          :  725 (2704 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f489,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f88,f93,f97,f101,f107,f112,f116,f121,f125,f130,f135,f140,f148,f154,f162,f189,f200,f208,f217,f257,f286,f297,f309,f379,f397,f408,f413,f419,f421,f466,f480,f488])).

fof(f488,plain,
    ( ~ spl4_21
    | ~ spl4_56
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f483,f477,f395,f159])).

fof(f159,plain,
    ( spl4_21
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f395,plain,
    ( spl4_56
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f477,plain,
    ( spl4_66
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f483,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl4_56
    | ~ spl4_66 ),
    inference(resolution,[],[f479,f396])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f395])).

fof(f479,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f477])).

fof(f480,plain,
    ( spl4_66
    | ~ spl4_10
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f471,f463,f99,f477])).

fof(f99,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f463,plain,
    ( spl4_64
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f471,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl4_10
    | ~ spl4_64 ),
    inference(resolution,[],[f465,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f465,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f463])).

fof(f466,plain,
    ( ~ spl4_5
    | spl4_64
    | ~ spl4_8
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f446,f406,f90,f463,f76])).

fof(f76,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f90,plain,
    ( spl4_8
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f406,plain,
    ( spl4_58
  <=> ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r1_tarski(sK3,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f446,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8
    | ~ spl4_58 ),
    inference(resolution,[],[f407,f92])).

fof(f92,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r1_tarski(sK3,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f406])).

fof(f421,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_17
    | spl4_60 ),
    inference(avatar_split_clause,[],[f420,f416,f133,f76,f66,f61])).

fof(f61,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f133,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f416,plain,
    ( spl4_60
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f420,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_17
    | spl4_60 ),
    inference(resolution,[],[f418,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f418,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f416])).

fof(f419,plain,
    ( ~ spl4_18
    | ~ spl4_60
    | ~ spl4_26
    | ~ spl4_20
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f414,f376,f152,f186,f416,f137])).

fof(f137,plain,
    ( spl4_18
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f186,plain,
    ( spl4_26
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f152,plain,
    ( spl4_20
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f376,plain,
    ( spl4_54
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f414,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_20
    | ~ spl4_54 ),
    inference(resolution,[],[f377,f153])).

fof(f153,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f377,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f376])).

fof(f413,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_45
    | spl4_54 ),
    inference(avatar_split_clause,[],[f380,f376,f307,f81,f76])).

fof(f81,plain,
    ( spl4_6
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f307,plain,
    ( spl4_45
  <=> ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f380,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_45
    | spl4_54 ),
    inference(resolution,[],[f378,f308])).

fof(f308,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f307])).

fof(f378,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f376])).

fof(f408,plain,
    ( ~ spl4_37
    | spl4_58
    | ~ spl4_7
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f288,f284,f85,f406,f254])).

fof(f254,plain,
    ( spl4_37
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f85,plain,
    ( spl4_7
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f284,plain,
    ( spl4_41
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK3,k1_tops_1(sK0,X0)) )
    | ~ spl4_7
    | ~ spl4_41 ),
    inference(resolution,[],[f285,f87])).

fof(f87,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_tops_1(sK0,X1)) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f284])).

fof(f397,plain,
    ( spl4_56
    | ~ spl4_13
    | spl4_54 ),
    inference(avatar_split_clause,[],[f381,f376,f114,f395])).

fof(f114,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f381,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) )
    | ~ spl4_13
    | spl4_54 ),
    inference(resolution,[],[f378,f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f379,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_54
    | spl4_6
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f369,f215,f81,f376,f76,f71,f66,f61,f56])).

fof(f56,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f215,plain,
    ( spl4_32
  <=> ! [X1,X0,X2] :
        ( m1_connsp_2(X2,X0,X1)
        | ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f369,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_6
    | ~ spl4_32 ),
    inference(resolution,[],[f82,f216])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( m1_connsp_2(X2,X0,X1)
        | ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f215])).

fof(f82,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f309,plain,
    ( spl4_45
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f300,f295,f71,f307])).

fof(f295,plain,
    ( spl4_43
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f300,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(resolution,[],[f296,f73])).

fof(f73,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_43
    | spl4_1
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f228,f206,f56,f295,f66,f61])).

fof(f206,plain,
    ( spl4_30
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | spl4_1
    | ~ spl4_30 ),
    inference(resolution,[],[f207,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | r2_hidden(X1,k1_tops_1(X0,X2)) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f286,plain,
    ( spl4_41
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f222,f198,f66,f284])).

fof(f198,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_tops_1(sK0,X1)) )
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(resolution,[],[f199,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ r1_tarski(X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(X1,k1_tops_1(X0,X2)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f257,plain,
    ( spl4_6
    | spl4_37 ),
    inference(avatar_split_clause,[],[f40,f254,f81])).

fof(f40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ m1_connsp_2(X2,sK0,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | m1_connsp_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(sK1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ m1_connsp_2(X2,sK0,sK1) )
          & ( ? [X4] :
                ( r2_hidden(sK1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | m1_connsp_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ m1_connsp_2(X2,sK0,sK1) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | m1_connsp_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | m1_connsp_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f217,plain,(
    spl4_32 ),
    inference(avatar_split_clause,[],[f48,f215])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f208,plain,(
    spl4_30 ),
    inference(avatar_split_clause,[],[f47,f206])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f200,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f46,f198])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f189,plain,
    ( spl4_26
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f150,f145,f99,f186])).

fof(f145,plain,
    ( spl4_19
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f150,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(resolution,[],[f147,f100])).

fof(f147,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f162,plain,
    ( spl4_6
    | spl4_21 ),
    inference(avatar_split_clause,[],[f43,f159,f81])).

fof(f43,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f154,plain,
    ( ~ spl4_6
    | spl4_20 ),
    inference(avatar_split_clause,[],[f44,f152,f81])).

fof(f44,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f148,plain,
    ( spl4_19
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f141,f137,f119,f145])).

fof(f119,plain,
    ( spl4_14
  <=> ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f141,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(resolution,[],[f139,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f139,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f131,f128,f76,f137])).

fof(f128,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f131,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(resolution,[],[f129,f78])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f51,f133])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f130,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f126,f123,f66,f128])).

fof(f123,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f124,f68])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f121,plain,
    ( spl4_14
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f117,f110,f104,f119])).

fof(f104,plain,
    ( spl4_11
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f110,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f117,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f111,f106])).

fof(f106,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f112,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f107,plain,
    ( spl4_11
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f102,f95,f76,f104])).

fof(f95,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f102,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f96,f78])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f101,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,
    ( spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f42,f90,f81])).

fof(f42,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f41,f85,f81])).

fof(f41,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f56])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (12057)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.19/0.47  % (12057)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (12049)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f489,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f88,f93,f97,f101,f107,f112,f116,f121,f125,f130,f135,f140,f148,f154,f162,f189,f200,f208,f217,f257,f286,f297,f309,f379,f397,f408,f413,f419,f421,f466,f480,f488])).
% 0.19/0.48  fof(f488,plain,(
% 0.19/0.48    ~spl4_21 | ~spl4_56 | ~spl4_66),
% 0.19/0.48    inference(avatar_split_clause,[],[f483,f477,f395,f159])).
% 0.19/0.48  fof(f159,plain,(
% 0.19/0.48    spl4_21 <=> r2_hidden(sK1,sK3)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.48  fof(f395,plain,(
% 0.19/0.48    spl4_56 <=> ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.19/0.48  fof(f477,plain,(
% 0.19/0.48    spl4_66 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.19/0.48  fof(f483,plain,(
% 0.19/0.48    ~r2_hidden(sK1,sK3) | (~spl4_56 | ~spl4_66)),
% 0.19/0.48    inference(resolution,[],[f479,f396])).
% 0.19/0.48  fof(f396,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(sK1,X0)) ) | ~spl4_56),
% 0.19/0.48    inference(avatar_component_clause,[],[f395])).
% 0.19/0.48  fof(f479,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~spl4_66),
% 0.19/0.48    inference(avatar_component_clause,[],[f477])).
% 0.19/0.48  fof(f480,plain,(
% 0.19/0.48    spl4_66 | ~spl4_10 | ~spl4_64),
% 0.19/0.48    inference(avatar_split_clause,[],[f471,f463,f99,f477])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    spl4_10 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.48  fof(f463,plain,(
% 0.19/0.48    spl4_64 <=> r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.19/0.48  fof(f471,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | (~spl4_10 | ~spl4_64)),
% 0.19/0.48    inference(resolution,[],[f465,f100])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f99])).
% 0.19/0.48  fof(f465,plain,(
% 0.19/0.48    r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~spl4_64),
% 0.19/0.48    inference(avatar_component_clause,[],[f463])).
% 0.19/0.48  fof(f466,plain,(
% 0.19/0.48    ~spl4_5 | spl4_64 | ~spl4_8 | ~spl4_58),
% 0.19/0.48    inference(avatar_split_clause,[],[f446,f406,f90,f463,f76])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.48  fof(f90,plain,(
% 0.19/0.48    spl4_8 <=> r1_tarski(sK3,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.48  fof(f406,plain,(
% 0.19/0.48    spl4_58 <=> ! [X0] : (~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.19/0.48  fof(f446,plain,(
% 0.19/0.48    r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_8 | ~spl4_58)),
% 0.19/0.48    inference(resolution,[],[f407,f92])).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    r1_tarski(sK3,sK2) | ~spl4_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f90])).
% 0.19/0.48  fof(f407,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_58),
% 0.19/0.48    inference(avatar_component_clause,[],[f406])).
% 0.19/0.48  fof(f421,plain,(
% 0.19/0.48    ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_17 | spl4_60),
% 0.19/0.48    inference(avatar_split_clause,[],[f420,f416,f133,f76,f66,f61])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    spl4_2 <=> v2_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    spl4_3 <=> l1_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    spl4_17 <=> ! [X1,X0] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.48  fof(f416,plain,(
% 0.19/0.48    spl4_60 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.19/0.48  fof(f420,plain,(
% 0.19/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_17 | spl4_60)),
% 0.19/0.48    inference(resolution,[],[f418,f134])).
% 0.19/0.48  fof(f134,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_17),
% 0.19/0.48    inference(avatar_component_clause,[],[f133])).
% 0.19/0.48  fof(f418,plain,(
% 0.19/0.48    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | spl4_60),
% 0.19/0.48    inference(avatar_component_clause,[],[f416])).
% 0.19/0.48  fof(f419,plain,(
% 0.19/0.48    ~spl4_18 | ~spl4_60 | ~spl4_26 | ~spl4_20 | ~spl4_54),
% 0.19/0.48    inference(avatar_split_clause,[],[f414,f376,f152,f186,f416,f137])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    spl4_18 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.48  fof(f186,plain,(
% 0.19/0.48    spl4_26 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.19/0.48  fof(f152,plain,(
% 0.19/0.48    spl4_20 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.48  fof(f376,plain,(
% 0.19/0.48    spl4_54 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.19/0.48  fof(f414,plain,(
% 0.19/0.48    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_20 | ~spl4_54)),
% 0.19/0.48    inference(resolution,[],[f377,f153])).
% 0.19/0.48  fof(f153,plain,(
% 0.19/0.48    ( ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) ) | ~spl4_20),
% 0.19/0.48    inference(avatar_component_clause,[],[f152])).
% 0.19/0.48  fof(f377,plain,(
% 0.19/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl4_54),
% 0.19/0.48    inference(avatar_component_clause,[],[f376])).
% 0.19/0.48  fof(f413,plain,(
% 0.19/0.48    ~spl4_5 | ~spl4_6 | ~spl4_45 | spl4_54),
% 0.19/0.48    inference(avatar_split_clause,[],[f380,f376,f307,f81,f76])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    spl4_6 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.48  fof(f307,plain,(
% 0.19/0.48    spl4_45 <=> ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.19/0.48  fof(f380,plain,(
% 0.19/0.48    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_45 | spl4_54)),
% 0.19/0.48    inference(resolution,[],[f378,f308])).
% 0.19/0.48  fof(f308,plain,(
% 0.19/0.48    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_45),
% 0.19/0.48    inference(avatar_component_clause,[],[f307])).
% 0.19/0.48  fof(f378,plain,(
% 0.19/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_54),
% 0.19/0.48    inference(avatar_component_clause,[],[f376])).
% 0.19/0.48  fof(f408,plain,(
% 0.19/0.48    ~spl4_37 | spl4_58 | ~spl4_7 | ~spl4_41),
% 0.19/0.48    inference(avatar_split_clause,[],[f288,f284,f85,f406,f254])).
% 0.19/0.48  fof(f254,plain,(
% 0.19/0.48    spl4_37 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.19/0.48  fof(f85,plain,(
% 0.19/0.48    spl4_7 <=> v3_pre_topc(sK3,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.48  fof(f284,plain,(
% 0.19/0.48    spl4_41 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,X1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.19/0.48  fof(f288,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,k1_tops_1(sK0,X0))) ) | (~spl4_7 | ~spl4_41)),
% 0.19/0.48    inference(resolution,[],[f285,f87])).
% 0.19/0.48  fof(f87,plain,(
% 0.19/0.48    v3_pre_topc(sK3,sK0) | ~spl4_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f85])).
% 0.19/0.48  fof(f285,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,X1))) ) | ~spl4_41),
% 0.19/0.48    inference(avatar_component_clause,[],[f284])).
% 0.19/0.48  fof(f397,plain,(
% 0.19/0.48    spl4_56 | ~spl4_13 | spl4_54),
% 0.19/0.48    inference(avatar_split_clause,[],[f381,f376,f114,f395])).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    spl4_13 <=> ! [X1,X0,X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.48  fof(f381,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))) ) | (~spl4_13 | spl4_54)),
% 0.19/0.48    inference(resolution,[],[f378,f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_13),
% 0.19/0.48    inference(avatar_component_clause,[],[f114])).
% 0.19/0.48  fof(f379,plain,(
% 0.19/0.48    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_54 | spl4_6 | ~spl4_32),
% 0.19/0.48    inference(avatar_split_clause,[],[f369,f215,f81,f376,f76,f71,f66,f61,f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    spl4_1 <=> v2_struct_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.48  fof(f215,plain,(
% 0.19/0.48    spl4_32 <=> ! [X1,X0,X2] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.19/0.48  fof(f369,plain,(
% 0.19/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_6 | ~spl4_32)),
% 0.19/0.48    inference(resolution,[],[f82,f216])).
% 0.19/0.48  fof(f216,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_32),
% 0.19/0.48    inference(avatar_component_clause,[],[f215])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    ~m1_connsp_2(sK2,sK0,sK1) | spl4_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f81])).
% 0.19/0.48  fof(f309,plain,(
% 0.19/0.48    spl4_45 | ~spl4_4 | ~spl4_43),
% 0.19/0.48    inference(avatar_split_clause,[],[f300,f295,f71,f307])).
% 0.19/0.48  fof(f295,plain,(
% 0.19/0.48    spl4_43 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.19/0.48  fof(f300,plain,(
% 0.19/0.48    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_4 | ~spl4_43)),
% 0.19/0.48    inference(resolution,[],[f296,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f71])).
% 0.19/0.48  fof(f296,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_43),
% 0.19/0.48    inference(avatar_component_clause,[],[f295])).
% 0.19/0.48  fof(f297,plain,(
% 0.19/0.48    ~spl4_2 | ~spl4_3 | spl4_43 | spl4_1 | ~spl4_30),
% 0.19/0.48    inference(avatar_split_clause,[],[f228,f206,f56,f295,f66,f61])).
% 0.19/0.48  fof(f206,plain,(
% 0.19/0.48    spl4_30 <=> ! [X1,X0,X2] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.19/0.48  fof(f228,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | (spl4_1 | ~spl4_30)),
% 0.19/0.48    inference(resolution,[],[f207,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ~v2_struct_0(sK0) | spl4_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f56])).
% 0.19/0.48  fof(f207,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2))) ) | ~spl4_30),
% 0.19/0.48    inference(avatar_component_clause,[],[f206])).
% 0.19/0.48  fof(f286,plain,(
% 0.19/0.48    spl4_41 | ~spl4_3 | ~spl4_28),
% 0.19/0.48    inference(avatar_split_clause,[],[f222,f198,f66,f284])).
% 0.19/0.48  fof(f198,plain,(
% 0.19/0.48    spl4_28 <=> ! [X1,X0,X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.19/0.48  fof(f222,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,X1))) ) | (~spl4_3 | ~spl4_28)),
% 0.19/0.48    inference(resolution,[],[f199,f68])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    l1_pre_topc(sK0) | ~spl4_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f66])).
% 0.19/0.48  fof(f199,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2))) ) | ~spl4_28),
% 0.19/0.48    inference(avatar_component_clause,[],[f198])).
% 0.19/0.48  fof(f257,plain,(
% 0.19/0.48    spl4_6 | spl4_37),
% 0.19/0.48    inference(avatar_split_clause,[],[f40,f254,f81])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(rectify,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.19/0.48    inference(negated_conjecture,[],[f9])).
% 0.19/0.48  fof(f9,conjecture,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.19/0.48  fof(f217,plain,(
% 0.19/0.48    spl4_32),
% 0.19/0.48    inference(avatar_split_clause,[],[f48,f215])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.19/0.48  fof(f208,plain,(
% 0.19/0.48    spl4_30),
% 0.19/0.48    inference(avatar_split_clause,[],[f47,f206])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f33])).
% 0.19/0.48  fof(f200,plain,(
% 0.19/0.48    spl4_28),
% 0.19/0.48    inference(avatar_split_clause,[],[f46,f198])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.19/0.48  fof(f189,plain,(
% 0.19/0.48    spl4_26 | ~spl4_10 | ~spl4_19),
% 0.19/0.48    inference(avatar_split_clause,[],[f150,f145,f99,f186])).
% 0.19/0.48  fof(f145,plain,(
% 0.19/0.48    spl4_19 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.48  fof(f150,plain,(
% 0.19/0.48    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_10 | ~spl4_19)),
% 0.19/0.48    inference(resolution,[],[f147,f100])).
% 0.19/0.48  fof(f147,plain,(
% 0.19/0.48    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_19),
% 0.19/0.48    inference(avatar_component_clause,[],[f145])).
% 0.19/0.48  fof(f162,plain,(
% 0.19/0.48    spl4_6 | spl4_21),
% 0.19/0.48    inference(avatar_split_clause,[],[f43,f159,f81])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f154,plain,(
% 0.19/0.48    ~spl4_6 | spl4_20),
% 0.19/0.48    inference(avatar_split_clause,[],[f44,f152,f81])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f148,plain,(
% 0.19/0.48    spl4_19 | ~spl4_14 | ~spl4_18),
% 0.19/0.48    inference(avatar_split_clause,[],[f141,f137,f119,f145])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    spl4_14 <=> ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.48  fof(f141,plain,(
% 0.19/0.48    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | (~spl4_14 | ~spl4_18)),
% 0.19/0.48    inference(resolution,[],[f139,f120])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl4_14),
% 0.19/0.48    inference(avatar_component_clause,[],[f119])).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl4_18),
% 0.19/0.48    inference(avatar_component_clause,[],[f137])).
% 0.19/0.48  fof(f140,plain,(
% 0.19/0.48    spl4_18 | ~spl4_5 | ~spl4_16),
% 0.19/0.48    inference(avatar_split_clause,[],[f131,f128,f76,f137])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    spl4_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.48  fof(f131,plain,(
% 0.19/0.48    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_5 | ~spl4_16)),
% 0.19/0.48    inference(resolution,[],[f129,f78])).
% 0.19/0.48  fof(f78,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f76])).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl4_16),
% 0.19/0.48    inference(avatar_component_clause,[],[f128])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    spl4_17),
% 0.19/0.48    inference(avatar_split_clause,[],[f51,f133])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    spl4_16 | ~spl4_3 | ~spl4_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f126,f123,f66,f128])).
% 0.19/0.48  fof(f123,plain,(
% 0.19/0.48    spl4_15 <=> ! [X1,X0] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.48  fof(f126,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | (~spl4_3 | ~spl4_15)),
% 0.19/0.48    inference(resolution,[],[f124,f68])).
% 0.19/0.48  fof(f124,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) ) | ~spl4_15),
% 0.19/0.48    inference(avatar_component_clause,[],[f123])).
% 0.19/0.48  fof(f125,plain,(
% 0.19/0.48    spl4_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f45,f123])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    spl4_14 | ~spl4_11 | ~spl4_12),
% 0.19/0.48    inference(avatar_split_clause,[],[f117,f110,f104,f119])).
% 0.19/0.48  fof(f104,plain,(
% 0.19/0.48    spl4_11 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.48  fof(f110,plain,(
% 0.19/0.48    spl4_12 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.48  fof(f117,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2)) ) | (~spl4_11 | ~spl4_12)),
% 0.19/0.48    inference(resolution,[],[f111,f106])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f104])).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl4_12),
% 0.19/0.48    inference(avatar_component_clause,[],[f110])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    spl4_13),
% 0.19/0.48    inference(avatar_split_clause,[],[f49,f114])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.48  fof(f112,plain,(
% 0.19/0.48    spl4_12),
% 0.19/0.48    inference(avatar_split_clause,[],[f54,f110])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    spl4_11 | ~spl4_5 | ~spl4_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f102,f95,f76,f104])).
% 0.19/0.48  fof(f95,plain,(
% 0.19/0.48    spl4_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    r1_tarski(sK2,u1_struct_0(sK0)) | (~spl4_5 | ~spl4_9)),
% 0.19/0.48    inference(resolution,[],[f96,f78])).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl4_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f95])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    spl4_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f53,f99])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.48    inference(nnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.48  fof(f97,plain,(
% 0.19/0.48    spl4_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f52,f95])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f34])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    spl4_6 | spl4_8),
% 0.19/0.48    inference(avatar_split_clause,[],[f42,f90,f81])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    spl4_6 | spl4_7),
% 0.19/0.49    inference(avatar_split_clause,[],[f41,f85,f81])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    spl4_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f39,f76])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    spl4_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f38,f71])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    spl4_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f37,f66])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    l1_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    spl4_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f36,f61])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    v2_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ~spl4_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f35,f56])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ~v2_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f32])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (12057)------------------------------
% 0.19/0.49  % (12057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12057)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (12057)Memory used [KB]: 5628
% 0.19/0.49  % (12057)Time elapsed: 0.075 s
% 0.19/0.49  % (12057)------------------------------
% 0.19/0.49  % (12057)------------------------------
% 0.19/0.49  % (12040)Success in time 0.138 s
%------------------------------------------------------------------------------
