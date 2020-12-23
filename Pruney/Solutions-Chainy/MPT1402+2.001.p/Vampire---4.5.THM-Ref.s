%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 260 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :    8
%              Number of atoms          :  649 (1169 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f97,f102,f108,f113,f120,f134,f138,f143,f154,f168,f220,f228,f236,f255,f261,f279])).

fof(f279,plain,
    ( ~ spl5_35
    | ~ spl5_3
    | ~ spl5_6
    | spl5_34
    | spl5_41 ),
    inference(avatar_split_clause,[],[f274,f259,f215,f71,f59,f218])).

fof(f218,plain,
    ( spl5_35
  <=> m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f59,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f71,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | r2_hidden(sK2(X0,X1),X1)
        | v2_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f215,plain,
    ( spl5_34
  <=> v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f259,plain,
    ( spl5_41
  <=> r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_6
    | spl5_34
    | spl5_41 ),
    inference(subsumption_resolution,[],[f273,f216])).

fof(f216,plain,
    ( ~ v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f215])).

fof(f273,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ spl5_3
    | ~ spl5_6
    | spl5_41 ),
    inference(subsumption_resolution,[],[f267,f60])).

fof(f60,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f267,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ spl5_6
    | spl5_41 ),
    inference(resolution,[],[f260,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v2_tops_2(X1,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f260,plain,
    ( ~ r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( ~ spl5_41
    | ~ spl5_35
    | spl5_34
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f257,f253,f215,f218,f259])).

fof(f253,plain,
    ( spl5_40
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f257,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | spl5_34
    | ~ spl5_40 ),
    inference(resolution,[],[f254,f216])).

fof(f254,plain,
    ( ! [X0] :
        ( v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl5_40
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f247,f234,f83,f59,f253])).

fof(f83,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f234,plain,
    ( spl5_37
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f246,f60])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_9
    | ~ spl5_37 ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | v2_tops_2(X0,sK0) )
    | ~ spl5_9
    | ~ spl5_37 ),
    inference(resolution,[],[f235,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v2_tops_2(X1,X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl5_37
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f180,f166,f75,f59,f234])).

fof(f75,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v4_pre_topc(sK2(X0,X1),X0)
        | v2_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f166,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f179,f60])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | v2_tops_2(X0,sK0) )
    | ~ spl5_7
    | ~ spl5_25 ),
    inference(resolution,[],[f167,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(sK2(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v2_tops_2(X1,X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f167,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f166])).

fof(f228,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_13
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_13
    | spl5_35 ),
    inference(subsumption_resolution,[],[f226,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f226,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_13
    | spl5_35 ),
    inference(subsumption_resolution,[],[f225,f64])).

fof(f64,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f225,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_13
    | spl5_35 ),
    inference(subsumption_resolution,[],[f224,f60])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_13
    | spl5_35 ),
    inference(subsumption_resolution,[],[f222,f56])).

fof(f56,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f222,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_13
    | spl5_35 ),
    inference(resolution,[],[f219,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f219,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( ~ spl5_34
    | ~ spl5_35
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f147,f132,f87,f67,f59,f55,f218,f215])).

fof(f67,plain,
    ( spl5_5
  <=> v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f87,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(X1,X0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f132,plain,
    ( spl5_19
  <=> k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f147,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f146,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f145,f60])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_5
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f144,f68])).

fof(f68,plain,
    ( ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f144,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(superposition,[],[f88,f133])).

fof(f133,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f168,plain,
    ( spl5_25
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f164,f152,f63,f166])).

fof(f152,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f153,f64])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl5_22
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f150,f141,f59,f55,f51,f152])).

fof(f141,plain,
    ( spl5_21
  <=> ! [X1,X0,X4] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X4,X0)
        | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f149,f60])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f148,f56])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_21 ),
    inference(resolution,[],[f142,f52])).

fof(f142,plain,
    ( ! [X4,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X4,X0)
        | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl5_21
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f139,f136,f79,f141])).

fof(f79,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f136,plain,
    ( spl5_20
  <=> ! [X1,X0,X4] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X4,X0)
        | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f139,plain,
    ( ! [X4,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X4,X0)
        | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f137,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f137,plain,
    ( ! [X4,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X4,X0)
        | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f44,f136])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X4,X0)
      | ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X4,X0)
      | ~ r2_hidden(X4,sK3(X0,X1,X2))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).

fof(f134,plain,
    ( spl5_19
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f130,f118,f63,f132])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f130,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(resolution,[],[f119,f64])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl5_16
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f116,f111,f59,f55,f51,f118])).

fof(f111,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f115,f60])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f114,f56])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) )
    | spl5_1
    | ~ spl5_15 ),
    inference(resolution,[],[f112,f52])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl5_15
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f109,f106,f79,f111])).

fof(f106,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f107,f80])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f39,f106])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,
    ( spl5_13
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f98,f95,f79,f100])).

fof(f95,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f96,f80])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_tops_2(X1,X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v2_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v2_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_2)).

fof(f85,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f23,f83])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f81,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f77,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f75])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f24,f71])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f18,f67])).

fof(f18,plain,(
    ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_connsp_2)).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f17,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (28493)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (28502)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (28494)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (28494)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f97,f102,f108,f113,f120,f134,f138,f143,f154,f168,f220,f228,f236,f255,f261,f279])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    ~spl5_35 | ~spl5_3 | ~spl5_6 | spl5_34 | spl5_41),
% 0.21/0.47    inference(avatar_split_clause,[],[f274,f259,f215,f71,f59,f218])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    spl5_35 <=> m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl5_3 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl5_6 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2(X0,X1),X1) | v2_tops_2(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    spl5_34 <=> v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    spl5_41 <=> r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_3 | ~spl5_6 | spl5_34 | spl5_41)),
% 0.21/0.47    inference(subsumption_resolution,[],[f273,f216])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    ~v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | spl5_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f215])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | (~spl5_3 | ~spl5_6 | spl5_41)),
% 0.21/0.47    inference(subsumption_resolution,[],[f267,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | (~spl5_6 | spl5_41)),
% 0.21/0.47    inference(resolution,[],[f260,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_tops_2(X1,X0)) ) | ~spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    ~r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | spl5_41),
% 0.21/0.47    inference(avatar_component_clause,[],[f259])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    ~spl5_41 | ~spl5_35 | spl5_34 | ~spl5_40),
% 0.21/0.47    inference(avatar_split_clause,[],[f257,f253,f215,f218,f259])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    spl5_40 <=> ! [X0] : (~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (spl5_34 | ~spl5_40)),
% 0.21/0.47    inference(resolution,[],[f254,f216])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    ( ! [X0] : (v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ) | ~spl5_40),
% 0.21/0.47    inference(avatar_component_clause,[],[f253])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    spl5_40 | ~spl5_3 | ~spl5_9 | ~spl5_37),
% 0.21/0.47    inference(avatar_split_clause,[],[f247,f234,f83,f59,f253])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl5_9 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    spl5_37 <=> ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl5_3 | ~spl5_9 | ~spl5_37)),
% 0.21/0.47    inference(subsumption_resolution,[],[f246,f60])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl5_9 | ~spl5_37)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f245])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_tops_2(X0,sK0)) ) | (~spl5_9 | ~spl5_37)),
% 0.21/0.47    inference(resolution,[],[f235,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_tops_2(X1,X0)) ) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl5_37),
% 0.21/0.47    inference(avatar_component_clause,[],[f234])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    spl5_37 | ~spl5_3 | ~spl5_7 | ~spl5_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f180,f166,f75,f59,f234])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl5_7 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(sK2(X0,X1),X0) | v2_tops_2(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    spl5_25 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl5_3 | ~spl5_7 | ~spl5_25)),
% 0.21/0.47    inference(subsumption_resolution,[],[f179,f60])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,X0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_tops_2(X0,sK0)) ) | (~spl5_7 | ~spl5_25)),
% 0.21/0.47    inference(resolution,[],[f167,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_tops_2(X1,X0)) ) | ~spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ) | ~spl5_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f166])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_13 | spl5_35),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_13 | spl5_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f226,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_13 | spl5_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f225,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_13 | spl5_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f224,f60])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_13 | spl5_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f222,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl5_2 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_13 | spl5_35)),
% 0.21/0.47    inference(resolution,[],[f219,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl5_13 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f218])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    ~spl5_34 | ~spl5_35 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_10 | ~spl5_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f132,f87,f67,f59,f55,f218,f215])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl5_5 <=> v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl5_10 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0) | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl5_19 <=> k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_10 | ~spl5_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f146,f56])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | (~spl5_3 | spl5_5 | ~spl5_10 | ~spl5_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f145,f60])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | (spl5_5 | ~spl5_10 | ~spl5_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f144,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_2(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | (~spl5_10 | ~spl5_19)),
% 0.21/0.47    inference(superposition,[],[f88,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~spl5_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f87])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    spl5_25 | ~spl5_4 | ~spl5_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f164,f152,f63,f166])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl5_22 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ) | (~spl5_4 | ~spl5_22)),
% 0.21/0.47    inference(resolution,[],[f153,f64])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | ~spl5_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f152])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl5_22 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f150,f141,f59,f55,f51,f152])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl5_21 <=> ! [X1,X0,X4] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f60])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f148,f56])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X1,sK0) | ~r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_21)),
% 0.21/0.47    inference(resolution,[],[f142,f52])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | ~spl5_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f141])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    spl5_21 | ~spl5_8 | ~spl5_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f139,f136,f79,f141])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl5_8 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl5_20 <=> ! [X1,X0,X4] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | (~spl5_8 | ~spl5_20)),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | ~spl5_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    spl5_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f136])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X4,X0) | ~r2_hidden(X4,sK3(X0,X1,X2)) | k1_connsp_2(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl5_19 | ~spl5_4 | ~spl5_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f118,f63,f132])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl5_16 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (~spl5_4 | ~spl5_16)),
% 0.21/0.47    inference(resolution,[],[f119,f64])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | ~spl5_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl5_16 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f111,f59,f55,f51,f118])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl5_15 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f60])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f56])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) ) | (spl5_1 | ~spl5_15)),
% 0.21/0.47    inference(resolution,[],[f112,f52])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | ~spl5_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl5_15 | ~spl5_8 | ~spl5_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f106,f79,f111])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl5_14 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | (~spl5_8 | ~spl5_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f80])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) ) | ~spl5_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl5_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f106])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2 | k1_connsp_2(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl5_13 | ~spl5_8 | ~spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f98,f95,f79,f100])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl5_12 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | (~spl5_8 | ~spl5_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f96,f80])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | ~spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f95])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.47    inference(equality_resolution,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | k1_connsp_2(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl5_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f87])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0) | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_2)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f83])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f79])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f75])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(sK2(X0,X1),X0) | v2_tops_2(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f71])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK2(X0,X1),X1) | v2_tops_2(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f67])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ~v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_connsp_2)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f63])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f59])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f55])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f51])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28494)------------------------------
% 0.21/0.47  % (28494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28494)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28494)Memory used [KB]: 10746
% 0.21/0.47  % (28494)Time elapsed: 0.063 s
% 0.21/0.47  % (28494)------------------------------
% 0.21/0.47  % (28494)------------------------------
% 0.21/0.47  % (28484)Success in time 0.114 s
%------------------------------------------------------------------------------
