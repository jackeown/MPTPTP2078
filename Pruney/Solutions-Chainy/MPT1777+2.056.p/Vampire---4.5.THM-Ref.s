%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 459 expanded)
%              Number of leaves         :   63 ( 189 expanded)
%              Depth                    :    9
%              Number of atoms          : 1351 (3297 expanded)
%              Number of equality atoms :   20 ( 178 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f111,f115,f119,f123,f127,f131,f135,f139,f147,f151,f155,f159,f163,f167,f171,f175,f179,f183,f187,f191,f195,f199,f203,f211,f220,f236,f241,f245,f253,f261,f269,f272,f332,f361,f366,f371,f381,f387,f422,f437,f443,f454,f503,f513,f532,f542,f552,f556,f566])).

fof(f566,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f564,f130])).

fof(f130,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f564,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f563,f134])).

fof(f134,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl10_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f563,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f562,f146])).

fof(f146,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl10_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f562,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f558,f138])).

fof(f138,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f558,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_19
    | ~ spl10_73 ),
    inference(resolution,[],[f421,f178])).

fof(f178,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl10_19
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f421,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl10_73
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f556,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_23
    | spl10_90 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_23
    | spl10_90 ),
    inference(unit_resulting_resolution,[],[f134,f138,f150,f551,f194])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_23
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f551,plain,
    ( ~ v2_pre_topc(sK2)
    | spl10_90 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl10_90
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f150,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl10_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f552,plain,
    ( ~ spl10_40
    | ~ spl10_90
    | spl10_3
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_89 ),
    inference(avatar_split_clause,[],[f548,f540,f189,f181,f113,f550,f264])).

fof(f264,plain,
    ( spl10_40
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f113,plain,
    ( spl10_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f181,plain,
    ( spl10_20
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_pre_topc(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f189,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f540,plain,
    ( spl10_89
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f548,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | spl10_3
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f547,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f547,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | spl10_3
    | ~ spl10_22
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f546,f114])).

fof(f114,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f546,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ spl10_22
    | ~ spl10_89 ),
    inference(duplicate_literal_removal,[],[f543])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl10_22
    | ~ spl10_89 ),
    inference(resolution,[],[f541,f190])).

fof(f190,plain,
    ( ! [X0] :
        ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f541,plain,
    ( ! [X1] :
        ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK2,X1) )
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f540])).

fof(f542,plain,
    ( spl10_89
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f538,f530,f243,f201,f540])).

fof(f201,plain,
    ( spl10_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f243,plain,
    ( spl10_35
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X1,u1_pre_topc(X0))
        | v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f530,plain,
    ( spl10_88
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v3_pre_topc(u1_struct_0(sK2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f538,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)) )
    | ~ spl10_25
    | ~ spl10_35
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f536,f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f201])).

fof(f536,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)) )
    | ~ spl10_35
    | ~ spl10_88 ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1))
        | ~ l1_pre_topc(X1) )
    | ~ spl10_35
    | ~ spl10_88 ),
    inference(resolution,[],[f531,f244])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X1,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f243])).

fof(f531,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(u1_struct_0(sK2),X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f530])).

fof(f532,plain,
    ( spl10_88
    | ~ spl10_37
    | ~ spl10_85 ),
    inference(avatar_split_clause,[],[f517,f501,f251,f530])).

fof(f251,plain,
    ( spl10_37
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f501,plain,
    ( spl10_85
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f517,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v3_pre_topc(u1_struct_0(sK2),X2) )
    | ~ spl10_37
    | ~ spl10_85 ),
    inference(duplicate_literal_removal,[],[f516])).

fof(f516,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v3_pre_topc(u1_struct_0(sK2),X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl10_37
    | ~ spl10_85 ),
    inference(resolution,[],[f502,f252])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( v1_tsep_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f251])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_85 ),
    inference(avatar_component_clause,[],[f501])).

fof(f513,plain,
    ( ~ spl10_74
    | ~ spl10_71
    | ~ spl10_24
    | spl10_84 ),
    inference(avatar_split_clause,[],[f504,f498,f197,f414,f432])).

fof(f432,plain,
    ( spl10_74
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f414,plain,
    ( spl10_71
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f197,plain,
    ( spl10_24
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f498,plain,
    ( spl10_84
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f504,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl10_24
    | spl10_84 ),
    inference(resolution,[],[f499,f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f499,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl10_84 ),
    inference(avatar_component_clause,[],[f498])).

fof(f503,plain,
    ( ~ spl10_84
    | spl10_85
    | spl10_2
    | ~ spl10_34
    | ~ spl10_56
    | spl10_72 ),
    inference(avatar_split_clause,[],[f456,f417,f330,f239,f109,f501,f498])).

fof(f109,plain,
    ( spl10_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f239,plain,
    ( spl10_34
  <=> ! [X0] :
        ( m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f330,plain,
    ( spl10_56
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v1_tsep_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f417,plain,
    ( spl10_72
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X0) )
    | spl10_2
    | ~ spl10_34
    | ~ spl10_56
    | spl10_72 ),
    inference(subsumption_resolution,[],[f455,f240])).

fof(f240,plain,
    ( ! [X0] :
        ( m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f239])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X0) )
    | spl10_2
    | ~ spl10_56
    | spl10_72 ),
    inference(subsumption_resolution,[],[f429,f110])).

fof(f110,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X0) )
    | ~ spl10_56
    | spl10_72 ),
    inference(resolution,[],[f418,f331])).

fof(f331,plain,
    ( ! [X2,X0,X1] :
        ( v1_tsep_1(X1,X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v2_struct_0(X0) )
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f330])).

fof(f418,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl10_72 ),
    inference(avatar_component_clause,[],[f417])).

fof(f454,plain,
    ( ~ spl10_40
    | ~ spl10_20
    | spl10_75 ),
    inference(avatar_split_clause,[],[f444,f441,f181,f264])).

fof(f441,plain,
    ( spl10_75
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f444,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl10_20
    | spl10_75 ),
    inference(resolution,[],[f442,f182])).

fof(f442,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl10_75 ),
    inference(avatar_component_clause,[],[f441])).

fof(f443,plain,
    ( ~ spl10_75
    | ~ spl10_41
    | spl10_71 ),
    inference(avatar_split_clause,[],[f423,f414,f267,f441])).

fof(f267,plain,
    ( spl10_41
  <=> ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f423,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ spl10_41
    | spl10_71 ),
    inference(resolution,[],[f415,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f267])).

fof(f415,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl10_71 ),
    inference(avatar_component_clause,[],[f414])).

fof(f437,plain,
    ( ~ spl10_9
    | ~ spl10_11
    | ~ spl10_21
    | spl10_74 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_21
    | spl10_74 ),
    inference(unit_resulting_resolution,[],[f138,f146,f433,f186])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f433,plain,
    ( ~ l1_pre_topc(sK3)
    | spl10_74 ),
    inference(avatar_component_clause,[],[f432])).

% (1645)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f422,plain,
    ( ~ spl10_71
    | ~ spl10_72
    | spl10_73
    | spl10_3
    | ~ spl10_14
    | ~ spl10_67 ),
    inference(avatar_split_clause,[],[f391,f385,f157,f113,f420,f417,f414])).

fof(f157,plain,
    ( spl10_14
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f385,plain,
    ( spl10_67
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
        | ~ l1_pre_topc(X1) )
    | spl10_3
    | ~ spl10_14
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f389,f114])).

fof(f389,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | v2_struct_0(sK2)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_14
    | ~ spl10_67 ),
    inference(resolution,[],[f386,f158])).

fof(f158,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f385])).

fof(f387,plain,
    ( spl10_67
    | ~ spl10_13
    | spl10_15
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f383,f379,f161,f153,f385])).

fof(f153,plain,
    ( spl10_13
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f161,plain,
    ( spl10_15
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f379,plain,
    ( spl10_66
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_13
    | spl10_15
    | ~ spl10_66 ),
    inference(subsumption_resolution,[],[f382,f154])).

fof(f154,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f382,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1) )
    | spl10_15
    | ~ spl10_66 ),
    inference(resolution,[],[f380,f162])).

fof(f162,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl10_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f380,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(sK3,sK1,sK4,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f379])).

fof(f381,plain,
    ( spl10_66
    | spl10_2
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_65 ),
    inference(avatar_split_clause,[],[f377,f369,f173,f165,f125,f121,f117,f109,f379])).

fof(f117,plain,
    ( spl10_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f121,plain,
    ( spl10_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f125,plain,
    ( spl10_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f165,plain,
    ( spl10_16
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f173,plain,
    ( spl10_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f369,plain,
    ( spl10_65
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f377,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | spl10_2
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f376,f174])).

fof(f174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f376,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | spl10_2
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f375,f110])).

fof(f375,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f374,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f374,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | spl10_4
    | ~ spl10_5
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f373,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f373,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | spl10_4
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f372,f118])).

fof(f118,plain,
    ( ~ v2_struct_0(sK1)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK1,sK4,X2) )
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(resolution,[],[f370,f166])).

fof(f166,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f370,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f369])).

fof(f371,plain,
    ( spl10_65
    | ~ spl10_1
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f367,f364,f105,f369])).

fof(f105,plain,
    ( spl10_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f364,plain,
    ( spl10_64
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f367,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl10_1
    | ~ spl10_64 ),
    inference(resolution,[],[f365,f106])).

fof(f106,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f365,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f364])).

fof(f366,plain,
    ( spl10_64
    | ~ spl10_29
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f362,f359,f218,f364])).

fof(f218,plain,
    ( spl10_29
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f359,plain,
    ( spl10_63
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f362,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl10_29
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f360,f219])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f360,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,(
    spl10_63 ),
    inference(avatar_split_clause,[],[f97,f359])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f332,plain,(
    spl10_56 ),
    inference(avatar_split_clause,[],[f90,f330])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
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
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f272,plain,
    ( ~ spl10_9
    | ~ spl10_12
    | ~ spl10_21
    | spl10_40 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_21
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f138,f150,f265,f186])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_40 ),
    inference(avatar_component_clause,[],[f264])).

fof(f269,plain,
    ( ~ spl10_40
    | spl10_41
    | ~ spl10_17
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f262,f259,f169,f267,f264])).

fof(f169,plain,
    ( spl10_17
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f259,plain,
    ( spl10_39
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f262,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl10_17
    | ~ spl10_39 ),
    inference(superposition,[],[f260,f170])).

fof(f170,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl10_39
    | ~ spl10_21
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f237,f234,f185,f259])).

fof(f234,plain,
    ( spl10_33
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl10_21
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f235,f186])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f234])).

fof(f253,plain,(
    spl10_37 ),
    inference(avatar_split_clause,[],[f102,f251])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f98,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f245,plain,(
    spl10_35 ),
    inference(avatar_split_clause,[],[f85,f243])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f241,plain,
    ( spl10_34
    | ~ spl10_17
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f221,f209,f169,f239])).

fof(f209,plain,
    ( spl10_27
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f221,plain,
    ( ! [X0] :
        ( m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_17
    | ~ spl10_27 ),
    inference(superposition,[],[f210,f170])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f209])).

fof(f236,plain,(
    spl10_33 ),
    inference(avatar_split_clause,[],[f79,f234])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f220,plain,(
    spl10_29 ),
    inference(avatar_split_clause,[],[f93,f218])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f211,plain,(
    spl10_27 ),
    inference(avatar_split_clause,[],[f84,f209])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f203,plain,(
    spl10_25 ),
    inference(avatar_split_clause,[],[f82,f201])).

fof(f199,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f81,f197])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f195,plain,(
    spl10_23 ),
    inference(avatar_split_clause,[],[f92,f193])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f191,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f77,f189])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f187,plain,(
    spl10_21 ),
    inference(avatar_split_clause,[],[f80,f185])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f183,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f59,f181])).

% (1647)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f179,plain,(
    spl10_19 ),
    inference(avatar_split_clause,[],[f100,f177])).

fof(f100,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f42,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f175,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f47,f173])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f48,f169])).

fof(f48,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f46,f165])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,(
    ~ spl10_15 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f159,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f101,f157])).

fof(f101,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f44,f153])).

fof(f44,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f52,f149])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f50,f145])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f139,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f131,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f56,f129])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f53,f117])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f51,f113])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f49,f109])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:17:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (1653)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (1659)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (1654)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (1646)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (1662)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (1650)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (1652)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (1655)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (1653)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f567,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f107,f111,f115,f119,f123,f127,f131,f135,f139,f147,f151,f155,f159,f163,f167,f171,f175,f179,f183,f187,f191,f195,f199,f203,f211,f220,f236,f241,f245,f253,f261,f269,f272,f332,f361,f366,f371,f381,f387,f422,f437,f443,f454,f503,f513,f532,f542,f552,f556,f566])).
% 0.21/0.52  fof(f566,plain,(
% 0.21/0.52    spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_19 | ~spl10_73),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f565])).
% 0.21/0.52  fof(f565,plain,(
% 0.21/0.52    $false | (spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_19 | ~spl10_73)),
% 0.21/0.52    inference(subsumption_resolution,[],[f564,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl10_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl10_7 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.52  fof(f564,plain,(
% 0.21/0.52    v2_struct_0(sK0) | (~spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_19 | ~spl10_73)),
% 0.21/0.52    inference(subsumption_resolution,[],[f563,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl10_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl10_8 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.52  fof(f563,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_9 | ~spl10_11 | ~spl10_19 | ~spl10_73)),
% 0.21/0.52    inference(subsumption_resolution,[],[f562,f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0) | ~spl10_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl10_11 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.52  fof(f562,plain,(
% 0.21/0.52    ~m1_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_9 | ~spl10_19 | ~spl10_73)),
% 0.21/0.52    inference(subsumption_resolution,[],[f558,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl10_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl10_9 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.52  fof(f558,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_19 | ~spl10_73)),
% 0.21/0.52    inference(resolution,[],[f421,f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl10_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl10_19 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.52  fof(f421,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl10_73),
% 0.21/0.52    inference(avatar_component_clause,[],[f420])).
% 0.21/0.52  fof(f420,plain,(
% 0.21/0.52    spl10_73 <=> ! [X1] : (~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 0.21/0.52  fof(f556,plain,(
% 0.21/0.52    ~spl10_8 | ~spl10_9 | ~spl10_12 | ~spl10_23 | spl10_90),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f553])).
% 0.21/0.52  fof(f553,plain,(
% 0.21/0.52    $false | (~spl10_8 | ~spl10_9 | ~spl10_12 | ~spl10_23 | spl10_90)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f134,f138,f150,f551,f194])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl10_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f193])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl10_23 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.52  fof(f551,plain,(
% 0.21/0.52    ~v2_pre_topc(sK2) | spl10_90),
% 0.21/0.52    inference(avatar_component_clause,[],[f550])).
% 0.21/0.52  fof(f550,plain,(
% 0.21/0.52    spl10_90 <=> v2_pre_topc(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0) | ~spl10_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl10_12 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.52  fof(f552,plain,(
% 0.21/0.52    ~spl10_40 | ~spl10_90 | spl10_3 | ~spl10_20 | ~spl10_22 | ~spl10_89),
% 0.21/0.52    inference(avatar_split_clause,[],[f548,f540,f189,f181,f113,f550,f264])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    spl10_40 <=> l1_pre_topc(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl10_3 <=> v2_struct_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl10_20 <=> ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl10_22 <=> ! [X0] : (~l1_pre_topc(X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.52  fof(f540,plain,(
% 0.21/0.52    spl10_89 <=> ! [X1] : (~m1_pre_topc(sK2,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).
% 0.21/0.52  fof(f548,plain,(
% 0.21/0.52    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | (spl10_3 | ~spl10_20 | ~spl10_22 | ~spl10_89)),
% 0.21/0.52    inference(subsumption_resolution,[],[f547,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) ) | ~spl10_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f181])).
% 0.21/0.52  fof(f547,plain,(
% 0.21/0.52    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | (spl10_3 | ~spl10_22 | ~spl10_89)),
% 0.21/0.52    inference(subsumption_resolution,[],[f546,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ~v2_struct_0(sK2) | spl10_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f546,plain,(
% 0.21/0.52    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | (~spl10_22 | ~spl10_89)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f543])).
% 0.21/0.52  fof(f543,plain,(
% 0.21/0.52    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl10_22 | ~spl10_89)),
% 0.21/0.52    inference(resolution,[],[f541,f190])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl10_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f541,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK2,X1)) ) | ~spl10_89),
% 0.21/0.52    inference(avatar_component_clause,[],[f540])).
% 0.21/0.52  fof(f542,plain,(
% 0.21/0.52    spl10_89 | ~spl10_25 | ~spl10_35 | ~spl10_88),
% 0.21/0.52    inference(avatar_split_clause,[],[f538,f530,f243,f201,f540])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    spl10_25 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    spl10_35 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.21/0.52  fof(f530,plain,(
% 0.21/0.52    spl10_88 <=> ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v3_pre_topc(u1_struct_0(sK2),X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).
% 0.21/0.52  fof(f538,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1))) ) | (~spl10_25 | ~spl10_35 | ~spl10_88)),
% 0.21/0.52    inference(subsumption_resolution,[],[f536,f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl10_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f201])).
% 0.21/0.52  fof(f536,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1))) ) | (~spl10_35 | ~spl10_88)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f535])).
% 0.21/0.52  fof(f535,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(X1)) | ~l1_pre_topc(X1)) ) | (~spl10_35 | ~spl10_88)),
% 0.21/0.52    inference(resolution,[],[f531,f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) ) | ~spl10_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f243])).
% 0.21/0.52  fof(f531,plain,(
% 0.21/0.52    ( ! [X2] : (~v3_pre_topc(u1_struct_0(sK2),X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl10_88),
% 0.21/0.52    inference(avatar_component_clause,[],[f530])).
% 0.21/0.52  fof(f532,plain,(
% 0.21/0.52    spl10_88 | ~spl10_37 | ~spl10_85),
% 0.21/0.52    inference(avatar_split_clause,[],[f517,f501,f251,f530])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl10_37 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.21/0.52  fof(f501,plain,(
% 0.21/0.52    spl10_85 <=> ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).
% 0.21/0.52  fof(f517,plain,(
% 0.21/0.52    ( ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v3_pre_topc(u1_struct_0(sK2),X2)) ) | (~spl10_37 | ~spl10_85)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f516])).
% 0.21/0.52  fof(f516,plain,(
% 0.21/0.52    ( ! [X2] : (v2_struct_0(X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | ~v3_pre_topc(u1_struct_0(sK2),X2) | ~v2_pre_topc(X2)) ) | (~spl10_37 | ~spl10_85)),
% 0.21/0.52    inference(resolution,[],[f502,f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0)) ) | ~spl10_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f251])).
% 0.21/0.52  fof(f502,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tsep_1(sK2,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl10_85),
% 0.21/0.52    inference(avatar_component_clause,[],[f501])).
% 0.21/0.52  fof(f513,plain,(
% 0.21/0.52    ~spl10_74 | ~spl10_71 | ~spl10_24 | spl10_84),
% 0.21/0.52    inference(avatar_split_clause,[],[f504,f498,f197,f414,f432])).
% 0.21/0.52  fof(f432,plain,(
% 0.21/0.52    spl10_74 <=> l1_pre_topc(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).
% 0.21/0.52  fof(f414,plain,(
% 0.21/0.52    spl10_71 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    spl10_24 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.52  fof(f498,plain,(
% 0.21/0.52    spl10_84 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).
% 0.21/0.52  fof(f504,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | (~spl10_24 | spl10_84)),
% 0.21/0.52    inference(resolution,[],[f499,f198])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl10_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f197])).
% 0.21/0.52  fof(f499,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | spl10_84),
% 0.21/0.52    inference(avatar_component_clause,[],[f498])).
% 0.21/0.52  fof(f503,plain,(
% 0.21/0.52    ~spl10_84 | spl10_85 | spl10_2 | ~spl10_34 | ~spl10_56 | spl10_72),
% 0.21/0.52    inference(avatar_split_clause,[],[f456,f417,f330,f239,f109,f501,f498])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl10_2 <=> v2_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl10_34 <=> ! [X0] : (m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    spl10_56 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 0.21/0.52  fof(f417,plain,(
% 0.21/0.52    spl10_72 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X0)) ) | (spl10_2 | ~spl10_34 | ~spl10_56 | spl10_72)),
% 0.21/0.52    inference(subsumption_resolution,[],[f455,f240])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | ~spl10_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f239])).
% 0.21/0.52  fof(f455,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X0)) ) | (spl10_2 | ~spl10_56 | spl10_72)),
% 0.21/0.52    inference(subsumption_resolution,[],[f429,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~v2_struct_0(sK3) | spl10_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X0)) ) | (~spl10_56 | spl10_72)),
% 0.21/0.53    inference(resolution,[],[f418,f331])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X0)) ) | ~spl10_56),
% 0.21/0.53    inference(avatar_component_clause,[],[f330])).
% 0.21/0.53  fof(f418,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK3) | spl10_72),
% 0.21/0.53    inference(avatar_component_clause,[],[f417])).
% 0.21/0.53  fof(f454,plain,(
% 0.21/0.53    ~spl10_40 | ~spl10_20 | spl10_75),
% 0.21/0.53    inference(avatar_split_clause,[],[f444,f441,f181,f264])).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    spl10_75 <=> m1_pre_topc(sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | (~spl10_20 | spl10_75)),
% 0.21/0.53    inference(resolution,[],[f442,f182])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK2) | spl10_75),
% 0.21/0.53    inference(avatar_component_clause,[],[f441])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    ~spl10_75 | ~spl10_41 | spl10_71),
% 0.21/0.53    inference(avatar_split_clause,[],[f423,f414,f267,f441])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl10_41 <=> ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.21/0.53  fof(f423,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK2) | (~spl10_41 | spl10_71)),
% 0.21/0.53    inference(resolution,[],[f415,f268])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2)) ) | ~spl10_41),
% 0.21/0.53    inference(avatar_component_clause,[],[f267])).
% 0.21/0.53  fof(f415,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK3) | spl10_71),
% 0.21/0.53    inference(avatar_component_clause,[],[f414])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    ~spl10_9 | ~spl10_11 | ~spl10_21 | spl10_74),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f435])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    $false | (~spl10_9 | ~spl10_11 | ~spl10_21 | spl10_74)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f138,f146,f433,f186])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl10_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    spl10_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | spl10_74),
% 0.21/0.53    inference(avatar_component_clause,[],[f432])).
% 0.21/0.53  % (1645)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    ~spl10_71 | ~spl10_72 | spl10_73 | spl10_3 | ~spl10_14 | ~spl10_67),
% 0.21/0.53    inference(avatar_split_clause,[],[f391,f385,f157,f113,f420,f417,f414])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl10_14 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    spl10_67 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).
% 0.21/0.53  fof(f391,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~l1_pre_topc(X1)) ) | (spl10_3 | ~spl10_14 | ~spl10_67)),
% 0.21/0.53    inference(subsumption_resolution,[],[f389,f114])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~l1_pre_topc(X1)) ) | (~spl10_14 | ~spl10_67)),
% 0.21/0.53    inference(resolution,[],[f386,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl10_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f157])).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1)) ) | ~spl10_67),
% 0.21/0.53    inference(avatar_component_clause,[],[f385])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    spl10_67 | ~spl10_13 | spl10_15 | ~spl10_66),
% 0.21/0.53    inference(avatar_split_clause,[],[f383,f379,f161,f153,f385])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    spl10_13 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    spl10_15 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    spl10_66 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 0.21/0.53  fof(f383,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1)) ) | (~spl10_13 | spl10_15 | ~spl10_66)),
% 0.21/0.53    inference(subsumption_resolution,[],[f382,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl10_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f153])).
% 0.21/0.53  fof(f382,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1)) ) | (spl10_15 | ~spl10_66)),
% 0.21/0.53    inference(resolution,[],[f380,f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl10_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f161])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,sK1,sK4,X2) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | ~l1_pre_topc(X0)) ) | ~spl10_66),
% 0.21/0.53    inference(avatar_component_clause,[],[f379])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    spl10_66 | spl10_2 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_16 | ~spl10_18 | ~spl10_65),
% 0.21/0.53    inference(avatar_split_clause,[],[f377,f369,f173,f165,f125,f121,f117,f109,f379])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl10_4 <=> v2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl10_5 <=> v2_pre_topc(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl10_6 <=> l1_pre_topc(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl10_16 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl10_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    spl10_65 <=> ! [X1,X3,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (spl10_2 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_16 | ~spl10_18 | ~spl10_65)),
% 0.21/0.53    inference(subsumption_resolution,[],[f376,f174])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl10_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f173])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (spl10_2 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_16 | ~spl10_65)),
% 0.21/0.53    inference(subsumption_resolution,[],[f375,f110])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_16 | ~spl10_65)),
% 0.21/0.53    inference(subsumption_resolution,[],[f374,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | ~spl10_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (spl10_4 | ~spl10_5 | ~spl10_16 | ~spl10_65)),
% 0.21/0.53    inference(subsumption_resolution,[],[f373,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    v2_pre_topc(sK1) | ~spl10_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (spl10_4 | ~spl10_16 | ~spl10_65)),
% 0.21/0.53    inference(subsumption_resolution,[],[f372,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~v2_struct_0(sK1) | spl10_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f117])).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK1,sK4,X2)) ) | (~spl10_16 | ~spl10_65)),
% 0.21/0.53    inference(resolution,[],[f370,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl10_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f165])).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | ~spl10_65),
% 0.21/0.53    inference(avatar_component_clause,[],[f369])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    spl10_65 | ~spl10_1 | ~spl10_64),
% 0.21/0.53    inference(avatar_split_clause,[],[f367,f364,f105,f369])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl10_1 <=> v1_funct_1(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    spl10_64 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | (~spl10_1 | ~spl10_64)),
% 0.21/0.53    inference(resolution,[],[f365,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v1_funct_1(sK4) | ~spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl10_64),
% 0.21/0.53    inference(avatar_component_clause,[],[f364])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    spl10_64 | ~spl10_29 | ~spl10_63),
% 0.21/0.53    inference(avatar_split_clause,[],[f362,f359,f218,f364])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    spl10_29 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    spl10_63 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | (~spl10_29 | ~spl10_63)),
% 0.21/0.53    inference(subsumption_resolution,[],[f360,f219])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) ) | ~spl10_29),
% 0.21/0.53    inference(avatar_component_clause,[],[f218])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl10_63),
% 0.21/0.53    inference(avatar_component_clause,[],[f359])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    spl10_63),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f359])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.53    inference(equality_resolution,[],[f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    spl10_56),
% 0.21/0.53    inference(avatar_split_clause,[],[f90,f330])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ~spl10_9 | ~spl10_12 | ~spl10_21 | spl10_40),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    $false | (~spl10_9 | ~spl10_12 | ~spl10_21 | spl10_40)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f138,f150,f265,f186])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | spl10_40),
% 0.21/0.53    inference(avatar_component_clause,[],[f264])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    ~spl10_40 | spl10_41 | ~spl10_17 | ~spl10_39),
% 0.21/0.53    inference(avatar_split_clause,[],[f262,f259,f169,f267,f264])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    spl10_17 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    spl10_39 <=> ! [X1,X0] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X0,sK2)) ) | (~spl10_17 | ~spl10_39)),
% 0.21/0.53    inference(superposition,[],[f260,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl10_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f169])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) ) | ~spl10_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f259])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    spl10_39 | ~spl10_21 | ~spl10_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f237,f234,f185,f259])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    spl10_33 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | (~spl10_21 | ~spl10_33)),
% 0.21/0.53    inference(subsumption_resolution,[],[f235,f186])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | ~spl10_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f234])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl10_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f102,f251])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    spl10_35),
% 0.21/0.53    inference(avatar_split_clause,[],[f85,f243])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    spl10_34 | ~spl10_17 | ~spl10_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f221,f209,f169,f239])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    spl10_27 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ( ! [X0] : (m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | (~spl10_17 | ~spl10_27)),
% 0.21/0.53    inference(superposition,[],[f210,f170])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl10_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f209])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    spl10_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f234])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    spl10_29),
% 0.21/0.53    inference(avatar_split_clause,[],[f93,f218])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    spl10_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f84,f209])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    spl10_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f82,f201])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    spl10_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f197])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl10_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f92,f193])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl10_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f77,f189])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    spl10_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f80,f185])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl10_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f59,f181])).
% 0.21/0.53  % (1647)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl10_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f100,f177])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.53    inference(backward_demodulation,[],[f42,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK5 = sK6),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl10_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f173])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl10_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f169])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl10_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f165])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~spl10_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f161])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl10_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f101,f157])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f40,f41])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl10_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f153])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl10_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f52,f149])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    spl10_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f145])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl10_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f58,f137])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl10_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f133])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~spl10_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f129])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl10_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f125])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl10_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f121])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ~spl10_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f117])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~spl10_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f113])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~spl10_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f109])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl10_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f105])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (1653)------------------------------
% 0.21/0.53  % (1653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1653)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (1653)Memory used [KB]: 11001
% 0.21/0.53  % (1653)Time elapsed: 0.063 s
% 0.21/0.53  % (1653)------------------------------
% 0.21/0.53  % (1653)------------------------------
% 0.21/0.53  % (1656)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1643)Success in time 0.173 s
%------------------------------------------------------------------------------
