%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 328 expanded)
%              Number of leaves         :   31 ( 123 expanded)
%              Depth                    :    8
%              Number of atoms          :  712 (2701 expanded)
%              Number of equality atoms :   24 ( 117 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f94,f98,f102,f106,f110,f114,f118,f125,f128,f136,f147,f154,f158,f169,f173,f179,f189,f194,f212])).

fof(f212,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_20
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_20
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f57,f73,f69,f77,f53,f65,f61,f49,f93,f188,f97,f105,f101,f109,f121,f113,f117,f127,f168])).

fof(f168,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ m1_connsp_2(X4,X1,X6)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_28
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f127,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_20
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f113,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_17
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f121,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_19
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f101,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_14
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f105,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f97,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_13
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f188,plain,
    ( m1_connsp_2(sK4,sK1,sK5)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_30
  <=> m1_connsp_2(sK4,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f93,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_12
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f49,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f61,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f65,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f53,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f69,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f73,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f57,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f194,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_27
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f65,f77,f69,f73,f57,f53,f61,f49,f93,f97,f105,f101,f126,f109,f113,f124,f117,f188,f157])).

fof(f157,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ m1_connsp_2(X4,X1,X6)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | v2_struct_0(X0)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | ~ r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_27
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f124,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f189,plain,
    ( spl7_30
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f185,f171,f100,f84,f187])).

fof(f84,plain,
    ( spl7_10
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f171,plain,
    ( spl7_29
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_connsp_2(sK4,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f185,plain,
    ( m1_connsp_2(sK4,sK1,sK5)
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f184,f101])).

fof(f184,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | m1_connsp_2(sK4,sK1,sK5)
    | ~ spl7_10
    | ~ spl7_29 ),
    inference(resolution,[],[f172,f85])).

fof(f85,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f171])).

fof(f179,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f177,f65])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f175,f61])).

fof(f175,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(resolution,[],[f146,f109])).

fof(f146,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_25
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f173,plain,
    ( spl7_29
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f165,f152,f134,f108,f64,f60,f56,f171])).

fof(f134,plain,
    ( spl7_22
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | m1_connsp_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f152,plain,
    ( spl7_26
  <=> sK4 = k1_tops_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_connsp_2(sK4,sK1,X0) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f164,f57])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f163,f109])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f162,f65])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f159,f61])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(superposition,[],[f135,f153])).

fof(f153,plain,
    ( sK4 = k1_tops_1(sK1,sK4)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f152])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | m1_connsp_2(X2,X0,X1) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f134])).

fof(f169,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f41,f167])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f158,plain,(
    spl7_27 ),
    inference(avatar_split_clause,[],[f40,f156])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f154,plain,
    ( spl7_26
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f150,f142,f108,f80,f64,f152])).

fof(f80,plain,
    ( spl7_9
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f142,plain,
    ( spl7_24
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f150,plain,
    ( sK4 = k1_tops_1(sK1,sK4)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f149,f65])).

fof(f149,plain,
    ( sK4 = k1_tops_1(sK1,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_9
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f148,f81])).

fof(f81,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f148,plain,
    ( sK4 = k1_tops_1(sK1,sK4)
    | ~ v3_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(resolution,[],[f143,f109])).

fof(f143,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f142])).

fof(f147,plain,
    ( spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f39,f145,f142])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f136,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f34,f134])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f128,plain,
    ( spl7_19
    | spl7_20 ),
    inference(avatar_split_clause,[],[f46,f123,f120])).

fof(f46,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f14,f20])).

fof(f20,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ( ( X5 = X6
                                    & r1_tarski(X4,u1_struct_0(X3))
                                    & r2_hidden(X5,X4)
                                    & v3_pre_topc(X4,X1) )
                                 => ( r1_tmap_1(X1,X0,X2,X5)
                                  <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f14,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f125,plain,
    ( ~ spl7_19
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f45,f123,f120])).

fof(f45,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f15,f20])).

fof(f15,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f118,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f27,f116])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f114,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f26,f112])).

fof(f26,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f110,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f22,f108])).

fof(f22,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f106,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f16,f20])).

fof(f16,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f102,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f21,f100])).

fof(f21,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f19,f96])).

fof(f19,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f24,f92])).

fof(f24,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f18,f84])).

fof(f18,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f17,f80])).

fof(f17,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f78,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f66,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (2763)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (2761)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (2771)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (2759)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (2767)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (2763)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (2769)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f94,f98,f102,f106,f110,f114,f118,f125,f128,f136,f147,f154,f158,f169,f173,f179,f189,f194,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_20 | ~spl7_28 | ~spl7_30),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    $false | (spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_20 | ~spl7_28 | ~spl7_30)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f57,f73,f69,f77,f53,f65,f61,f49,f93,f188,f97,f105,f101,f109,f121,f113,f117,f127,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | v2_struct_0(X0) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | ~spl7_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl7_28 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl7_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl7_20 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl7_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl7_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl7_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl7_17 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl7_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl7_19 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl7_16 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl7_14 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl7_15 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r1_tarski(sK4,u1_struct_0(sK3)) | ~spl7_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl7_13 <=> r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    m1_connsp_2(sK4,sK1,sK5) | ~spl7_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f187])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl7_30 <=> m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK1) | ~spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl7_12 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v2_struct_0(sK3) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl7_1 <=> v2_struct_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    v2_pre_topc(sK1) | ~spl7_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl7_4 <=> v2_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl7_5 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl7_2 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl7_8 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl7_6 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl7_7 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~v2_struct_0(sK1) | spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl7_3 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | spl7_20 | ~spl7_27 | ~spl7_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    $false | (spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | spl7_20 | ~spl7_27 | ~spl7_30)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f65,f77,f69,f73,f57,f53,f61,f49,f93,f97,f105,f101,f126,f109,f113,f124,f117,f188,f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) ) | ~spl7_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl7_27 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl7_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f123])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl7_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl7_30 | ~spl7_10 | ~spl7_14 | ~spl7_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f171,f100,f84,f187])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl7_10 <=> r2_hidden(sK5,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl7_29 <=> ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK4,sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    m1_connsp_2(sK4,sK1,sK5) | (~spl7_10 | ~spl7_14 | ~spl7_29)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f101])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK1)) | m1_connsp_2(sK4,sK1,sK5) | (~spl7_10 | ~spl7_29)),
% 0.21/0.51    inference(resolution,[],[f172,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    r2_hidden(sK5,sK4) | ~spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK4,sK1,X0)) ) | ~spl7_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~spl7_4 | ~spl7_5 | ~spl7_16 | ~spl7_25),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    $false | (~spl7_4 | ~spl7_5 | ~spl7_16 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f65])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | (~spl7_4 | ~spl7_16 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f61])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | (~spl7_16 | ~spl7_25)),
% 0.21/0.51    inference(resolution,[],[f146,f109])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl7_25 <=> ! [X0,X2] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl7_29 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_16 | ~spl7_22 | ~spl7_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f152,f134,f108,f64,f60,f56,f171])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl7_22 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl7_26 <=> sK4 = k1_tops_1(sK1,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK4,sK1,X0)) ) | (spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_16 | ~spl7_22 | ~spl7_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f57])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK4,sK1,X0)) ) | (~spl7_4 | ~spl7_5 | ~spl7_16 | ~spl7_22 | ~spl7_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f109])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | m1_connsp_2(sK4,sK1,X0)) ) | (~spl7_4 | ~spl7_5 | ~spl7_22 | ~spl7_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f162,f65])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | m1_connsp_2(sK4,sK1,X0)) ) | (~spl7_4 | ~spl7_22 | ~spl7_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f159,f61])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | m1_connsp_2(sK4,sK1,X0)) ) | (~spl7_22 | ~spl7_26)),
% 0.21/0.51    inference(superposition,[],[f135,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    sK4 = k1_tops_1(sK1,sK4) | ~spl7_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) ) | ~spl7_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl7_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f167])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    spl7_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f156])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.51    inference(equality_resolution,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl7_26 | ~spl7_5 | ~spl7_9 | ~spl7_16 | ~spl7_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f150,f142,f108,f80,f64,f152])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl7_9 <=> v3_pre_topc(sK4,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl7_24 <=> ! [X1,X3] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    sK4 = k1_tops_1(sK1,sK4) | (~spl7_5 | ~spl7_9 | ~spl7_16 | ~spl7_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f149,f65])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    sK4 = k1_tops_1(sK1,sK4) | ~l1_pre_topc(sK1) | (~spl7_9 | ~spl7_16 | ~spl7_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    v3_pre_topc(sK4,sK1) | ~spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    sK4 = k1_tops_1(sK1,sK4) | ~v3_pre_topc(sK4,sK1) | ~l1_pre_topc(sK1) | (~spl7_16 | ~spl7_24)),
% 0.21/0.51    inference(resolution,[],[f143,f109])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~l1_pre_topc(X1)) ) | ~spl7_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl7_24 | spl7_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f145,f142])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl7_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f134])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl7_19 | spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f123,f120])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f14,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    sK5 = sK6),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~spl7_19 | ~spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f123,f120])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f15,f20])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f116])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl7_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f112])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl7_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f108])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl7_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f104])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    inference(forward_demodulation,[],[f16,f20])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl7_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f100])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f19,f96])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f92])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl7_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f18,f84])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r2_hidden(sK5,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f17,f80])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    v3_pre_topc(sK4,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f76])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f72])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f64])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f60])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v2_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ~spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f52])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2763)------------------------------
% 0.21/0.51  % (2763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2763)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2763)Memory used [KB]: 10746
% 0.21/0.51  % (2763)Time elapsed: 0.074 s
% 0.21/0.51  % (2763)------------------------------
% 0.21/0.51  % (2763)------------------------------
% 0.21/0.51  % (2753)Success in time 0.15 s
%------------------------------------------------------------------------------
