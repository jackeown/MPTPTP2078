%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 422 expanded)
%              Number of leaves         :   51 ( 175 expanded)
%              Depth                    :   11
%              Number of atoms          : 1312 (3011 expanded)
%              Number of equality atoms :   17 (  87 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f112,f116,f124,f128,f132,f136,f143,f146,f150,f154,f158,f166,f170,f174,f182,f188,f192,f197,f200,f204,f213,f218,f230,f237,f242,f251,f258,f266,f276,f283,f286,f292,f294])).

fof(f294,plain,
    ( ~ spl6_43
    | ~ spl6_16
    | spl6_44 ),
    inference(avatar_split_clause,[],[f293,f290,f134,f281])).

fof(f281,plain,
    ( spl6_43
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f134,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f290,plain,
    ( spl6_44
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl6_16
    | spl6_44 ),
    inference(resolution,[],[f291,f135])).

fof(f135,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f291,plain,
    ( ~ l1_struct_0(sK3)
    | spl6_44 ),
    inference(avatar_component_clause,[],[f290])).

fof(f292,plain,
    ( ~ spl6_44
    | spl6_1
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f288,f261,f156,f74,f290])).

fof(f74,plain,
    ( spl6_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f156,plain,
    ( spl6_21
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

% (16492)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f261,plain,
    ( spl6_40
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

% (16491)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f288,plain,
    ( ~ l1_struct_0(sK3)
    | spl6_1
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f287,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f287,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(resolution,[],[f262,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f156])).

fof(f262,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f286,plain,
    ( ~ spl6_5
    | ~ spl6_11
    | ~ spl6_20
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_20
    | spl6_43 ),
    inference(unit_resulting_resolution,[],[f91,f115,f282,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_20
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK3)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f281])).

fof(f115,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_11
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f91,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f283,plain,
    ( ~ spl6_43
    | ~ spl6_19
    | ~ spl6_25
    | spl6_42 ),
    inference(avatar_split_clause,[],[f279,f274,f172,f148,f281])).

fof(f148,plain,
    ( spl6_19
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_pre_topc(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f172,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f274,plain,
    ( spl6_42
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f279,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl6_19
    | ~ spl6_25
    | spl6_42 ),
    inference(subsumption_resolution,[],[f277,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f277,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl6_25
    | spl6_42 ),
    inference(resolution,[],[f275,f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f172])).

fof(f275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( ~ spl6_42
    | spl6_1
    | ~ spl6_11
    | ~ spl6_13
    | spl6_17
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f272,f264,f141,f138,f122,f114,f74,f274])).

fof(f122,plain,
    ( spl6_13
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f138,plain,
    ( spl6_17
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f141,plain,
    ( spl6_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f264,plain,
    ( spl6_41
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f272,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl6_1
    | ~ spl6_11
    | ~ spl6_13
    | spl6_17
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f271,f139])).

fof(f139,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f271,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl6_1
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f270,f115])).

fof(f270,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl6_1
    | ~ spl6_13
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f269,f75])).

fof(f269,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl6_13
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f268,f123])).

fof(f123,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f268,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl6_18
    | ~ spl6_41 ),
    inference(resolution,[],[f265,f145])).

fof(f145,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl6_40
    | spl6_41
    | ~ spl6_24
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f259,f249,f168,f264,f261])).

fof(f168,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f249,plain,
    ( spl6_39
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | v1_xboole_0(u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl6_24
    | ~ spl6_39 ),
    inference(resolution,[],[f250,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f249])).

fof(f258,plain,
    ( ~ spl6_5
    | ~ spl6_11
    | ~ spl6_25
    | spl6_38 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_25
    | spl6_38 ),
    inference(subsumption_resolution,[],[f256,f91])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl6_11
    | ~ spl6_25
    | spl6_38 ),
    inference(subsumption_resolution,[],[f253,f115])).

fof(f253,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_25
    | spl6_38 ),
    inference(resolution,[],[f247,f173])).

fof(f247,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl6_38
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f251,plain,
    ( ~ spl6_38
    | spl6_39
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f244,f240,f114,f110,f249,f246])).

fof(f110,plain,
    ( spl6_10
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f240,plain,
    ( spl6_37
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | v2_struct_0(X2)
        | ~ r2_hidden(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X2,sK1)
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ v1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_pre_topc(X1,sK1)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f243,f115])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_pre_topc(X1,sK1)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(resolution,[],[f241,f111])).

fof(f111,plain,
    ( v1_tsep_1(sK3,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_tsep_1(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | v2_struct_0(X2)
        | ~ r2_hidden(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X2,sK1)
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( spl6_37
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f238,f235,f164,f240])).

fof(f164,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f235,plain,
    ( spl6_36
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ v1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | v2_struct_0(X2)
        | ~ r2_hidden(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X2,sK1)
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ v1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(resolution,[],[f236,f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f164])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ v1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( spl6_36
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f233,f228,f180,f90,f86,f235])).

fof(f86,plain,
    ( spl6_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f180,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f228,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ v1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f232,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ v2_pre_topc(sK1)
        | ~ v1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f231,f91])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v1_tsep_1(X1,sK1)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl6_27
    | ~ spl6_35 ),
    inference(resolution,[],[f229,f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(u1_struct_0(X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f180])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl6_35
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f226,f216,f130,f126,f102,f98,f94,f90,f86,f82,f228])).

fof(f82,plain,
    ( spl6_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f94,plain,
    ( spl6_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f98,plain,
    ( spl6_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f102,plain,
    ( spl6_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f126,plain,
    ( spl6_14
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f130,plain,
    ( spl6_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f216,plain,
    ( spl6_34
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ v3_pre_topc(X3,X1)
        | ~ r2_hidden(X4,X3)
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f225,f131])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f225,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f224,f99])).

fof(f99,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f223,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f222,f91])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f221,f87])).

fof(f221,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | spl6_3
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f220,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f219,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK1)
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(resolution,[],[f217,f127])).

fof(f127,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f217,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ v3_pre_topc(X3,X1)
        | ~ r2_hidden(X4,X3)
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f216])).

fof(f218,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f214,f211,f78,f216])).

fof(f78,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f211,plain,
    ( spl6_33
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
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ v3_pre_topc(X4,X1)
        | ~ r2_hidden(X6,X4)
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f214,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ v3_pre_topc(X3,X1)
        | ~ r2_hidden(X4,X3)
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl6_2
    | ~ spl6_33 ),
    inference(resolution,[],[f212,f79])).

fof(f79,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f212,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ v3_pre_topc(X4,X1)
        | ~ r2_hidden(X6,X4)
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl6_33
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f205,f202,f186,f211])).

fof(f186,plain,
    ( spl6_28
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f202,plain,
    ( spl6_31
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
        | ~ v3_pre_topc(X4,X1)
        | ~ r2_hidden(X6,X4)
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f205,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
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
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ v3_pre_topc(X4,X1)
        | ~ r2_hidden(X6,X4)
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f203,f187])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | v2_struct_0(X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f186])).

fof(f203,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
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
        | ~ v3_pre_topc(X4,X1)
        | ~ r2_hidden(X6,X4)
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f65,f202])).

fof(f65,plain,(
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
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f200,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_18
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_18
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f99,f83,f87,f91,f75,f79,f103,f95,f115,f123,f144,f127,f142,f131,f196])).

fof(f196,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_30
  <=> ! [X1,X3,X5,X0,X2] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f142,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f197,plain,
    ( spl6_30
    | ~ spl6_28
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f193,f190,f186,f195])).

fof(f190,plain,
    ( spl6_29
  <=> ! [X1,X3,X5,X0,X2] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f193,plain,
    ( ! [X2,X0,X5,X3,X1] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl6_28
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f191,f187])).

fof(f191,plain,
    ( ! [X2,X0,X5,X3,X1] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f63,f190])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f188,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f57,f186])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f182,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f72,f180])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f67,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f174,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f52,f172])).

fof(f170,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f60,f168])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f166,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f62,f164])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f53,f156])).

fof(f53,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f154,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f51,f152])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f150,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f50,f148])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f146,plain,
    ( spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f70,f141,f138])).

fof(f70,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f32,f35])).

fof(f35,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f32,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f143,plain,
    ( ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f69,f141,f138])).

fof(f69,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f33,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

% (16495)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f136,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f49,f134])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f132,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f42,f130])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f128,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f41,f126])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f68,f122])).

fof(f68,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f34,f35])).

fof(f34,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f39,f114])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f38,f110])).

fof(f38,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:25:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (16484)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (16499)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (16484)Refutation not found, incomplete strategy% (16484)------------------------------
% 0.20/0.48  % (16484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16489)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (16493)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (16484)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16484)Memory used [KB]: 10618
% 0.20/0.49  % (16484)Time elapsed: 0.063 s
% 0.20/0.49  % (16484)------------------------------
% 0.20/0.49  % (16484)------------------------------
% 0.20/0.49  % (16485)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (16498)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (16490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (16493)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f112,f116,f124,f128,f132,f136,f143,f146,f150,f154,f158,f166,f170,f174,f182,f188,f192,f197,f200,f204,f213,f218,f230,f237,f242,f251,f258,f266,f276,f283,f286,f292,f294])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    ~spl6_43 | ~spl6_16 | spl6_44),
% 0.20/0.49    inference(avatar_split_clause,[],[f293,f290,f134,f281])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    spl6_43 <=> l1_pre_topc(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl6_16 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    spl6_44 <=> l1_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    ~l1_pre_topc(sK3) | (~spl6_16 | spl6_44)),
% 0.20/0.49    inference(resolution,[],[f291,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl6_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    ~l1_struct_0(sK3) | spl6_44),
% 0.20/0.49    inference(avatar_component_clause,[],[f290])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    ~spl6_44 | spl6_1 | ~spl6_21 | ~spl6_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f288,f261,f156,f74,f290])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl6_1 <=> v2_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl6_21 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.49  % (16492)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    spl6_40 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.49  % (16491)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ~l1_struct_0(sK3) | (spl6_1 | ~spl6_21 | ~spl6_40)),
% 0.20/0.49    inference(subsumption_resolution,[],[f287,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~v2_struct_0(sK3) | spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ~l1_struct_0(sK3) | v2_struct_0(sK3) | (~spl6_21 | ~spl6_40)),
% 0.20/0.49    inference(resolution,[],[f262,f157])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl6_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f156])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK3)) | ~spl6_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f261])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    ~spl6_5 | ~spl6_11 | ~spl6_20 | spl6_43),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    $false | (~spl6_5 | ~spl6_11 | ~spl6_20 | spl6_43)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f91,f115,f282,f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl6_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl6_20 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    ~l1_pre_topc(sK3) | spl6_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f281])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK1) | ~spl6_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl6_11 <=> m1_pre_topc(sK3,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    l1_pre_topc(sK1) | ~spl6_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl6_5 <=> l1_pre_topc(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ~spl6_43 | ~spl6_19 | ~spl6_25 | spl6_42),
% 0.20/0.50    inference(avatar_split_clause,[],[f279,f274,f172,f148,f281])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl6_19 <=> ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl6_25 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    spl6_42 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    ~l1_pre_topc(sK3) | (~spl6_19 | ~spl6_25 | spl6_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f277,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) ) | ~spl6_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f148])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | (~spl6_25 | spl6_42)),
% 0.20/0.50    inference(resolution,[],[f275,f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl6_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f172])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | spl6_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f274])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ~spl6_42 | spl6_1 | ~spl6_11 | ~spl6_13 | spl6_17 | ~spl6_18 | ~spl6_41),
% 0.20/0.50    inference(avatar_split_clause,[],[f272,f264,f141,f138,f122,f114,f74,f274])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl6_13 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    spl6_17 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl6_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    spl6_41 <=> ! [X1,X0] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | (spl6_1 | ~spl6_11 | ~spl6_13 | spl6_17 | ~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(subsumption_resolution,[],[f271,f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl6_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tmap_1(sK1,sK0,sK2,sK4) | (spl6_1 | ~spl6_11 | ~spl6_13 | ~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(subsumption_resolution,[],[f270,f115])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tmap_1(sK1,sK0,sK2,sK4) | (spl6_1 | ~spl6_13 | ~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(subsumption_resolution,[],[f269,f75])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tmap_1(sK1,sK0,sK2,sK4) | (~spl6_13 | ~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(subsumption_resolution,[],[f268,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl6_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tmap_1(sK1,sK0,sK2,sK4) | (~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tmap_1(sK1,sK0,sK2,sK4) | (~spl6_18 | ~spl6_41)),
% 0.20/0.50    inference(resolution,[],[f265,f145])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl6_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f141])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | ~spl6_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f264])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    spl6_40 | spl6_41 | ~spl6_24 | ~spl6_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f259,f249,f168,f264,f261])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl6_24 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    spl6_39 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~m1_pre_topc(X1,sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | r1_tmap_1(sK1,sK0,sK2,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (~spl6_24 | ~spl6_39)),
% 0.20/0.50    inference(resolution,[],[f250,f169])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl6_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f168])).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) ) | ~spl6_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f249])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ~spl6_5 | ~spl6_11 | ~spl6_25 | spl6_38),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f257])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    $false | (~spl6_5 | ~spl6_11 | ~spl6_25 | spl6_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f256,f91])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | (~spl6_11 | ~spl6_25 | spl6_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f253,f115])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | (~spl6_25 | spl6_38)),
% 0.20/0.50    inference(resolution,[],[f247,f173])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl6_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    spl6_38 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ~spl6_38 | spl6_39 | ~spl6_10 | ~spl6_11 | ~spl6_37),
% 0.20/0.50    inference(avatar_split_clause,[],[f244,f240,f114,f110,f249,f246])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    spl6_10 <=> v1_tsep_1(sK3,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    spl6_37 <=> ! [X1,X0,X2] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X2)) | v2_struct_0(X2) | ~r2_hidden(X1,u1_struct_0(X0)) | ~m1_pre_topc(X2,sK1) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))) ) | (~spl6_10 | ~spl6_11 | ~spl6_37)),
% 0.20/0.50    inference(subsumption_resolution,[],[f243,f115])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))) ) | (~spl6_10 | ~spl6_37)),
% 0.20/0.50    inference(resolution,[],[f241,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    v1_tsep_1(sK3,sK1) | ~spl6_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f110])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_tsep_1(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(X2)) | v2_struct_0(X2) | ~r2_hidden(X1,u1_struct_0(X0)) | ~m1_pre_topc(X2,sK1) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))) ) | ~spl6_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f240])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    spl6_37 | ~spl6_23 | ~spl6_36),
% 0.20/0.50    inference(avatar_split_clause,[],[f238,f235,f164,f240])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    spl6_23 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl6_36 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X2)) | v2_struct_0(X2) | ~r2_hidden(X1,u1_struct_0(X0)) | ~m1_pre_topc(X2,sK1) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))) ) | (~spl6_23 | ~spl6_36)),
% 0.20/0.50    inference(resolution,[],[f236,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl6_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f164])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_pre_topc(X0,sK1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK1)) ) | ~spl6_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f235])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    spl6_36 | ~spl6_4 | ~spl6_5 | ~spl6_27 | ~spl6_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f233,f228,f180,f90,f86,f235])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl6_4 <=> v2_pre_topc(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    spl6_27 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    spl6_35 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK1)) ) | (~spl6_4 | ~spl6_5 | ~spl6_27 | ~spl6_35)),
% 0.20/0.50    inference(subsumption_resolution,[],[f232,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    v2_pre_topc(sK1) | ~spl6_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f86])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK1)) ) | (~spl6_5 | ~spl6_27 | ~spl6_35)),
% 0.20/0.50    inference(subsumption_resolution,[],[f231,f91])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_tsep_1(X1,sK1) | ~m1_pre_topc(X1,sK1)) ) | (~spl6_27 | ~spl6_35)),
% 0.20/0.50    inference(resolution,[],[f229,f181])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) ) | ~spl6_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f180])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | ~spl6_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f228])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    spl6_35 | spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14 | ~spl6_15 | ~spl6_34),
% 0.20/0.50    inference(avatar_split_clause,[],[f226,f216,f130,f126,f102,f98,f94,f90,f86,f82,f228])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl6_3 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl6_6 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl6_7 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl6_8 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl6_14 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl6_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl6_34 <=> ! [X1,X3,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~v3_pre_topc(X3,X1) | ~r2_hidden(X4,X3) | ~r1_tarski(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14 | ~spl6_15 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f225,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl6_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    v2_pre_topc(sK0) | ~spl6_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f98])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f223,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl6_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f94])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f91])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f87])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (spl6_3 | ~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f220,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ~v2_struct_0(sK1) | spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl6_8 | ~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f219,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl6_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f102])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X2,X1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl6_14 | ~spl6_34)),
% 0.20/0.50    inference(resolution,[],[f217,f127])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl6_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~v3_pre_topc(X3,X1) | ~r2_hidden(X4,X3) | ~r1_tarski(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl6_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f216])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    spl6_34 | ~spl6_2 | ~spl6_33),
% 0.20/0.50    inference(avatar_split_clause,[],[f214,f211,f78,f216])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl6_2 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    spl6_33 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~v3_pre_topc(X3,X1) | ~r2_hidden(X4,X3) | ~r1_tarski(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | (~spl6_2 | ~spl6_33)),
% 0.20/0.50    inference(resolution,[],[f212,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f78])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | ~spl6_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f211])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    spl6_33 | ~spl6_28 | ~spl6_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f205,f202,f186,f211])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    spl6_28 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    spl6_31 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | (~spl6_28 | ~spl6_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0)) ) | ~spl6_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f186])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | ~spl6_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f202])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    spl6_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f65,f202])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.50    inference(equality_resolution,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_18 | ~spl6_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    $false | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_18 | ~spl6_30)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f99,f83,f87,f91,f75,f79,f103,f95,f115,f123,f144,f127,f142,f131,f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl6_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f195])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    spl6_30 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl6_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f141])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl6_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl6_30 | ~spl6_28 | ~spl6_29),
% 0.20/0.50    inference(avatar_split_clause,[],[f193,f190,f186,f195])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl6_29 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | (~spl6_28 | ~spl6_29)),
% 0.20/0.50    inference(subsumption_resolution,[],[f191,f187])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl6_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl6_29),
% 0.20/0.50    inference(avatar_split_clause,[],[f63,f190])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.50    inference(equality_resolution,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    spl6_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f186])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    spl6_27),
% 0.20/0.50    inference(avatar_split_clause,[],[f72,f180])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f67,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl6_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f172])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl6_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f60,f168])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    spl6_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f62,f164])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    spl6_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f156])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl6_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f152])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    spl6_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f50,f148])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    spl6_17 | spl6_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f70,f141,f138])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.50    inference(forward_demodulation,[],[f32,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    sK4 = sK5),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ~spl6_17 | ~spl6_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f69,f141,f138])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.50    inference(forward_demodulation,[],[f33,f35])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % (16495)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl6_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f134])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl6_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f130])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    spl6_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f126])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl6_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f68,f122])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.50    inference(forward_demodulation,[],[f34,f35])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl6_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f114])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    m1_pre_topc(sK3,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    spl6_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f110])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    v1_tsep_1(sK3,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl6_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f48,f102])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl6_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f98])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ~spl6_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f94])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl6_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f90])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    l1_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl6_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f86])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v2_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ~spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f82])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl6_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f78])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~spl6_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f74])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~v2_struct_0(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16493)------------------------------
% 0.20/0.50  % (16493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16493)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16493)Memory used [KB]: 10874
% 0.20/0.50  % (16493)Time elapsed: 0.080 s
% 0.20/0.50  % (16493)------------------------------
% 0.20/0.50  % (16493)------------------------------
% 0.20/0.50  % (16494)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (16479)Success in time 0.139 s
%------------------------------------------------------------------------------
