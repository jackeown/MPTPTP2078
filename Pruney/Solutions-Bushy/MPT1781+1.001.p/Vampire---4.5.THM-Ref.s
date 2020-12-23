%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  289 ( 616 expanded)
%              Number of leaves         :   65 ( 297 expanded)
%              Depth                    :    9
%              Number of atoms          : 1742 (3787 expanded)
%              Number of equality atoms :  109 ( 261 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f93,f99,f104,f108,f113,f117,f122,f126,f130,f136,f140,f144,f149,f153,f157,f172,f179,f185,f193,f220,f227,f231,f235,f242,f249,f263,f266,f270,f282,f291,f305,f309,f319,f328,f333,f340,f348,f355,f362,f372,f379,f386,f394,f401,f408])).

fof(f408,plain,
    ( ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_47
    | ~ spl4_48
    | ~ spl4_59 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_47
    | ~ spl4_48
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f406,f323])).

fof(f323,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl4_48
  <=> sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f406,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) != k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_47
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f405,f318])).

fof(f318,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_47
  <=> sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f405,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f404,f103])).

fof(f103,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_9
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f404,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_5
    | ~ spl4_11
    | spl4_13
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f403,f112])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_5
    | spl4_13
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f402,f83])).

fof(f83,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f402,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | spl4_13
    | ~ spl4_59 ),
    inference(resolution,[],[f400,f121])).

fof(f121,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_13
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f400,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl4_59
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f401,plain,
    ( spl4_59
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f397,f392,f182,f86,f76,f399])).

fof(f76,plain,
    ( spl4_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f86,plain,
    ( spl4_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f182,plain,
    ( spl4_26
  <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f392,plain,
    ( spl4_58
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f397,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f396,f184])).

fof(f184,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f182])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f395,f78])).

fof(f78,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0) )
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(resolution,[],[f393,f88])).

fof(f88,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f393,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f392])).

fof(f394,plain,
    ( spl4_58
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f390,f384,f257,f253,f151,f96,f392])).

fof(f96,plain,
    ( spl4_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f151,plain,
    ( spl4_20
  <=> ! [X0] :
        ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f253,plain,
    ( spl4_39
  <=> v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f257,plain,
    ( spl4_40
  <=> v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f384,plain,
    ( spl4_57
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,sK3(sK0,sK0,X1,X2,X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,X2,X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) )
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f389,f98])).

fof(f98,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f388,f254])).

fof(f254,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f253])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_40
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f387,f258])).

fof(f258,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f257])).

fof(f387,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,X1,k3_struct_0(sK0),X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,k3_struct_0(sK0),X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_57 ),
    inference(resolution,[],[f385,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ l1_struct_0(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f385,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,sK3(sK0,sK0,X1,X2,X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,X2,X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f384])).

fof(f386,plain,
    ( spl4_57
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f382,f377,f71,f66,f61,f384])).

fof(f61,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f377,plain,
    ( spl4_56
  <=> ! [X1,X3,X0,X2] :
        ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3(sK0,X0,X2,X1,X3)) != k1_funct_1(X3,sK3(sK0,X0,X2,X1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X1,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f382,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,sK3(sK0,sK0,X1,X2,X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,X2,X0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f381,f63])).

fof(f63,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f381,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,sK3(sK0,sK0,X1,X2,X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,X2,X0))
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f380,f68])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f380,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,sK3(sK0,sK0,X1,X2,X0)) != k1_funct_1(X0,sK3(sK0,sK0,X1,X2,X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_3
    | ~ spl4_56 ),
    inference(resolution,[],[f378,f73])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f378,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3(sK0,X0,X2,X1,X3)) != k1_funct_1(X3,sK3(sK0,X0,X2,X1,X3))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X1,X2),X3) )
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f377])).

fof(f379,plain,
    ( spl4_56
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f375,f370,f71,f66,f61,f377])).

fof(f370,plain,
    ( spl4_55
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f375,plain,
    ( ! [X2,X0,X3,X1] :
        ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3(sK0,X0,X2,X1,X3)) != k1_funct_1(X3,sK3(sK0,X0,X2,X1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X1,X2),X3) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f374,f63])).

fof(f374,plain,
    ( ! [X2,X0,X3,X1] :
        ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3(sK0,X0,X2,X1,X3)) != k1_funct_1(X3,sK3(sK0,X0,X2,X1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X1,X2),X3)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f373,f68])).

fof(f373,plain,
    ( ! [X2,X0,X3,X1] :
        ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3(sK0,X0,X2,X1,X3)) != k1_funct_1(X3,sK3(sK0,X0,X2,X1,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X1,X2),X3)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_55 ),
    inference(resolution,[],[f371,f73])).

fof(f371,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f370])).

fof(f372,plain,(
    spl4_55 ),
    inference(avatar_split_clause,[],[f54,f370])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
                        & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f33])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
        & r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f362,plain,
    ( spl4_49
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f359,f353,f119,f110,f101,f81,f325])).

fof(f325,plain,
    ( spl4_49
  <=> r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f353,plain,
    ( spl4_53
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f359,plain,
    ( r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f358,f103])).

fof(f358,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_11
    | spl4_13
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f357,f121])).

fof(f357,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f356,f83])).

fof(f356,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl4_11
    | ~ spl4_53 ),
    inference(resolution,[],[f354,f112])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f353])).

fof(f355,plain,
    ( spl4_53
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f351,f346,f182,f86,f76,f353])).

fof(f346,plain,
    ( spl4_52
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f351,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f350,f184])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f349,f78])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0) )
    | ~ spl4_6
    | ~ spl4_52 ),
    inference(resolution,[],[f347,f88])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f346])).

fof(f348,plain,
    ( spl4_52
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f344,f338,f257,f253,f151,f96,f346])).

fof(f338,plain,
    ( spl4_51
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) )
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f343,f98])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f342,f254])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_40
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f341,f258])).

fof(f341,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_51 ),
    inference(resolution,[],[f339,f152])).

fof(f339,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl4_51
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f336,f331,f71,f66,f61,f338])).

fof(f331,plain,
    ( spl4_50
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f336,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(X1))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f335,f63])).

fof(f335,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(X1))
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f334,f68])).

fof(f334,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_3
    | ~ spl4_50 ),
    inference(resolution,[],[f332,f73])).

fof(f332,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | r2_hidden(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X1))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f331])).

fof(f333,plain,
    ( spl4_50
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f314,f233,f71,f66,f61,f331])).

fof(f233,plain,
    ( spl4_36
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f314,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f313,f63])).

fof(f313,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f312,f68])).

fof(f312,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(resolution,[],[f234,f73])).

fof(f234,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f328,plain,
    ( spl4_48
    | ~ spl4_49
    | ~ spl4_19
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f292,f288,f147,f325,f321])).

fof(f147,plain,
    ( spl4_19
  <=> ! [X3] :
        ( k1_funct_1(sK2,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f288,plain,
    ( spl4_44
  <=> m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f292,plain,
    ( ~ r2_hidden(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(sK2,sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_19
    | ~ spl4_44 ),
    inference(resolution,[],[f290,f148])).

fof(f148,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,u1_struct_0(sK1))
        | k1_funct_1(sK2,X3) = X3 )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f290,plain,
    ( m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f288])).

fof(f319,plain,
    ( spl4_47
    | ~ spl4_8
    | ~ spl4_34
    | ~ spl4_44
    | spl4_45
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f311,f302,f298,f288,f225,f96,f316])).

fof(f225,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0) = k1_funct_1(k3_struct_0(X1),X0)
        | v1_xboole_0(u1_struct_0(X1))
        | ~ l1_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f298,plain,
    ( spl4_45
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f302,plain,
    ( spl4_46
  <=> sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f311,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_8
    | ~ spl4_34
    | ~ spl4_44
    | spl4_45
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f310,f299])).

fof(f299,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f298])).

fof(f310,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_34
    | ~ spl4_44
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f295,f304])).

fof(f304,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f302])).

fof(f295,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k1_funct_1(k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_34
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f293,f98])).

fof(f293,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k1_funct_1(k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl4_34
    | ~ spl4_44 ),
    inference(resolution,[],[f290,f226])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0) = k1_funct_1(k3_struct_0(X1),X0)
        | v1_xboole_0(u1_struct_0(X1))
        | ~ l1_struct_0(X1) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f225])).

fof(f309,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f307,f63])).

fof(f307,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f306,f98])).

fof(f306,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(resolution,[],[f300,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f300,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f298])).

fof(f305,plain,
    ( spl4_45
    | spl4_46
    | ~ spl4_16
    | ~ spl4_21
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f296,f288,f155,f133,f302,f298])).

fof(f133,plain,
    ( spl4_16
  <=> k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f155,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( k1_funct_1(k6_relat_1(X0),X1) = X1
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f296,plain,
    ( sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(k3_struct_0(sK0),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_21
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f294,f135])).

fof(f135,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f294,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl4_21
    | ~ spl4_44 ),
    inference(resolution,[],[f290,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | k1_funct_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f291,plain,
    ( spl4_44
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f286,f280,f119,f110,f101,f81,f288])).

fof(f280,plain,
    ( spl4_43
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f286,plain,
    ( m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f285,f83])).

fof(f285,plain,
    ( m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f284,f121])).

fof(f284,plain,
    ( m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f283,f103])).

fof(f283,plain,
    ( m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_11
    | ~ spl4_43 ),
    inference(resolution,[],[f281,f112])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f280])).

fof(f282,plain,
    ( spl4_43
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f278,f261,f182,f86,f76,f280])).

fof(f261,plain,
    ( spl4_41
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | m1_subset_1(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f278,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f277,f184])).

fof(f277,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0)
        | m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f276,f78])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),X0)
        | m1_subset_1(sK3(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) )
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(resolution,[],[f262,f88])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | m1_subset_1(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f261])).

fof(f270,plain,
    ( ~ spl4_8
    | ~ spl4_17
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_17
    | spl4_40 ),
    inference(subsumption_resolution,[],[f268,f98])).

fof(f268,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_17
    | spl4_40 ),
    inference(resolution,[],[f259,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        | ~ l1_struct_0(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_17
  <=> ! [X0] :
        ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f259,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f257])).

fof(f266,plain,
    ( ~ spl4_8
    | ~ spl4_10
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_10
    | spl4_39 ),
    inference(subsumption_resolution,[],[f264,f98])).

fof(f264,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_10
    | spl4_39 ),
    inference(resolution,[],[f255,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( v1_funct_1(k3_struct_0(X0))
        | ~ l1_struct_0(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_10
  <=> ! [X0] :
        ( v1_funct_1(k3_struct_0(X0))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f255,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f253])).

fof(f263,plain,
    ( ~ spl4_39
    | ~ spl4_40
    | spl4_41
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f251,f247,f151,f96,f261,f257,f253])).

fof(f247,plain,
    ( spl4_38
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0) )
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f250,f98])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X1),X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl4_20
    | ~ spl4_38 ),
    inference(resolution,[],[f248,f152])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl4_38
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f245,f240,f71,f66,f61,f247])).

fof(f240,plain,
    ( spl4_37
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f244,f63])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f243,f68])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,sK0,X1,X2,X0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,X2,X1),X0) )
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(resolution,[],[f241,f73])).

fof(f241,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( spl4_37
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f238,f229,f71,f66,f61,f240])).

fof(f229,plain,
    ( spl4_35
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f238,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f237,f63])).

fof(f237,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f236,f68])).

fof(f236,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2,X3),u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,sK0,X2,X1),X3)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_35 ),
    inference(resolution,[],[f230,f73])).

fof(f230,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f229])).

fof(f235,plain,(
    spl4_36 ),
    inference(avatar_split_clause,[],[f53,f233])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f231,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f52,f229])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f227,plain,
    ( spl4_34
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f223,f218,f151,f138,f225])).

fof(f218,plain,
    ( spl4_33
  <=> ! [X3,X5,X4,X6] :
        ( ~ m1_subset_1(X3,X4)
        | ~ m1_subset_1(k3_struct_0(X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))
        | ~ v1_funct_2(k3_struct_0(X5),X4,X6)
        | k3_funct_2(X4,X6,k3_struct_0(X5),X3) = k1_funct_1(k3_struct_0(X5),X3)
        | v1_xboole_0(X4)
        | ~ l1_struct_0(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0) = k1_funct_1(k3_struct_0(X1),X0)
        | v1_xboole_0(u1_struct_0(X1))
        | ~ l1_struct_0(X1) )
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f222,f139])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0) = k1_funct_1(k3_struct_0(X1),X0)
        | v1_xboole_0(u1_struct_0(X1))
        | ~ l1_struct_0(X1) )
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0) = k1_funct_1(k3_struct_0(X1),X0)
        | v1_xboole_0(u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X1) )
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(resolution,[],[f219,f152])).

fof(f219,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ m1_subset_1(k3_struct_0(X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(k3_struct_0(X5),X4,X6)
        | k3_funct_2(X4,X6,k3_struct_0(X5),X3) = k1_funct_1(k3_struct_0(X5),X3)
        | v1_xboole_0(X4)
        | ~ l1_struct_0(X5) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( spl4_33
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f195,f191,f106,f218])).

fof(f191,plain,
    ( spl4_28
  <=> ! [X1,X3,X0,X2] :
        ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
        | ~ m1_subset_1(X3,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f195,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ m1_subset_1(X3,X4)
        | ~ m1_subset_1(k3_struct_0(X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))
        | ~ v1_funct_2(k3_struct_0(X5),X4,X6)
        | k3_funct_2(X4,X6,k3_struct_0(X5),X3) = k1_funct_1(k3_struct_0(X5),X3)
        | v1_xboole_0(X4)
        | ~ l1_struct_0(X5) )
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(resolution,[],[f192,f107])).

fof(f192,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
        | v1_xboole_0(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f58,f191])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f185,plain,
    ( spl4_26
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f180,f177,f86,f182])).

fof(f177,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f180,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(resolution,[],[f178,f88])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl4_25
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f175,f170,f71,f66,f61,f177])).

fof(f170,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f174,f63])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f173,f68])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f171,f73])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f51,f170])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

fof(f157,plain,
    ( spl4_21
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f145,f142,f124,f155])).

fof(f124,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f142,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k1_funct_1(k6_relat_1(X1),X0) = X0
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k6_relat_1(X0),X1) = X1
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(resolution,[],[f143,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k6_relat_1(X1),X0) = X0 )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f153,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f49,f151])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

fof(f149,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f43,f147])).

fof(f43,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK0),k4_tmap_1(sK0,X1),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(sK1))
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X2)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(sK1))
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
      & ! [X3] :
          ( k1_funct_1(sK2,X3) = X3
          | ~ r2_hidden(X3,u1_struct_0(sK1))
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f144,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f56,f142])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f140,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f48,f138])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f131,f128,f96,f133])).

fof(f128,plain,
    ( spl4_15
  <=> ! [X0] :
        ( k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f131,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(resolution,[],[f129,f98])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f59,f128])).

fof(f59,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f46,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

fof(f126,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f57,f124])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f122,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f117,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f113,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f42,f110])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f94,f91,f71,f96])).

fof(f91,plain,
    ( spl4_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f92,f73])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
