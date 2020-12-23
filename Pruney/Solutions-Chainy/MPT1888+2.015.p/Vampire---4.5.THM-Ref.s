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
% DateTime   : Thu Dec  3 13:22:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 450 expanded)
%              Number of leaves         :   54 ( 213 expanded)
%              Depth                    :   10
%              Number of atoms          :  917 (1867 expanded)
%              Number of equality atoms :   69 ( 197 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f104,f108,f116,f128,f133,f138,f142,f150,f163,f172,f179,f182,f190,f196,f204,f210,f214,f218,f244,f251,f255,f263,f270,f305,f313,f325,f360,f366,f373,f383,f426,f429])).

fof(f429,plain,
    ( ~ spl4_21
    | ~ spl4_37
    | spl4_58 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl4_21
    | ~ spl4_37
    | spl4_58 ),
    inference(subsumption_resolution,[],[f427,f171])).

fof(f171,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_21
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f427,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_37
    | spl4_58 ),
    inference(resolution,[],[f425,f269])).

fof(f269,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_37
  <=> ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f425,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl4_58
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f426,plain,
    ( ~ spl4_58
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_21
    | spl4_23
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f421,f381,f216,f201,f187,f169,f87,f77,f423])).

fof(f77,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f187,plain,
    ( spl4_23
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f201,plain,
    ( spl4_25
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f216,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f381,plain,
    ( spl4_53
  <=> ! [X0] :
        ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0)
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f421,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_21
    | spl4_23
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f420,f171])).

fof(f420,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_23
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f419,f79])).

fof(f79,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f419,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | spl4_23
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f418,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f418,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_23
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f417,f203])).

fof(f203,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f201])).

fof(f417,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_23
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f416,f189])).

fof(f189,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f187])).

fof(f416,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_53 ),
    inference(resolution,[],[f382,f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f216])).

fof(f382,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f381])).

fof(f383,plain,
    ( spl4_53
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f374,f370,f249,f381])).

fof(f249,plain,
    ( spl4_34
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
        | ~ v3_pre_topc(X1,X0)
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f370,plain,
    ( spl4_51
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0)
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(resolution,[],[f372,f250])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | r1_xboole_0(X1,k2_pre_topc(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f249])).

fof(f372,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f370])).

fof(f373,plain,
    ( spl4_51
    | ~ spl4_10
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f368,f363,f114,f370])).

fof(f114,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f363,plain,
    ( spl4_50
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f368,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_10
    | ~ spl4_50 ),
    inference(trivial_inequality_removal,[],[f367])).

fof(f367,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_10
    | ~ spl4_50 ),
    inference(superposition,[],[f115,f365])).

fof(f365,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f363])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f366,plain,
    ( spl4_50
    | ~ spl4_13
    | spl4_49 ),
    inference(avatar_split_clause,[],[f361,f357,f126,f363])).

fof(f126,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f357,plain,
    ( spl4_49
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f361,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl4_13
    | spl4_49 ),
    inference(resolution,[],[f359,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f359,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f357])).

fof(f360,plain,
    ( ~ spl4_49
    | ~ spl4_5
    | ~ spl4_20
    | spl4_26
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f355,f323,f207,f160,f92,f357])).

fof(f92,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( spl4_20
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f207,plain,
    ( spl4_26
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f323,plain,
    ( spl4_45
  <=> ! [X1] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f355,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl4_5
    | ~ spl4_20
    | spl4_26
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f354,f162])).

fof(f162,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f354,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_5
    | ~ spl4_20
    | spl4_26
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f353,f209])).

fof(f209,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f353,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f351,f162])).

fof(f351,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_5
    | ~ spl4_45 ),
    inference(resolution,[],[f324,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f324,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f323])).

fof(f325,plain,
    ( spl4_45
    | ~ spl4_6
    | ~ spl4_24
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f317,f311,f193,f97,f323])).

fof(f97,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f193,plain,
    ( spl4_24
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f311,plain,
    ( spl4_43
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f317,plain,
    ( ! [X1] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) )
    | ~ spl4_6
    | ~ spl4_24
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f315,f195])).

fof(f195,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) )
    | ~ spl4_6
    | ~ spl4_43 ),
    inference(resolution,[],[f312,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f311])).

fof(f313,plain,
    ( spl4_43
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f309,f303,f87,f82,f77,f72,f311])).

fof(f72,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,
    ( spl4_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f303,plain,
    ( spl4_42
  <=> ! [X1,X0,X2] :
        ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f308,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f307,f79])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f306,f89])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_42 ),
    inference(resolution,[],[f304,f84])).

fof(f84,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f304,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_tdlat_3(X0)
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,(
    spl4_42 ),
    inference(avatar_split_clause,[],[f56,f303])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f270,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f266,f261,f216,f87,f268])).

fof(f261,plain,
    ( spl4_36
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f266,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f265,f89])).

fof(f265,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_28
    | ~ spl4_36 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_28
    | ~ spl4_36 ),
    inference(resolution,[],[f262,f217])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl4_36
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f259,f253,f212,f87,f77,f261])).

fof(f212,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f253,plain,
    ( spl4_35
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f258,f79])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_4
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f257,f89])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(resolution,[],[f254,f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f212])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl4_35
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f247,f242,f87,f82,f77,f253])).

fof(f242,plain,
    ( spl4_33
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f246,f79])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f245,f89])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_3
    | ~ spl4_33 ),
    inference(resolution,[],[f243,f84])).

fof(f243,plain,
    ( ! [X2,X0] :
        ( ~ v3_tdlat_3(X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f242])).

fof(f251,plain,(
    spl4_34 ),
    inference(avatar_split_clause,[],[f61,f249])).

% (16250)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f244,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f57,f242])).

fof(f57,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f218,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f65,f216])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f214,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f64,f212])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f210,plain,
    ( ~ spl4_26
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f185,f160,f156,f148,f135,f97,f207])).

fof(f135,plain,
    ( spl4_15
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f148,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f156,plain,
    ( spl4_19
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f185,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f164,f183])).

fof(f183,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_6
    | ~ spl4_18
    | spl4_19 ),
    inference(subsumption_resolution,[],[f152,f157])).

fof(f157,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f152,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f149,f99])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f164,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl4_15
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f137,f162])).

fof(f137,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f204,plain,
    ( spl4_25
    | ~ spl4_6
    | ~ spl4_16
    | spl4_19
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f199,f193,f156,f140,f97,f201])).

fof(f140,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f199,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_16
    | spl4_19
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f198,f157])).

fof(f198,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f197,f99])).

fof(f197,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(superposition,[],[f141,f195])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f196,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f183,f156,f148,f97,f193])).

fof(f190,plain,
    ( ~ spl4_23
    | ~ spl4_6
    | spl4_14
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f184,f160,f156,f148,f130,f97,f187])).

fof(f130,plain,
    ( spl4_14
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f184,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_6
    | spl4_14
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f165,f183])).

fof(f165,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_14
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f132,f162])).

fof(f132,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f182,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | spl4_22 ),
    inference(subsumption_resolution,[],[f180,f89])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_22 ),
    inference(resolution,[],[f178,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f178,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f179,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f174,f156,f106,f72,f176])).

fof(f106,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f174,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_1
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f173,f74])).

fof(f173,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(resolution,[],[f158,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f158,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f172,plain,
    ( spl4_19
    | spl4_21
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f167,f160,f140,f92,f169,f156])).

fof(f167,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f166,f94])).

fof(f166,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(superposition,[],[f141,f162])).

fof(f163,plain,
    ( spl4_19
    | spl4_20
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f151,f148,f92,f160,f156])).

fof(f151,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(resolution,[],[f149,f94])).

fof(f150,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f69,f148])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f142,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f63,f140])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f138,plain,(
    ~ spl4_15 ),
    inference(avatar_split_clause,[],[f52,f135])).

fof(f52,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f133,plain,(
    ~ spl4_14 ),
    inference(avatar_split_clause,[],[f51,f130])).

fof(f51,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f70,f126])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f116,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f67,f114])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f108,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f106])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f54,f102])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f100,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f50,f97])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f48,f87])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f47,f82])).

fof(f47,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16251)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (16248)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (16246)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16249)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (16243)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (16259)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (16255)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (16253)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (16247)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (16249)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f104,f108,f116,f128,f133,f138,f142,f150,f163,f172,f179,f182,f190,f196,f204,f210,f214,f218,f244,f251,f255,f263,f270,f305,f313,f325,f360,f366,f373,f383,f426,f429])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    ~spl4_21 | ~spl4_37 | spl4_58),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    $false | (~spl4_21 | ~spl4_37 | spl4_58)),
% 0.21/0.49    inference(subsumption_resolution,[],[f427,f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl4_21 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_37 | spl4_58)),
% 0.21/0.49    inference(resolution,[],[f425,f269])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f268])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    spl4_37 <=> ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | spl4_58),
% 0.21/0.49    inference(avatar_component_clause,[],[f423])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    spl4_58 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    ~spl4_58 | ~spl4_2 | ~spl4_4 | ~spl4_21 | spl4_23 | ~spl4_25 | ~spl4_28 | ~spl4_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f421,f381,f216,f201,f187,f169,f87,f77,f423])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl4_4 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl4_23 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl4_25 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl4_28 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl4_53 <=> ! [X0] : (~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl4_2 | ~spl4_4 | ~spl4_21 | spl4_23 | ~spl4_25 | ~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f420,f171])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_4 | spl4_23 | ~spl4_25 | ~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f419,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | spl4_23 | ~spl4_25 | ~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f418,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f418,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_23 | ~spl4_25 | ~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f417,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_23 | ~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f416,f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f187])).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f415])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_28 | ~spl4_53)),
% 0.21/0.49    inference(resolution,[],[f382,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f216])).
% 0.21/0.49  fof(f382,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f381])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl4_53 | ~spl4_34 | ~spl4_51),
% 0.21/0.49    inference(avatar_split_clause,[],[f374,f370,f249,f381])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    spl4_34 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    spl4_51 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),X0) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(X0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl4_34 | ~spl4_51)),
% 0.21/0.49    inference(resolution,[],[f372,f250])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f249])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~spl4_51),
% 0.21/0.49    inference(avatar_component_clause,[],[f370])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    spl4_51 | ~spl4_10 | ~spl4_50),
% 0.21/0.49    inference(avatar_split_clause,[],[f368,f363,f114,f370])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    spl4_50 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (~spl4_10 | ~spl4_50)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f367])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (~spl4_10 | ~spl4_50)),
% 0.21/0.49    inference(superposition,[],[f115,f365])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~spl4_50),
% 0.21/0.49    inference(avatar_component_clause,[],[f363])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    spl4_50 | ~spl4_13 | spl4_49),
% 0.21/0.49    inference(avatar_split_clause,[],[f361,f357,f126,f363])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl4_13 <=> ! [X1,X0] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    spl4_49 <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k4_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (~spl4_13 | spl4_49)),
% 0.21/0.49    inference(resolution,[],[f359,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0) ) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl4_49),
% 0.21/0.49    inference(avatar_component_clause,[],[f357])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    ~spl4_49 | ~spl4_5 | ~spl4_20 | spl4_26 | ~spl4_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f355,f323,f207,f160,f92,f357])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl4_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl4_20 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    spl4_26 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    spl4_45 <=> ! [X1] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl4_5 | ~spl4_20 | spl4_26 | ~spl4_45)),
% 0.21/0.49    inference(forward_demodulation,[],[f354,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl4_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (~spl4_5 | ~spl4_20 | spl4_26 | ~spl4_45)),
% 0.21/0.49    inference(subsumption_resolution,[],[f353,f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | spl4_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f207])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (~spl4_5 | ~spl4_20 | ~spl4_45)),
% 0.21/0.49    inference(forward_demodulation,[],[f351,f162])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (~spl4_5 | ~spl4_45)),
% 0.21/0.49    inference(resolution,[],[f324,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))) ) | ~spl4_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f323])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    spl4_45 | ~spl4_6 | ~spl4_24 | ~spl4_43),
% 0.21/0.49    inference(avatar_split_clause,[],[f317,f311,f193,f97,f323])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl4_24 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    spl4_43 <=> ! [X1,X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ( ! [X1] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))) ) | (~spl4_6 | ~spl4_24 | ~spl4_43)),
% 0.21/0.49    inference(forward_demodulation,[],[f315,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f193])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) | (~spl4_6 | ~spl4_43)),
% 0.21/0.49    inference(resolution,[],[f312,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | ~spl4_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f311])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    spl4_43 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f309,f303,f87,f82,f77,f72,f311])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_3 <=> v3_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    spl4_42 <=> ! [X1,X0,X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f79])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f306,f89])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_42)),
% 0.21/0.49    inference(resolution,[],[f304,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v3_tdlat_3(sK0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f303])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f303])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl4_37 | ~spl4_4 | ~spl4_28 | ~spl4_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f266,f261,f216,f87,f268])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    spl4_36 <=> ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_4 | ~spl4_28 | ~spl4_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f89])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl4_28 | ~spl4_36)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f264])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl4_28 | ~spl4_36)),
% 0.21/0.49    inference(resolution,[],[f262,f217])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f261])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    spl4_36 | ~spl4_2 | ~spl4_4 | ~spl4_27 | ~spl4_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f259,f253,f212,f87,f77,f261])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl4_27 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl4_35 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_2 | ~spl4_4 | ~spl4_27 | ~spl4_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f79])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl4_4 | ~spl4_27 | ~spl4_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f89])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_27 | ~spl4_35)),
% 0.21/0.49    inference(resolution,[],[f254,f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f212])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | ~spl4_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl4_35 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f247,f242,f87,f82,f77,f253])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl4_33 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_33)),
% 0.21/0.49    inference(subsumption_resolution,[],[f246,f79])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_33)),
% 0.21/0.49    inference(subsumption_resolution,[],[f245,f89])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_3 | ~spl4_33)),
% 0.21/0.49    inference(resolution,[],[f243,f84])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl4_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f249])).
% 0.21/0.49  % (16250)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f242])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl4_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f216])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl4_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f212])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~spl4_26 | ~spl4_6 | spl4_15 | ~spl4_18 | spl4_19 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f185,f160,f156,f148,f135,f97,f207])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl4_15 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl4_18 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl4_19 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl4_6 | spl4_15 | ~spl4_18 | spl4_19 | ~spl4_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f164,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl4_6 | ~spl4_18 | spl4_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_18)),
% 0.21/0.49    inference(resolution,[],[f149,f99])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (spl4_15 | ~spl4_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f137,f162])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl4_25 | ~spl4_6 | ~spl4_16 | spl4_19 | ~spl4_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f199,f193,f156,f140,f97,f201])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl4_16 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_6 | ~spl4_16 | spl4_19 | ~spl4_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f157])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_16 | ~spl4_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f197,f99])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_16 | ~spl4_24)),
% 0.21/0.49    inference(superposition,[],[f141,f195])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl4_24 | ~spl4_6 | ~spl4_18 | spl4_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f183,f156,f148,f97,f193])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~spl4_23 | ~spl4_6 | spl4_14 | ~spl4_18 | spl4_19 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f160,f156,f148,f130,f97,f187])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl4_14 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_6 | spl4_14 | ~spl4_18 | spl4_19 | ~spl4_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f165,f183])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl4_14 | ~spl4_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f132,f162])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ~spl4_4 | ~spl4_7 | spl4_22),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    $false | (~spl4_4 | ~spl4_7 | spl4_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f180,f89])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl4_7 | spl4_22)),
% 0.21/0.49    inference(resolution,[],[f178,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl4_7 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | spl4_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl4_22 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~spl4_22 | spl4_1 | ~spl4_8 | ~spl4_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f156,f106,f72,f176])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl4_8 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | (spl4_1 | ~spl4_8 | ~spl4_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f74])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl4_8 | ~spl4_19)),
% 0.21/0.49    inference(resolution,[],[f158,f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl4_19 | spl4_21 | ~spl4_5 | ~spl4_16 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f160,f140,f92,f169,f156])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_5 | ~spl4_16 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f166,f94])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_16 | ~spl4_20)),
% 0.21/0.49    inference(superposition,[],[f141,f162])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl4_19 | spl4_20 | ~spl4_5 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f148,f92,f160,f156])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_5 | ~spl4_18)),
% 0.21/0.49    inference(resolution,[],[f149,f94])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f148])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f62,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f140])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f135])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f38,f37,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~spl4_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f130])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f126])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f68,f53])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X1,X0) => k4_xboole_0(X0,k1_tarski(X1)) = X0)),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f114])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f106])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f102])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f97])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f92])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f87])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f82])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v3_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f77])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f72])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (16249)------------------------------
% 0.21/0.49  % (16249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16249)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (16249)Memory used [KB]: 6396
% 0.21/0.49  % (16249)Time elapsed: 0.015 s
% 0.21/0.49  % (16249)------------------------------
% 0.21/0.49  % (16249)------------------------------
% 0.21/0.49  % (16241)Success in time 0.133 s
%------------------------------------------------------------------------------
