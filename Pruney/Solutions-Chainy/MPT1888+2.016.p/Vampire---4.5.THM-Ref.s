%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  249 ( 484 expanded)
%              Number of leaves         :   61 ( 232 expanded)
%              Depth                    :    8
%              Number of atoms          :  962 (1947 expanded)
%              Number of equality atoms :   78 ( 208 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f803,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f107,f111,f115,f119,f124,f138,f143,f147,f155,f168,f177,f184,f187,f195,f201,f209,f215,f219,f255,f260,f277,f304,f308,f314,f327,f331,f345,f353,f461,f479,f487,f497,f512,f542,f775,f783,f796,f802])).

fof(f802,plain,
    ( ~ spl4_8
    | spl4_23
    | ~ spl4_63 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | ~ spl4_8
    | spl4_23
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f798,f194])).

fof(f194,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_23
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f798,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_8
    | ~ spl4_63 ),
    inference(resolution,[],[f511,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f511,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl4_63
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f796,plain,
    ( ~ spl4_62
    | ~ spl4_6
    | ~ spl4_24
    | spl4_26
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f795,f781,f212,f198,f100,f505])).

fof(f505,plain,
    ( spl4_62
  <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f100,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f198,plain,
    ( spl4_24
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f212,plain,
    ( spl4_26
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f781,plain,
    ( spl4_81
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f795,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_6
    | ~ spl4_24
    | spl4_26
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f794,f214])).

fof(f214,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f794,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl4_6
    | ~ spl4_24
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f789,f102])).

fof(f102,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f789,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl4_24
    | ~ spl4_81 ),
    inference(superposition,[],[f782,f200])).

fof(f200,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f198])).

fof(f782,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f781])).

fof(f783,plain,
    ( spl4_81
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f778,f773,f165,f95,f781])).

fof(f95,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f165,plain,
    ( spl4_20
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f773,plain,
    ( spl4_80
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f778,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f776,f167])).

fof(f167,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f776,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl4_5
    | ~ spl4_80 ),
    inference(resolution,[],[f774,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f774,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f773])).

fof(f775,plain,
    ( spl4_80
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f771,f540,f90,f85,f80,f75,f773])).

fof(f75,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f85,plain,
    ( spl4_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f90,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f540,plain,
    ( spl4_69
  <=> ! [X1,X0,X2] :
        ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f771,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f770,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f770,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f769,f82])).

fof(f82,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f769,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f768,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f768,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_69 ),
    inference(resolution,[],[f541,f87])).

fof(f87,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f541,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_tdlat_3(X0)
        | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f540])).

fof(f542,plain,(
    spl4_69 ),
    inference(avatar_split_clause,[],[f60,f540])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f512,plain,
    ( spl4_62
    | spl4_63
    | ~ spl4_21
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f502,f495,f174,f509,f505])).

fof(f174,plain,
    ( spl4_21
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f495,plain,
    ( spl4_60
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f502,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_21
    | ~ spl4_60 ),
    inference(resolution,[],[f496,f176])).

fof(f176,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f495])).

fof(f497,plain,
    ( spl4_60
    | ~ spl4_11
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f492,f485,f122,f495])).

fof(f122,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k2_tarski(X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f485,plain,
    ( spl4_58
  <=> ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f492,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl4_11
    | ~ spl4_58 ),
    inference(resolution,[],[f486,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,k2_tarski(X0,X0))
        | r2_hidden(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f486,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f485])).

fof(f487,plain,
    ( spl4_58
    | ~ spl4_43
    | ~ spl4_46
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f482,f477,f350,f320,f485])).

fof(f320,plain,
    ( spl4_43
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f350,plain,
    ( spl4_46
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f477,plain,
    ( spl4_57
  <=> ! [X1,X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl4_43
    | ~ spl4_46
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f480,f321])).

fof(f321,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f320])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl4_46
    | ~ spl4_57 ),
    inference(resolution,[],[f478,f352])).

fof(f352,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f350])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f477])).

fof(f479,plain,
    ( spl4_57
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f475,f459,f90,f80,f477])).

fof(f459,plain,
    ( spl4_55
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
        | ~ v3_pre_topc(X1,X0)
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f474,f92])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r1_xboole_0(X0,k2_pre_topc(sK0,X1)) )
    | ~ spl4_2
    | ~ spl4_55 ),
    inference(resolution,[],[f460,f82])).

fof(f460,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_pre_topc(X1,X0)
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | r1_xboole_0(X1,k2_pre_topc(X0,X2)) )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f459])).

fof(f461,plain,(
    spl4_55 ),
    inference(avatar_split_clause,[],[f65,f459])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f353,plain,
    ( spl4_46
    | ~ spl4_43
    | ~ spl4_44
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f348,f343,f324,f320,f350])).

fof(f324,plain,
    ( spl4_44
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f343,plain,
    ( spl4_45
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f348,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl4_43
    | ~ spl4_44
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f347,f321])).

fof(f347,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl4_44
    | ~ spl4_45 ),
    inference(resolution,[],[f344,f326])).

fof(f326,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f324])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f343])).

fof(f345,plain,
    ( spl4_45
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f341,f306,f90,f85,f80,f343])).

fof(f306,plain,
    ( spl4_41
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f340,f82])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f339,f92])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_3
    | ~ spl4_41 ),
    inference(resolution,[],[f307,f87])).

fof(f307,plain,
    ( ! [X2,X0] :
        ( ~ v3_tdlat_3(X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f306])).

fof(f331,plain,
    ( ~ spl4_4
    | ~ spl4_25
    | ~ spl4_27
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_25
    | ~ spl4_27
    | spl4_43 ),
    inference(subsumption_resolution,[],[f329,f92])).

fof(f329,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_25
    | ~ spl4_27
    | spl4_43 ),
    inference(subsumption_resolution,[],[f328,f208])).

fof(f208,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_25
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f328,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_27
    | spl4_43 ),
    inference(resolution,[],[f322,f218])).

% (6797)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f218,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f322,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f320])).

fof(f327,plain,
    ( ~ spl4_43
    | spl4_44
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f317,f312,f274,f324,f320])).

fof(f274,plain,
    ( spl4_37
  <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f312,plain,
    ( spl4_42
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f317,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(superposition,[],[f313,f276])).

fof(f276,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f274])).

fof(f313,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f310,f302,f90,f80,f312])).

fof(f302,plain,
    ( spl4_40
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f310,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f309,f92])).

fof(f309,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(resolution,[],[f303,f82])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f302])).

fof(f308,plain,(
    spl4_41 ),
    inference(avatar_split_clause,[],[f61,f306])).

fof(f61,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f304,plain,(
    spl4_40 ),
    inference(avatar_split_clause,[],[f58,f302])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f277,plain,
    ( spl4_37
    | ~ spl4_25
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f262,f258,f206,f274])).

fof(f258,plain,
    ( spl4_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f262,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_25
    | ~ spl4_35 ),
    inference(resolution,[],[f259,f208])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl4_35
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f256,f253,f90,f258])).

fof(f253,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(resolution,[],[f254,f92])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,(
    spl4_34 ),
    inference(avatar_split_clause,[],[f71,f253])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f219,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f70,f217])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f215,plain,
    ( ~ spl4_26
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f190,f165,f161,f153,f140,f100,f212])).

fof(f140,plain,
    ( spl4_15
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f153,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f161,plain,
    ( spl4_19
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f190,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f169,f188])).

fof(f188,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_6
    | ~ spl4_18
    | spl4_19 ),
    inference(subsumption_resolution,[],[f157,f162])).

fof(f162,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f157,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f154,f102])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f169,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl4_15
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f142,f167])).

fof(f142,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f209,plain,
    ( spl4_25
    | ~ spl4_6
    | ~ spl4_16
    | spl4_19
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f204,f198,f161,f145,f100,f206])).

fof(f145,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f204,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_16
    | spl4_19
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f203,f162])).

fof(f203,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f202,f102])).

fof(f202,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(superposition,[],[f146,f200])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f201,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f188,f161,f153,f100,f198])).

fof(f195,plain,
    ( ~ spl4_23
    | ~ spl4_6
    | spl4_14
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f189,f165,f161,f153,f135,f100,f192])).

fof(f135,plain,
    ( spl4_14
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f189,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_6
    | spl4_14
    | ~ spl4_18
    | spl4_19
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f170,f188])).

fof(f170,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_14
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f137,f167])).

fof(f137,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f187,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | spl4_22 ),
    inference(subsumption_resolution,[],[f185,f92])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_22 ),
    inference(resolution,[],[f183,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f183,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f184,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f179,f161,f113,f75,f181])).

fof(f113,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f179,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f178,f77])).

fof(f178,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(resolution,[],[f163,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f163,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f177,plain,
    ( spl4_19
    | spl4_21
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f172,f165,f145,f95,f174,f161])).

fof(f172,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f171,f97])).

fof(f171,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(superposition,[],[f146,f167])).

fof(f168,plain,
    ( spl4_19
    | spl4_20
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f156,f153,f95,f165,f161])).

fof(f156,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(resolution,[],[f154,f97])).

fof(f155,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f73,f153])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f55])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f147,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f69,f145])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f143,plain,(
    ~ spl4_15 ),
    inference(avatar_split_clause,[],[f54,f140])).

fof(f54,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f138,plain,(
    ~ spl4_14 ),
    inference(avatar_split_clause,[],[f53,f135])).

fof(f53,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,
    ( spl4_11
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f120,f117,f109,f122])).

fof(f117,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(k2_tarski(X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | r1_xboole_0(X1,k2_tarski(X0,X0)) )
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f118,f110])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_tarski(X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f72,f117])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f55])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f115,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f59,f113])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f111,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f67,f109])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f107,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f103,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f50,f90])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f49,f85])).

fof(f49,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f47,f75])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:29:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (6799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.42  % (6791)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % (6791)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f803,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f107,f111,f115,f119,f124,f138,f143,f147,f155,f168,f177,f184,f187,f195,f201,f209,f215,f219,f255,f260,f277,f304,f308,f314,f327,f331,f345,f353,f461,f479,f487,f497,f512,f542,f775,f783,f796,f802])).
% 0.20/0.44  fof(f802,plain,(
% 0.20/0.44    ~spl4_8 | spl4_23 | ~spl4_63),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f801])).
% 0.20/0.44  fof(f801,plain,(
% 0.20/0.44    $false | (~spl4_8 | spl4_23 | ~spl4_63)),
% 0.20/0.44    inference(subsumption_resolution,[],[f798,f194])).
% 0.20/0.44  fof(f194,plain,(
% 0.20/0.44    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_23),
% 0.20/0.44    inference(avatar_component_clause,[],[f192])).
% 0.20/0.44  fof(f192,plain,(
% 0.20/0.44    spl4_23 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.44  fof(f798,plain,(
% 0.20/0.44    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_8 | ~spl4_63)),
% 0.20/0.44    inference(resolution,[],[f511,f110])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f109])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.44  fof(f511,plain,(
% 0.20/0.44    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl4_63),
% 0.20/0.44    inference(avatar_component_clause,[],[f509])).
% 0.20/0.44  fof(f509,plain,(
% 0.20/0.44    spl4_63 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.20/0.44  fof(f796,plain,(
% 0.20/0.44    ~spl4_62 | ~spl4_6 | ~spl4_24 | spl4_26 | ~spl4_81),
% 0.20/0.44    inference(avatar_split_clause,[],[f795,f781,f212,f198,f100,f505])).
% 0.20/0.44  fof(f505,plain,(
% 0.20/0.44    spl4_62 <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    spl4_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f198,plain,(
% 0.20/0.44    spl4_24 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.44  fof(f212,plain,(
% 0.20/0.44    spl4_26 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.44  fof(f781,plain,(
% 0.20/0.44    spl4_81 <=> ! [X0] : (k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.20/0.44  fof(f795,plain,(
% 0.20/0.44    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_6 | ~spl4_24 | spl4_26 | ~spl4_81)),
% 0.20/0.44    inference(subsumption_resolution,[],[f794,f214])).
% 0.20/0.44  fof(f214,plain,(
% 0.20/0.44    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | spl4_26),
% 0.20/0.44    inference(avatar_component_clause,[],[f212])).
% 0.20/0.44  fof(f794,plain,(
% 0.20/0.44    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl4_6 | ~spl4_24 | ~spl4_81)),
% 0.20/0.44    inference(subsumption_resolution,[],[f789,f102])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f100])).
% 0.20/0.44  fof(f789,plain,(
% 0.20/0.44    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl4_24 | ~spl4_81)),
% 0.20/0.44    inference(superposition,[],[f782,f200])).
% 0.20/0.44  fof(f200,plain,(
% 0.20/0.44    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_24),
% 0.20/0.44    inference(avatar_component_clause,[],[f198])).
% 0.20/0.44  fof(f782,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | ~spl4_81),
% 0.20/0.44    inference(avatar_component_clause,[],[f781])).
% 0.20/0.44  fof(f783,plain,(
% 0.20/0.44    spl4_81 | ~spl4_5 | ~spl4_20 | ~spl4_80),
% 0.20/0.44    inference(avatar_split_clause,[],[f778,f773,f165,f95,f781])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    spl4_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.44  fof(f165,plain,(
% 0.20/0.44    spl4_20 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.44  fof(f773,plain,(
% 0.20/0.44    spl4_80 <=> ! [X1,X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 0.20/0.44  fof(f778,plain,(
% 0.20/0.44    ( ! [X0] : (k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))) ) | (~spl4_5 | ~spl4_20 | ~spl4_80)),
% 0.20/0.44    inference(forward_demodulation,[],[f776,f167])).
% 0.20/0.44  fof(f167,plain,(
% 0.20/0.44    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl4_20),
% 0.20/0.44    inference(avatar_component_clause,[],[f165])).
% 0.20/0.44  fof(f776,plain,(
% 0.20/0.44    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (~spl4_5 | ~spl4_80)),
% 0.20/0.44    inference(resolution,[],[f774,f97])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f95])).
% 0.20/0.44  fof(f774,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | ~spl4_80),
% 0.20/0.44    inference(avatar_component_clause,[],[f773])).
% 0.20/0.44  fof(f775,plain,(
% 0.20/0.44    spl4_80 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_69),
% 0.20/0.44    inference(avatar_split_clause,[],[f771,f540,f90,f85,f80,f75,f773])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    spl4_1 <=> v2_struct_0(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    spl4_2 <=> v2_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    spl4_3 <=> v3_tdlat_3(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f540,plain,(
% 0.20/0.44    spl4_69 <=> ! [X1,X0,X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.20/0.44  fof(f771,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_69)),
% 0.20/0.44    inference(subsumption_resolution,[],[f770,f77])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    ~v2_struct_0(sK0) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f75])).
% 0.20/0.44  fof(f770,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_69)),
% 0.20/0.44    inference(subsumption_resolution,[],[f769,f82])).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    v2_pre_topc(sK0) | ~spl4_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f80])).
% 0.20/0.44  fof(f769,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_69)),
% 0.20/0.44    inference(subsumption_resolution,[],[f768,f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f90])).
% 0.20/0.44  fof(f768,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_69)),
% 0.20/0.44    inference(resolution,[],[f541,f87])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    v3_tdlat_3(sK0) | ~spl4_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f85])).
% 0.20/0.44  fof(f541,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_69),
% 0.20/0.44    inference(avatar_component_clause,[],[f540])).
% 0.20/0.44  fof(f542,plain,(
% 0.20/0.44    spl4_69),
% 0.20/0.44    inference(avatar_split_clause,[],[f60,f540])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 0.20/0.44  fof(f512,plain,(
% 0.20/0.44    spl4_62 | spl4_63 | ~spl4_21 | ~spl4_60),
% 0.20/0.44    inference(avatar_split_clause,[],[f502,f495,f174,f509,f505])).
% 0.20/0.44  fof(f174,plain,(
% 0.20/0.44    spl4_21 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.44  fof(f495,plain,(
% 0.20/0.44    spl4_60 <=> ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0))) | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.20/0.44  fof(f502,plain,(
% 0.20/0.44    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_21 | ~spl4_60)),
% 0.20/0.44    inference(resolution,[],[f496,f176])).
% 0.20/0.44  fof(f176,plain,(
% 0.20/0.44    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.20/0.44    inference(avatar_component_clause,[],[f174])).
% 0.20/0.44  fof(f496,plain,(
% 0.20/0.44    ( ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0))) | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | ~spl4_60),
% 0.20/0.44    inference(avatar_component_clause,[],[f495])).
% 0.20/0.44  fof(f497,plain,(
% 0.20/0.44    spl4_60 | ~spl4_11 | ~spl4_58),
% 0.20/0.44    inference(avatar_split_clause,[],[f492,f485,f122,f495])).
% 0.20/0.44  fof(f122,plain,(
% 0.20/0.44    spl4_11 <=> ! [X1,X0] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.44  fof(f485,plain,(
% 0.20/0.44    spl4_58 <=> ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.20/0.44  fof(f492,plain,(
% 0.20/0.44    ( ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(X0,X0))) | r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))) ) | (~spl4_11 | ~spl4_58)),
% 0.20/0.44    inference(resolution,[],[f486,f123])).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(X1,k2_tarski(X0,X0)) | r2_hidden(X0,X1)) ) | ~spl4_11),
% 0.20/0.44    inference(avatar_component_clause,[],[f122])).
% 0.20/0.44  fof(f486,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | ~spl4_58),
% 0.20/0.44    inference(avatar_component_clause,[],[f485])).
% 0.20/0.44  fof(f487,plain,(
% 0.20/0.44    spl4_58 | ~spl4_43 | ~spl4_46 | ~spl4_57),
% 0.20/0.44    inference(avatar_split_clause,[],[f482,f477,f350,f320,f485])).
% 0.20/0.44  fof(f320,plain,(
% 0.20/0.44    spl4_43 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.20/0.44  fof(f350,plain,(
% 0.20/0.44    spl4_46 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.20/0.44  fof(f477,plain,(
% 0.20/0.44    spl4_57 <=> ! [X1,X0] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.44  fof(f482,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | (~spl4_43 | ~spl4_46 | ~spl4_57)),
% 0.20/0.44    inference(subsumption_resolution,[],[f480,f321])).
% 0.20/0.44  fof(f321,plain,(
% 0.20/0.44    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_43),
% 0.20/0.44    inference(avatar_component_clause,[],[f320])).
% 0.20/0.44  fof(f480,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,X0))) ) | (~spl4_46 | ~spl4_57)),
% 0.20/0.44    inference(resolution,[],[f478,f352])).
% 0.20/0.44  fof(f352,plain,(
% 0.20/0.44    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl4_46),
% 0.20/0.44    inference(avatar_component_clause,[],[f350])).
% 0.20/0.44  fof(f478,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | ~spl4_57),
% 0.20/0.44    inference(avatar_component_clause,[],[f477])).
% 0.20/0.44  fof(f479,plain,(
% 0.20/0.44    spl4_57 | ~spl4_2 | ~spl4_4 | ~spl4_55),
% 0.20/0.44    inference(avatar_split_clause,[],[f475,f459,f90,f80,f477])).
% 0.20/0.44  fof(f459,plain,(
% 0.20/0.44    spl4_55 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.20/0.44  fof(f475,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | (~spl4_2 | ~spl4_4 | ~spl4_55)),
% 0.20/0.44    inference(subsumption_resolution,[],[f474,f92])).
% 0.20/0.44  fof(f474,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_xboole_0(X0,k2_pre_topc(sK0,X1))) ) | (~spl4_2 | ~spl4_55)),
% 0.20/0.44    inference(resolution,[],[f460,f82])).
% 0.20/0.44  fof(f460,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2))) ) | ~spl4_55),
% 0.20/0.44    inference(avatar_component_clause,[],[f459])).
% 0.20/0.44  fof(f461,plain,(
% 0.20/0.44    spl4_55),
% 0.20/0.44    inference(avatar_split_clause,[],[f65,f459])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.20/0.44  fof(f353,plain,(
% 0.20/0.44    spl4_46 | ~spl4_43 | ~spl4_44 | ~spl4_45),
% 0.20/0.44    inference(avatar_split_clause,[],[f348,f343,f324,f320,f350])).
% 0.20/0.44  fof(f324,plain,(
% 0.20/0.44    spl4_44 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.44  fof(f343,plain,(
% 0.20/0.44    spl4_45 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.20/0.44  fof(f348,plain,(
% 0.20/0.44    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | (~spl4_43 | ~spl4_44 | ~spl4_45)),
% 0.20/0.44    inference(subsumption_resolution,[],[f347,f321])).
% 0.20/0.44  fof(f347,plain,(
% 0.20/0.44    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | (~spl4_44 | ~spl4_45)),
% 0.20/0.44    inference(resolution,[],[f344,f326])).
% 0.20/0.44  fof(f326,plain,(
% 0.20/0.44    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl4_44),
% 0.20/0.44    inference(avatar_component_clause,[],[f324])).
% 0.20/0.44  fof(f344,plain,(
% 0.20/0.44    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | ~spl4_45),
% 0.20/0.44    inference(avatar_component_clause,[],[f343])).
% 0.20/0.44  fof(f345,plain,(
% 0.20/0.44    spl4_45 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_41),
% 0.20/0.44    inference(avatar_split_clause,[],[f341,f306,f90,f85,f80,f343])).
% 0.20/0.44  fof(f306,plain,(
% 0.20/0.44    spl4_41 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.20/0.44  fof(f341,plain,(
% 0.20/0.44    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_41)),
% 0.20/0.44    inference(subsumption_resolution,[],[f340,f82])).
% 0.20/0.45  fof(f340,plain,(
% 0.20/0.45    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_41)),
% 0.20/0.45    inference(subsumption_resolution,[],[f339,f92])).
% 0.20/0.45  fof(f339,plain,(
% 0.20/0.45    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_3 | ~spl4_41)),
% 0.20/0.45    inference(resolution,[],[f307,f87])).
% 0.20/0.45  fof(f307,plain,(
% 0.20/0.45    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_41),
% 0.20/0.45    inference(avatar_component_clause,[],[f306])).
% 0.20/0.45  fof(f331,plain,(
% 0.20/0.45    ~spl4_4 | ~spl4_25 | ~spl4_27 | spl4_43),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f330])).
% 0.20/0.45  fof(f330,plain,(
% 0.20/0.45    $false | (~spl4_4 | ~spl4_25 | ~spl4_27 | spl4_43)),
% 0.20/0.45    inference(subsumption_resolution,[],[f329,f92])).
% 0.20/0.45  fof(f329,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | (~spl4_25 | ~spl4_27 | spl4_43)),
% 0.20/0.45    inference(subsumption_resolution,[],[f328,f208])).
% 0.20/0.45  fof(f208,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_25),
% 0.20/0.45    inference(avatar_component_clause,[],[f206])).
% 0.20/0.45  fof(f206,plain,(
% 0.20/0.45    spl4_25 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.45  fof(f328,plain,(
% 0.20/0.45    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_27 | spl4_43)),
% 0.20/0.45    inference(resolution,[],[f322,f218])).
% 0.20/0.45  % (6797)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  fof(f218,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_27),
% 0.20/0.45    inference(avatar_component_clause,[],[f217])).
% 0.20/0.45  fof(f217,plain,(
% 0.20/0.45    spl4_27 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.45  fof(f322,plain,(
% 0.20/0.45    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_43),
% 0.20/0.45    inference(avatar_component_clause,[],[f320])).
% 0.20/0.45  fof(f327,plain,(
% 0.20/0.45    ~spl4_43 | spl4_44 | ~spl4_37 | ~spl4_42),
% 0.20/0.45    inference(avatar_split_clause,[],[f317,f312,f274,f324,f320])).
% 0.20/0.45  fof(f274,plain,(
% 0.20/0.45    spl4_37 <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.45  fof(f312,plain,(
% 0.20/0.45    spl4_42 <=> ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.45  fof(f317,plain,(
% 0.20/0.45    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_37 | ~spl4_42)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f316])).
% 0.20/0.45  fof(f316,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_37 | ~spl4_42)),
% 0.20/0.45    inference(superposition,[],[f313,f276])).
% 0.20/0.45  fof(f276,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl4_37),
% 0.20/0.45    inference(avatar_component_clause,[],[f274])).
% 0.20/0.45  fof(f313,plain,(
% 0.20/0.45    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_42),
% 0.20/0.45    inference(avatar_component_clause,[],[f312])).
% 0.20/0.45  fof(f314,plain,(
% 0.20/0.45    spl4_42 | ~spl4_2 | ~spl4_4 | ~spl4_40),
% 0.20/0.45    inference(avatar_split_clause,[],[f310,f302,f90,f80,f312])).
% 0.20/0.45  fof(f302,plain,(
% 0.20/0.45    spl4_40 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.45  fof(f310,plain,(
% 0.20/0.45    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_2 | ~spl4_4 | ~spl4_40)),
% 0.20/0.45    inference(subsumption_resolution,[],[f309,f92])).
% 0.20/0.45  fof(f309,plain,(
% 0.20/0.45    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl4_2 | ~spl4_40)),
% 0.20/0.45    inference(resolution,[],[f303,f82])).
% 0.20/0.45  fof(f303,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_40),
% 0.20/0.45    inference(avatar_component_clause,[],[f302])).
% 0.20/0.45  fof(f308,plain,(
% 0.20/0.45    spl4_41),
% 0.20/0.45    inference(avatar_split_clause,[],[f61,f306])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(rectify,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.20/0.45  fof(f304,plain,(
% 0.20/0.45    spl4_40),
% 0.20/0.45    inference(avatar_split_clause,[],[f58,f302])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.45  fof(f277,plain,(
% 0.20/0.45    spl4_37 | ~spl4_25 | ~spl4_35),
% 0.20/0.45    inference(avatar_split_clause,[],[f262,f258,f206,f274])).
% 0.20/0.45  fof(f258,plain,(
% 0.20/0.45    spl4_35 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.45  fof(f262,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_25 | ~spl4_35)),
% 0.20/0.45    inference(resolution,[],[f259,f208])).
% 0.20/0.45  fof(f259,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl4_35),
% 0.20/0.45    inference(avatar_component_clause,[],[f258])).
% 0.20/0.45  fof(f260,plain,(
% 0.20/0.45    spl4_35 | ~spl4_4 | ~spl4_34),
% 0.20/0.45    inference(avatar_split_clause,[],[f256,f253,f90,f258])).
% 0.20/0.45  fof(f253,plain,(
% 0.20/0.45    spl4_34 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.45  fof(f256,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | (~spl4_4 | ~spl4_34)),
% 0.20/0.45    inference(resolution,[],[f254,f92])).
% 0.20/0.45  fof(f254,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) ) | ~spl4_34),
% 0.20/0.45    inference(avatar_component_clause,[],[f253])).
% 0.20/0.45  fof(f255,plain,(
% 0.20/0.45    spl4_34),
% 0.20/0.45    inference(avatar_split_clause,[],[f71,f253])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.20/0.45  fof(f219,plain,(
% 0.20/0.45    spl4_27),
% 0.20/0.45    inference(avatar_split_clause,[],[f70,f217])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.45  fof(f215,plain,(
% 0.20/0.45    ~spl4_26 | ~spl4_6 | spl4_15 | ~spl4_18 | spl4_19 | ~spl4_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f190,f165,f161,f153,f140,f100,f212])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    spl4_15 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    spl4_18 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.45  fof(f161,plain,(
% 0.20/0.45    spl4_19 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl4_6 | spl4_15 | ~spl4_18 | spl4_19 | ~spl4_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f169,f188])).
% 0.20/0.45  fof(f188,plain,(
% 0.20/0.45    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl4_6 | ~spl4_18 | spl4_19)),
% 0.20/0.45    inference(subsumption_resolution,[],[f157,f162])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f161])).
% 0.20/0.45  fof(f157,plain,(
% 0.20/0.45    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_18)),
% 0.20/0.45    inference(resolution,[],[f154,f102])).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl4_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f153])).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (spl4_15 | ~spl4_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f142,f167])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl4_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f140])).
% 0.20/0.45  fof(f209,plain,(
% 0.20/0.45    spl4_25 | ~spl4_6 | ~spl4_16 | spl4_19 | ~spl4_24),
% 0.20/0.45    inference(avatar_split_clause,[],[f204,f198,f161,f145,f100,f206])).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    spl4_16 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.45  fof(f204,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_6 | ~spl4_16 | spl4_19 | ~spl4_24)),
% 0.20/0.45    inference(subsumption_resolution,[],[f203,f162])).
% 0.20/0.45  fof(f203,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_16 | ~spl4_24)),
% 0.20/0.45    inference(subsumption_resolution,[],[f202,f102])).
% 0.20/0.45  fof(f202,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_16 | ~spl4_24)),
% 0.20/0.45    inference(superposition,[],[f146,f200])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f145])).
% 0.20/0.45  fof(f201,plain,(
% 0.20/0.45    spl4_24 | ~spl4_6 | ~spl4_18 | spl4_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f188,f161,f153,f100,f198])).
% 0.20/0.45  fof(f195,plain,(
% 0.20/0.45    ~spl4_23 | ~spl4_6 | spl4_14 | ~spl4_18 | spl4_19 | ~spl4_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f189,f165,f161,f153,f135,f100,f192])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    spl4_14 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.45  fof(f189,plain,(
% 0.20/0.45    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl4_6 | spl4_14 | ~spl4_18 | spl4_19 | ~spl4_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f170,f188])).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl4_14 | ~spl4_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f137,f167])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f135])).
% 0.20/0.45  fof(f187,plain,(
% 0.20/0.45    ~spl4_4 | ~spl4_7 | spl4_22),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f186])).
% 0.20/0.45  fof(f186,plain,(
% 0.20/0.45    $false | (~spl4_4 | ~spl4_7 | spl4_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f185,f92])).
% 0.20/0.45  fof(f185,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | (~spl4_7 | spl4_22)),
% 0.20/0.45    inference(resolution,[],[f183,f106])).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f105])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl4_7 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.45  fof(f183,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | spl4_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f181])).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    spl4_22 <=> l1_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.45  fof(f184,plain,(
% 0.20/0.45    ~spl4_22 | spl4_1 | ~spl4_9 | ~spl4_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f179,f161,f113,f75,f181])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    spl4_9 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.45  fof(f179,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | (spl4_1 | ~spl4_9 | ~spl4_19)),
% 0.20/0.45    inference(subsumption_resolution,[],[f178,f77])).
% 0.20/0.45  fof(f178,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl4_9 | ~spl4_19)),
% 0.20/0.45    inference(resolution,[],[f163,f114])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f113])).
% 0.20/0.45  fof(f163,plain,(
% 0.20/0.45    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f161])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    spl4_19 | spl4_21 | ~spl4_5 | ~spl4_16 | ~spl4_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f172,f165,f145,f95,f174,f161])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_5 | ~spl4_16 | ~spl4_20)),
% 0.20/0.45    inference(subsumption_resolution,[],[f171,f97])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_16 | ~spl4_20)),
% 0.20/0.45    inference(superposition,[],[f146,f167])).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    spl4_19 | spl4_20 | ~spl4_5 | ~spl4_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f156,f153,f95,f165,f161])).
% 0.20/0.45  fof(f156,plain,(
% 0.20/0.45    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_5 | ~spl4_18)),
% 0.20/0.45    inference(resolution,[],[f154,f97])).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    spl4_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f73,f153])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f68,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    spl4_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f69,f145])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    ~spl4_15),
% 0.20/0.45    inference(avatar_split_clause,[],[f54,f140])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f41,f40,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ~spl4_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f53,f135])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    spl4_11 | ~spl4_8 | ~spl4_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f120,f117,f109,f122])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    spl4_10 <=> ! [X1,X0] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0))) ) | (~spl4_8 | ~spl4_10)),
% 0.20/0.45    inference(resolution,[],[f118,f110])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl4_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f117])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    spl4_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f72,f117])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f66,f55])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    spl4_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f59,f113])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    spl4_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f67,f109])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f56,f105])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f52,f100])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl4_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f51,f95])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    spl4_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f50,f90])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f49,f85])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    v3_tdlat_3(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f80])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f47,f75])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f42])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (6791)------------------------------
% 0.20/0.45  % (6791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (6791)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (6791)Memory used [KB]: 6524
% 0.20/0.45  % (6791)Time elapsed: 0.035 s
% 0.20/0.45  % (6791)------------------------------
% 0.20/0.45  % (6791)------------------------------
% 0.20/0.45  % (6782)Success in time 0.103 s
%------------------------------------------------------------------------------
