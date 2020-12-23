%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 315 expanded)
%              Number of leaves         :   37 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  575 (1282 expanded)
%              Number of equality atoms :   95 ( 230 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f926,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f96,f98,f118,f162,f172,f179,f183,f191,f206,f217,f224,f247,f261,f283,f306,f311,f318,f328,f338,f355,f358,f364,f485,f516,f701,f859,f925])).

fof(f925,plain,
    ( ~ spl3_25
    | spl3_49
    | ~ spl3_59
    | ~ spl3_72 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl3_25
    | spl3_49
    | ~ spl3_59
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f921,f920])).

fof(f920,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_25
    | spl3_49
    | ~ spl3_72 ),
    inference(unit_resulting_resolution,[],[f515,f858,f858,f216])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X1) = X2
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(sK2(X0,X1,X2),X0)
        | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f858,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl3_72
  <=> r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f515,plain,
    ( sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl3_49
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f921,plain,
    ( ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_59
    | ~ spl3_72 ),
    inference(unit_resulting_resolution,[],[f858,f700])).

fof(f700,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f699])).

fof(f699,plain,
    ( spl3_59
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f859,plain,
    ( spl3_72
    | ~ spl3_47
    | spl3_49 ),
    inference(avatar_split_clause,[],[f606,f513,f483,f856])).

fof(f483,plain,
    ( spl3_47
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f606,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl3_47
    | spl3_49 ),
    inference(unit_resulting_resolution,[],[f515,f484])).

fof(f484,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f483])).

fof(f701,plain,
    ( spl3_59
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f373,f315,f116,f699])).

fof(f116,plain,
    ( spl3_11
  <=> ! [X1,X0,X4] :
        ( ~ r2_hidden(X4,X1)
        | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f315,plain,
    ( spl3_32
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f373,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(superposition,[],[f117,f317])).

fof(f317,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f315])).

fof(f117,plain,
    ( ! [X4,X0,X1] :
        ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X4,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f516,plain,
    ( ~ spl3_49
    | ~ spl3_31
    | spl3_35 ),
    inference(avatar_split_clause,[],[f376,f341,f309,f513])).

fof(f309,plain,
    ( spl3_31
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f341,plain,
    ( spl3_35
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f376,plain,
    ( sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_31
    | spl3_35 ),
    inference(superposition,[],[f342,f310])).

fof(f310,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f309])).

fof(f342,plain,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f341])).

fof(f485,plain,
    ( spl3_47
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f194,f181,f483])).

fof(f181,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X1) = X2
        | r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_21 ),
    inference(factoring,[],[f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f364,plain,
    ( spl3_30
    | ~ spl3_34
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl3_30
    | ~ spl3_34
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f360,f305])).

fof(f305,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl3_30
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f360,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_34
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f337,f343])).

fof(f343,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f341])).

fof(f337,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl3_34
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f358,plain,
    ( spl3_6
    | ~ spl3_30
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl3_6
    | ~ spl3_30
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f94,f356])).

fof(f356,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_30
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f354,f304])).

fof(f304,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f303])).

fof(f354,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl3_36
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f94,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f355,plain,
    ( spl3_36
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f207,f204,f80,f75,f352])).

fof(f75,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f204,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f207,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f77,f82,f205])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f204])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f338,plain,
    ( spl3_34
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f198,f189,f80,f75,f335])).

fof(f189,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f198,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f77,f82,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f328,plain,
    ( ~ spl3_5
    | spl3_30
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f253,f222,f80,f75,f303,f89])).

fof(f89,plain,
    ( spl3_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f222,plain,
    ( spl3_27
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f253,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f223,f82])).

fof(f223,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f222])).

fof(f318,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f174,f170,f160,f93,f80,f75,f315])).

fof(f160,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f170,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f174,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f167,f173])).

fof(f173,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f82,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f167,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(superposition,[],[f161,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f311,plain,
    ( spl3_31
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f166,f160,f80,f309])).

fof(f166,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f82,f161])).

fof(f306,plain,
    ( ~ spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f293,f259,f89,f80,f75,f70,f303])).

fof(f70,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f259,plain,
    ( spl3_29
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f293,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f77,f72,f90,f82,f260])).

fof(f260,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f90,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f72,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f283,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f82,f267])).

fof(f267,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f77,f257])).

fof(f257,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_28
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f261,plain,
    ( spl3_28
    | spl3_29 ),
    inference(avatar_split_clause,[],[f46,f259,f256])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f247,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f212,f225])).

fof(f225,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f77,f72,f220])).

fof(f220,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_26
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f212,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f178,f171])).

fof(f178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_20
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f224,plain,
    ( spl3_26
    | spl3_27 ),
    inference(avatar_split_clause,[],[f45,f222,f219])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f217,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f63,f215])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f206,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f44,f204])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f191,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f43,f189])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f183,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f61,f181])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f179,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f173,f170,f80,f75,f176])).

fof(f172,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f53,f170])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f162,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f57,f160])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f118,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f67,f116])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f97,f93,f89])).

fof(f97,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f42,f95])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f96,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f41,f93,f89])).

fof(f41,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3081)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.45  % (3088)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.48  % (3104)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.48  % (3097)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.48  % (3089)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (3106)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.49  % (3096)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.49  % (3102)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.49  % (3096)Refutation not found, incomplete strategy% (3096)------------------------------
% 0.20/0.49  % (3096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3096)Memory used [KB]: 10618
% 0.20/0.49  % (3096)Time elapsed: 0.105 s
% 0.20/0.49  % (3096)------------------------------
% 0.20/0.49  % (3096)------------------------------
% 0.20/0.50  % (3094)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (3104)Refutation not found, incomplete strategy% (3104)------------------------------
% 0.20/0.50  % (3104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3104)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3104)Memory used [KB]: 10746
% 0.20/0.50  % (3104)Time elapsed: 0.105 s
% 0.20/0.50  % (3104)------------------------------
% 0.20/0.50  % (3104)------------------------------
% 0.20/0.50  % (3086)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (3082)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (3083)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (3085)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (3080)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (3095)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (3107)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (3092)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (3103)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (3098)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (3090)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (3090)Refutation not found, incomplete strategy% (3090)------------------------------
% 0.20/0.53  % (3090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3090)Memory used [KB]: 10746
% 0.20/0.53  % (3090)Time elapsed: 0.125 s
% 0.20/0.53  % (3090)------------------------------
% 0.20/0.53  % (3090)------------------------------
% 1.31/0.53  % (3105)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.53  % (3093)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.53  % (3108)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.53  % (3084)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.54  % (3108)Refutation not found, incomplete strategy% (3108)------------------------------
% 1.31/0.54  % (3108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (3108)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (3108)Memory used [KB]: 10746
% 1.31/0.54  % (3108)Time elapsed: 0.131 s
% 1.31/0.54  % (3108)------------------------------
% 1.31/0.54  % (3108)------------------------------
% 1.31/0.54  % (3101)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (3099)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.54  % (3091)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.54  % (3107)Refutation not found, incomplete strategy% (3107)------------------------------
% 1.31/0.54  % (3107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (3107)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (3107)Memory used [KB]: 6268
% 1.31/0.54  % (3107)Time elapsed: 0.116 s
% 1.31/0.54  % (3107)------------------------------
% 1.31/0.54  % (3107)------------------------------
% 1.31/0.55  % (3110)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (3110)Refutation not found, incomplete strategy% (3110)------------------------------
% 1.31/0.55  % (3110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (3110)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (3110)Memory used [KB]: 1663
% 1.31/0.55  % (3110)Time elapsed: 0.001 s
% 1.31/0.55  % (3110)------------------------------
% 1.31/0.55  % (3110)------------------------------
% 1.31/0.55  % (3087)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.55  % (3100)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.61  % (3112)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.63  % (3113)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.67  % (3119)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.04/0.67  % (3120)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.04/0.67  % (3112)Refutation found. Thanks to Tanya!
% 2.04/0.67  % SZS status Theorem for theBenchmark
% 2.04/0.67  % SZS output start Proof for theBenchmark
% 2.04/0.67  fof(f926,plain,(
% 2.04/0.67    $false),
% 2.04/0.67    inference(avatar_sat_refutation,[],[f73,f78,f83,f96,f98,f118,f162,f172,f179,f183,f191,f206,f217,f224,f247,f261,f283,f306,f311,f318,f328,f338,f355,f358,f364,f485,f516,f701,f859,f925])).
% 2.04/0.67  fof(f925,plain,(
% 2.04/0.67    ~spl3_25 | spl3_49 | ~spl3_59 | ~spl3_72),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f924])).
% 2.04/0.67  fof(f924,plain,(
% 2.04/0.67    $false | (~spl3_25 | spl3_49 | ~spl3_59 | ~spl3_72)),
% 2.04/0.67    inference(subsumption_resolution,[],[f921,f920])).
% 2.04/0.67  fof(f920,plain,(
% 2.04/0.67    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (~spl3_25 | spl3_49 | ~spl3_72)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f515,f858,f858,f216])).
% 2.04/0.67  fof(f216,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl3_25),
% 2.04/0.67    inference(avatar_component_clause,[],[f215])).
% 2.04/0.67  fof(f215,plain,(
% 2.04/0.67    spl3_25 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.04/0.67  fof(f858,plain,(
% 2.04/0.67    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | ~spl3_72),
% 2.04/0.67    inference(avatar_component_clause,[],[f856])).
% 2.04/0.67  fof(f856,plain,(
% 2.04/0.67    spl3_72 <=> r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 2.04/0.67  fof(f515,plain,(
% 2.04/0.67    sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl3_49),
% 2.04/0.67    inference(avatar_component_clause,[],[f513])).
% 2.04/0.67  fof(f513,plain,(
% 2.04/0.67    spl3_49 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.04/0.67  fof(f921,plain,(
% 2.04/0.67    ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (~spl3_59 | ~spl3_72)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f858,f700])).
% 2.04/0.67  fof(f700,plain,(
% 2.04/0.67    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | ~spl3_59),
% 2.04/0.67    inference(avatar_component_clause,[],[f699])).
% 2.04/0.67  fof(f699,plain,(
% 2.04/0.67    spl3_59 <=> ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 2.04/0.67  fof(f859,plain,(
% 2.04/0.67    spl3_72 | ~spl3_47 | spl3_49),
% 2.04/0.67    inference(avatar_split_clause,[],[f606,f513,f483,f856])).
% 2.04/0.67  fof(f483,plain,(
% 2.04/0.67    spl3_47 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 2.04/0.67  fof(f606,plain,(
% 2.04/0.67    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | (~spl3_47 | spl3_49)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f515,f484])).
% 2.04/0.67  fof(f484,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_47),
% 2.04/0.67    inference(avatar_component_clause,[],[f483])).
% 2.04/0.67  fof(f701,plain,(
% 2.04/0.67    spl3_59 | ~spl3_11 | ~spl3_32),
% 2.04/0.67    inference(avatar_split_clause,[],[f373,f315,f116,f699])).
% 2.04/0.67  fof(f116,plain,(
% 2.04/0.67    spl3_11 <=> ! [X1,X0,X4] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.04/0.67  fof(f315,plain,(
% 2.04/0.67    spl3_32 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.04/0.67  fof(f373,plain,(
% 2.04/0.67    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | (~spl3_11 | ~spl3_32)),
% 2.04/0.67    inference(superposition,[],[f117,f317])).
% 2.04/0.67  fof(f317,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_32),
% 2.04/0.67    inference(avatar_component_clause,[],[f315])).
% 2.04/0.67  fof(f117,plain,(
% 2.04/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) ) | ~spl3_11),
% 2.04/0.67    inference(avatar_component_clause,[],[f116])).
% 2.04/0.67  fof(f516,plain,(
% 2.04/0.67    ~spl3_49 | ~spl3_31 | spl3_35),
% 2.04/0.67    inference(avatar_split_clause,[],[f376,f341,f309,f513])).
% 2.04/0.67  fof(f309,plain,(
% 2.04/0.67    spl3_31 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.04/0.67  fof(f341,plain,(
% 2.04/0.67    spl3_35 <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.04/0.67  fof(f376,plain,(
% 2.04/0.67    sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_31 | spl3_35)),
% 2.04/0.67    inference(superposition,[],[f342,f310])).
% 2.04/0.67  fof(f310,plain,(
% 2.04/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_31),
% 2.04/0.67    inference(avatar_component_clause,[],[f309])).
% 2.04/0.67  fof(f342,plain,(
% 2.04/0.67    sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | spl3_35),
% 2.04/0.67    inference(avatar_component_clause,[],[f341])).
% 2.04/0.67  fof(f485,plain,(
% 2.04/0.67    spl3_47 | ~spl3_21),
% 2.04/0.67    inference(avatar_split_clause,[],[f194,f181,f483])).
% 2.04/0.67  fof(f181,plain,(
% 2.04/0.67    spl3_21 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.04/0.67  fof(f194,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_21),
% 2.04/0.67    inference(factoring,[],[f182])).
% 2.04/0.67  fof(f182,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl3_21),
% 2.04/0.67    inference(avatar_component_clause,[],[f181])).
% 2.04/0.67  fof(f364,plain,(
% 2.04/0.67    spl3_30 | ~spl3_34 | ~spl3_35),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f362])).
% 2.04/0.67  fof(f362,plain,(
% 2.04/0.67    $false | (spl3_30 | ~spl3_34 | ~spl3_35)),
% 2.04/0.67    inference(subsumption_resolution,[],[f360,f305])).
% 2.04/0.67  fof(f305,plain,(
% 2.04/0.67    sK1 != k1_tops_1(sK0,sK1) | spl3_30),
% 2.04/0.67    inference(avatar_component_clause,[],[f303])).
% 2.04/0.67  fof(f303,plain,(
% 2.04/0.67    spl3_30 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.04/0.67  fof(f360,plain,(
% 2.04/0.67    sK1 = k1_tops_1(sK0,sK1) | (~spl3_34 | ~spl3_35)),
% 2.04/0.67    inference(forward_demodulation,[],[f337,f343])).
% 2.04/0.67  fof(f343,plain,(
% 2.04/0.67    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_35),
% 2.04/0.67    inference(avatar_component_clause,[],[f341])).
% 2.04/0.67  fof(f337,plain,(
% 2.04/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_34),
% 2.04/0.67    inference(avatar_component_clause,[],[f335])).
% 2.04/0.67  fof(f335,plain,(
% 2.04/0.67    spl3_34 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.04/0.67  fof(f358,plain,(
% 2.04/0.67    spl3_6 | ~spl3_30 | ~spl3_36),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f357])).
% 2.04/0.67  fof(f357,plain,(
% 2.04/0.67    $false | (spl3_6 | ~spl3_30 | ~spl3_36)),
% 2.04/0.67    inference(subsumption_resolution,[],[f94,f356])).
% 2.04/0.67  fof(f356,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl3_30 | ~spl3_36)),
% 2.04/0.67    inference(forward_demodulation,[],[f354,f304])).
% 2.04/0.67  fof(f304,plain,(
% 2.04/0.67    sK1 = k1_tops_1(sK0,sK1) | ~spl3_30),
% 2.04/0.67    inference(avatar_component_clause,[],[f303])).
% 2.04/0.67  fof(f354,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_36),
% 2.04/0.67    inference(avatar_component_clause,[],[f352])).
% 2.04/0.67  fof(f352,plain,(
% 2.04/0.67    spl3_36 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.04/0.67  fof(f94,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_6),
% 2.04/0.67    inference(avatar_component_clause,[],[f93])).
% 2.04/0.67  fof(f93,plain,(
% 2.04/0.67    spl3_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.04/0.67  fof(f355,plain,(
% 2.04/0.67    spl3_36 | ~spl3_2 | ~spl3_3 | ~spl3_24),
% 2.04/0.67    inference(avatar_split_clause,[],[f207,f204,f80,f75,f352])).
% 2.04/0.67  fof(f75,plain,(
% 2.04/0.67    spl3_2 <=> l1_pre_topc(sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.04/0.67  fof(f80,plain,(
% 2.04/0.67    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.04/0.67  fof(f204,plain,(
% 2.04/0.67    spl3_24 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.04/0.67  fof(f207,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_24)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f82,f205])).
% 2.04/0.67  fof(f205,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_24),
% 2.04/0.67    inference(avatar_component_clause,[],[f204])).
% 2.04/0.67  fof(f82,plain,(
% 2.04/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.04/0.67    inference(avatar_component_clause,[],[f80])).
% 2.04/0.67  fof(f77,plain,(
% 2.04/0.67    l1_pre_topc(sK0) | ~spl3_2),
% 2.04/0.67    inference(avatar_component_clause,[],[f75])).
% 2.04/0.67  fof(f338,plain,(
% 2.04/0.67    spl3_34 | ~spl3_2 | ~spl3_3 | ~spl3_23),
% 2.04/0.67    inference(avatar_split_clause,[],[f198,f189,f80,f75,f335])).
% 2.04/0.67  fof(f189,plain,(
% 2.04/0.67    spl3_23 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.04/0.67  fof(f198,plain,(
% 2.04/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_23)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f82,f190])).
% 2.04/0.67  fof(f190,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_23),
% 2.04/0.67    inference(avatar_component_clause,[],[f189])).
% 2.04/0.67  fof(f328,plain,(
% 2.04/0.67    ~spl3_5 | spl3_30 | ~spl3_2 | ~spl3_3 | ~spl3_27),
% 2.04/0.67    inference(avatar_split_clause,[],[f253,f222,f80,f75,f303,f89])).
% 2.04/0.67  fof(f89,plain,(
% 2.04/0.67    spl3_5 <=> v3_pre_topc(sK1,sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.04/0.67  fof(f222,plain,(
% 2.04/0.67    spl3_27 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.04/0.67  fof(f253,plain,(
% 2.04/0.67    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_27)),
% 2.04/0.67    inference(resolution,[],[f223,f82])).
% 2.04/0.67  fof(f223,plain,(
% 2.04/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl3_27),
% 2.04/0.67    inference(avatar_component_clause,[],[f222])).
% 2.04/0.67  fof(f318,plain,(
% 2.04/0.67    spl3_32 | ~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_18 | ~spl3_19),
% 2.04/0.67    inference(avatar_split_clause,[],[f174,f170,f160,f93,f80,f75,f315])).
% 2.04/0.67  fof(f160,plain,(
% 2.04/0.67    spl3_18 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.04/0.67  fof(f170,plain,(
% 2.04/0.67    spl3_19 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.04/0.67  fof(f174,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_18 | ~spl3_19)),
% 2.04/0.67    inference(subsumption_resolution,[],[f167,f173])).
% 2.04/0.67  fof(f173,plain,(
% 2.04/0.67    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | ~spl3_19)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f82,f171])).
% 2.04/0.67  fof(f171,plain,(
% 2.04/0.67    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_19),
% 2.04/0.67    inference(avatar_component_clause,[],[f170])).
% 2.04/0.67  fof(f167,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_6 | ~spl3_18)),
% 2.04/0.67    inference(superposition,[],[f161,f95])).
% 2.04/0.67  fof(f95,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_6),
% 2.04/0.67    inference(avatar_component_clause,[],[f93])).
% 2.04/0.67  fof(f161,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 2.04/0.67    inference(avatar_component_clause,[],[f160])).
% 2.04/0.67  fof(f311,plain,(
% 2.04/0.67    spl3_31 | ~spl3_3 | ~spl3_18),
% 2.04/0.67    inference(avatar_split_clause,[],[f166,f160,f80,f309])).
% 2.04/0.67  fof(f166,plain,(
% 2.04/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl3_3 | ~spl3_18)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f82,f161])).
% 2.04/0.67  fof(f306,plain,(
% 2.04/0.67    ~spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_29),
% 2.04/0.67    inference(avatar_split_clause,[],[f293,f259,f89,f80,f75,f70,f303])).
% 2.04/0.67  fof(f70,plain,(
% 2.04/0.67    spl3_1 <=> v2_pre_topc(sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.04/0.67  fof(f259,plain,(
% 2.04/0.67    spl3_29 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.04/0.67  fof(f293,plain,(
% 2.04/0.67    sK1 != k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_29)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f72,f90,f82,f260])).
% 2.04/0.67  fof(f260,plain,(
% 2.04/0.67    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl3_29),
% 2.04/0.67    inference(avatar_component_clause,[],[f259])).
% 2.04/0.67  fof(f90,plain,(
% 2.04/0.67    ~v3_pre_topc(sK1,sK0) | spl3_5),
% 2.04/0.67    inference(avatar_component_clause,[],[f89])).
% 2.04/0.67  fof(f72,plain,(
% 2.04/0.67    v2_pre_topc(sK0) | ~spl3_1),
% 2.04/0.67    inference(avatar_component_clause,[],[f70])).
% 2.04/0.67  fof(f283,plain,(
% 2.04/0.67    ~spl3_2 | ~spl3_3 | ~spl3_28),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f280])).
% 2.04/0.67  fof(f280,plain,(
% 2.04/0.67    $false | (~spl3_2 | ~spl3_3 | ~spl3_28)),
% 2.04/0.67    inference(subsumption_resolution,[],[f82,f267])).
% 2.04/0.67  fof(f267,plain,(
% 2.04/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_28)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f257])).
% 2.04/0.67  fof(f257,plain,(
% 2.04/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl3_28),
% 2.04/0.67    inference(avatar_component_clause,[],[f256])).
% 2.04/0.67  fof(f256,plain,(
% 2.04/0.67    spl3_28 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.04/0.67  fof(f261,plain,(
% 2.04/0.67    spl3_28 | spl3_29),
% 2.04/0.67    inference(avatar_split_clause,[],[f46,f259,f256])).
% 2.04/0.67  fof(f46,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f21])).
% 2.04/0.67  fof(f21,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.04/0.67    inference(flattening,[],[f20])).
% 2.04/0.67  fof(f20,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f12])).
% 2.04/0.67  fof(f12,axiom,(
% 2.04/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.04/0.67  fof(f247,plain,(
% 2.04/0.67    ~spl3_1 | ~spl3_2 | ~spl3_19 | ~spl3_20 | ~spl3_26),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f244])).
% 2.04/0.67  fof(f244,plain,(
% 2.04/0.67    $false | (~spl3_1 | ~spl3_2 | ~spl3_19 | ~spl3_20 | ~spl3_26)),
% 2.04/0.67    inference(subsumption_resolution,[],[f212,f225])).
% 2.04/0.67  fof(f225,plain,(
% 2.04/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_26)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f72,f220])).
% 2.04/0.67  fof(f220,plain,(
% 2.04/0.67    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl3_26),
% 2.04/0.67    inference(avatar_component_clause,[],[f219])).
% 2.04/0.67  fof(f219,plain,(
% 2.04/0.67    spl3_26 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.04/0.67  fof(f212,plain,(
% 2.04/0.67    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_19 | ~spl3_20)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f77,f178,f171])).
% 2.04/0.67  fof(f178,plain,(
% 2.04/0.67    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_20),
% 2.04/0.67    inference(avatar_component_clause,[],[f176])).
% 2.04/0.67  fof(f176,plain,(
% 2.04/0.67    spl3_20 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.04/0.67  fof(f224,plain,(
% 2.04/0.67    spl3_26 | spl3_27),
% 2.04/0.67    inference(avatar_split_clause,[],[f45,f222,f219])).
% 2.04/0.67  fof(f45,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f21])).
% 2.04/0.67  fof(f217,plain,(
% 2.04/0.67    spl3_25),
% 2.04/0.67    inference(avatar_split_clause,[],[f63,f215])).
% 2.04/0.67  fof(f63,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f37])).
% 2.04/0.67  fof(f37,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.04/0.67  fof(f36,plain,(
% 2.04/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.04/0.67    introduced(choice_axiom,[])).
% 2.04/0.67  fof(f35,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(rectify,[],[f34])).
% 2.04/0.67  fof(f34,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(flattening,[],[f33])).
% 2.04/0.67  fof(f33,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(nnf_transformation,[],[f2])).
% 2.04/0.67  fof(f2,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.04/0.67  fof(f206,plain,(
% 2.04/0.67    spl3_24),
% 2.04/0.67    inference(avatar_split_clause,[],[f44,f204])).
% 2.04/0.67  fof(f44,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f19])).
% 2.04/0.67  fof(f19,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f11])).
% 2.04/0.67  fof(f11,axiom,(
% 2.04/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.04/0.67  fof(f191,plain,(
% 2.04/0.67    spl3_23),
% 2.04/0.67    inference(avatar_split_clause,[],[f43,f189])).
% 2.04/0.67  fof(f43,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f18])).
% 2.04/0.67  fof(f18,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f13])).
% 2.04/0.67  fof(f13,axiom,(
% 2.04/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.04/0.67  fof(f183,plain,(
% 2.04/0.67    spl3_21),
% 2.04/0.67    inference(avatar_split_clause,[],[f61,f181])).
% 2.04/0.67  fof(f61,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f37])).
% 2.04/0.67  fof(f179,plain,(
% 2.04/0.67    spl3_20 | ~spl3_2 | ~spl3_3 | ~spl3_19),
% 2.04/0.67    inference(avatar_split_clause,[],[f173,f170,f80,f75,f176])).
% 2.04/0.67  fof(f172,plain,(
% 2.04/0.67    spl3_19),
% 2.04/0.67    inference(avatar_split_clause,[],[f53,f170])).
% 2.04/0.67  fof(f53,plain,(
% 2.04/0.67    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f24])).
% 2.04/0.67  fof(f24,plain,(
% 2.04/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.04/0.67    inference(flattening,[],[f23])).
% 2.04/0.67  fof(f23,plain,(
% 2.04/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f10])).
% 2.04/0.67  fof(f10,axiom,(
% 2.04/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.04/0.67  fof(f162,plain,(
% 2.04/0.67    spl3_18),
% 2.04/0.67    inference(avatar_split_clause,[],[f57,f160])).
% 2.04/0.67  fof(f57,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f25])).
% 2.04/0.67  fof(f25,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f8])).
% 2.04/0.67  fof(f8,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.04/0.67  fof(f118,plain,(
% 2.04/0.67    spl3_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f67,f116])).
% 2.04/0.67  fof(f67,plain,(
% 2.04/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.04/0.67    inference(equality_resolution,[],[f59])).
% 2.04/0.67  fof(f59,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.04/0.67    inference(cnf_transformation,[],[f37])).
% 2.04/0.67  fof(f98,plain,(
% 2.04/0.67    ~spl3_5 | ~spl3_6),
% 2.04/0.67    inference(avatar_split_clause,[],[f97,f93,f89])).
% 2.04/0.67  fof(f97,plain,(
% 2.04/0.67    ~v3_pre_topc(sK1,sK0) | ~spl3_6),
% 2.04/0.67    inference(subsumption_resolution,[],[f42,f95])).
% 2.04/0.67  fof(f42,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  fof(f30,plain,(
% 2.04/0.67    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.04/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 2.04/0.67  fof(f28,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.04/0.67    introduced(choice_axiom,[])).
% 2.04/0.67  fof(f29,plain,(
% 2.04/0.67    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.04/0.67    introduced(choice_axiom,[])).
% 2.04/0.67  fof(f27,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.67    inference(flattening,[],[f26])).
% 2.04/0.67  fof(f26,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.67    inference(nnf_transformation,[],[f17])).
% 2.04/0.67  fof(f17,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.04/0.67    inference(flattening,[],[f16])).
% 2.04/0.67  fof(f16,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f15])).
% 2.04/0.67  fof(f15,negated_conjecture,(
% 2.04/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.04/0.67    inference(negated_conjecture,[],[f14])).
% 2.04/0.67  fof(f14,conjecture,(
% 2.04/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.04/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.04/0.67  fof(f96,plain,(
% 2.04/0.67    spl3_5 | spl3_6),
% 2.04/0.67    inference(avatar_split_clause,[],[f41,f93,f89])).
% 2.04/0.67  fof(f41,plain,(
% 2.04/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  fof(f83,plain,(
% 2.04/0.67    spl3_3),
% 2.04/0.67    inference(avatar_split_clause,[],[f40,f80])).
% 2.04/0.67  fof(f40,plain,(
% 2.04/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  fof(f78,plain,(
% 2.04/0.67    spl3_2),
% 2.04/0.67    inference(avatar_split_clause,[],[f39,f75])).
% 2.04/0.67  fof(f39,plain,(
% 2.04/0.67    l1_pre_topc(sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  fof(f73,plain,(
% 2.04/0.67    spl3_1),
% 2.04/0.67    inference(avatar_split_clause,[],[f38,f70])).
% 2.04/0.67  fof(f38,plain,(
% 2.04/0.67    v2_pre_topc(sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  % SZS output end Proof for theBenchmark
% 2.04/0.67  % (3112)------------------------------
% 2.04/0.67  % (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (3112)Termination reason: Refutation
% 2.04/0.67  
% 2.04/0.67  % (3112)Memory used [KB]: 6908
% 2.04/0.67  % (3112)Time elapsed: 0.130 s
% 2.04/0.67  % (3112)------------------------------
% 2.04/0.67  % (3112)------------------------------
% 2.35/0.68  % (3121)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.35/0.69  % (3122)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.35/0.69  % (3076)Success in time 0.332 s
%------------------------------------------------------------------------------
