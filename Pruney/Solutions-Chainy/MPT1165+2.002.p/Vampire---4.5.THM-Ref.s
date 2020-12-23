%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 336 expanded)
%              Number of leaves         :   33 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          : 1085 (1992 expanded)
%              Number of equality atoms :   92 ( 217 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f77,f82,f90,f94,f99,f136,f140,f145,f158,f167,f197,f201,f207,f216,f273,f293,f309,f335,f343,f358,f368,f386,f396])).

fof(f396,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f394,f80])).

fof(f80,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_9
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f394,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f393,f49])).

fof(f49,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f393,plain,
    ( v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f392,f65])).

fof(f65,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f392,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f391,f61])).

fof(f61,plain,
    ( v5_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f391,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f390,f57])).

fof(f57,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f390,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f388,f53])).

fof(f53,plain,
    ( v3_orders_2(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f388,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_50 ),
    inference(resolution,[],[f385,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0)
        | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_12
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f385,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl3_50
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f386,plain,
    ( spl3_50
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f370,f72,f68,f384])).

fof(f68,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f370,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f69,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f368,plain,
    ( ~ spl3_38
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f365,f356,f88,f64,f252])).

fof(f252,plain,
    ( spl3_38
  <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f88,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ r2_orders_2(X1,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f356,plain,
    ( spl3_48
  <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f365,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f363,f65])).

fof(f363,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_11
    | ~ spl3_48 ),
    inference(resolution,[],[f357,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_orders_2(X1,X0,X0)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f357,plain,
    ( r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f356])).

fof(f358,plain,
    ( spl3_48
    | ~ spl3_38
    | ~ spl3_8
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f348,f341,f75,f252,f356])).

fof(f75,plain,
    ( spl3_8
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f341,plain,
    ( spl3_46
  <=> ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f348,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ spl3_8
    | ~ spl3_46 ),
    inference(resolution,[],[f342,f76])).

fof(f76,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f341])).

fof(f343,plain,
    ( ~ spl3_38
    | spl3_46
    | ~ spl3_6
    | spl3_7
    | ~ spl3_35
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f339,f333,f235,f72,f68,f341,f252])).

fof(f235,plain,
    ( spl3_35
  <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f333,plain,
    ( spl3_45
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) )
    | ~ spl3_6
    | spl3_7
    | ~ spl3_35
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f338,f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | k1_xboole_0 = sK1 )
    | ~ spl3_6
    | ~ spl3_35
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f337,f69])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl3_35
    | ~ spl3_45 ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_35
    | ~ spl3_45 ),
    inference(superposition,[],[f334,f236])).

fof(f236,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f235])).

fof(f334,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( spl3_45
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f318,f307,f64,f60,f56,f52,f48,f333])).

fof(f307,plain,
    ( spl3_41
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0)
        | ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0))
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | v2_struct_0(X2)
        | ~ m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f317,f49])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f316,f61])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f315,f57])).

fof(f315,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f314,f53])).

fof(f314,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1)
        | ~ m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) )
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(resolution,[],[f308,f65])).

fof(f308,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0)
        | ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0))
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | v2_struct_0(X2)
        | ~ m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0)) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f307])).

fof(f309,plain,
    ( spl3_41
    | ~ spl3_21
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f203,f195,f143,f307])).

fof(f143,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f195,plain,
    ( spl3_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f203,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0)
        | ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0))
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ l1_orders_2(X2)
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | v2_struct_0(X2)
        | ~ m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0)) )
    | ~ spl3_21
    | ~ spl3_29 ),
    inference(resolution,[],[f196,f144])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | v2_struct_0(X0)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f195])).

fof(f293,plain,
    ( spl3_35
    | spl3_7
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f288,f214,f75,f68,f72,f235])).

fof(f214,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f288,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f222,f69])).

fof(f222,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(resolution,[],[f215,f76])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK0,X0)
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f273,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_25
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f271,f76])).

fof(f271,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f270,f49])).

fof(f270,plain,
    ( v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f269,f81])).

fof(f269,plain,
    ( k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f268,f69])).

fof(f268,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f267,f65])).

fof(f267,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f266,f61])).

fof(f266,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f265,f57])).

fof(f265,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_25
    | spl3_38 ),
    inference(subsumption_resolution,[],[f262,f53])).

fof(f262,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_25
    | spl3_38 ),
    inference(resolution,[],[f253,f166])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | v2_struct_0(X0)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f253,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f252])).

fof(f216,plain,
    ( spl3_32
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f212,f205,f64,f60,f56,f52,f48,f214])).

fof(f205,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f211,f49])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f210,f61])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f209,f57])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f208,f53])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(resolution,[],[f206,f65])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl3_31
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f202,f199,f97,f205])).

fof(f97,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_orders_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f199,plain,
    ( spl3_30
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f200,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_orders_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f33,f199])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f197,plain,
    ( spl3_29
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f179,f134,f64,f60,f56,f52,f48,f195])).

fof(f134,plain,
    ( spl3_19
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_orders_2(X0,X1,X2)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f178,f49])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f177,f61])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f176,f57])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f175,f53])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(resolution,[],[f135,f65])).

fof(f135,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_orders_2(X0,X1,X2)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f134])).

fof(f167,plain,
    ( spl3_25
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f159,f156,f97,f165])).

fof(f156,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f157,f98])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f31,f156])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f141,f138,f97,f143])).

fof(f138,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_orders_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f139,f98])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f32,f138])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f136,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f28,f134])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f99,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f94,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 != X2
      | m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f82,plain,
    ( ~ spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f46,f72,f79])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f77,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f20,f75,f72])).

fof(f20,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f68])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22655)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.45  % (22645)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (22644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (22647)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (22637)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (22647)Refutation not found, incomplete strategy% (22647)------------------------------
% 0.20/0.47  % (22647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22647)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22647)Memory used [KB]: 10618
% 0.20/0.47  % (22647)Time elapsed: 0.076 s
% 0.20/0.47  % (22647)------------------------------
% 0.20/0.47  % (22647)------------------------------
% 0.20/0.47  % (22645)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (22635)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (22656)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (22636)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22639)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (22642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (22636)Refutation not found, incomplete strategy% (22636)------------------------------
% 0.20/0.48  % (22636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22636)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22636)Memory used [KB]: 10618
% 0.20/0.48  % (22636)Time elapsed: 0.081 s
% 0.20/0.48  % (22636)------------------------------
% 0.20/0.48  % (22636)------------------------------
% 0.20/0.49  % (22651)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f397,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f77,f82,f90,f94,f99,f136,f140,f145,f158,f167,f197,f201,f207,f216,f273,f293,f309,f335,f343,f358,f368,f386,f396])).
% 0.20/0.49  fof(f396,plain,(
% 0.20/0.49    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_12 | ~spl3_50),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.49  fof(f395,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f394,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_9 <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f394,plain,(
% 0.20/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f393,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f393,plain,(
% 0.20/0.49    v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f392,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    l1_orders_2(sK0) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_5 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f392,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f391,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_4 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f390,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    v4_orders_2(sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_3 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(subsumption_resolution,[],[f388,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    v3_orders_2(sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_2 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_12 | ~spl3_50)),
% 0.20/0.49    inference(resolution,[],[f385,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl3_12 <=> ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_50),
% 0.20/0.49    inference(avatar_component_clause,[],[f384])).
% 0.20/0.49  fof(f384,plain,(
% 0.20/0.49    spl3_50 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.49  fof(f386,plain,(
% 0.20/0.49    spl3_50 | ~spl3_6 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f370,f72,f68,f384])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_7 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_6 | ~spl3_7)),
% 0.20/0.49    inference(backward_demodulation,[],[f69,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    ~spl3_38 | ~spl3_5 | ~spl3_11 | ~spl3_48),
% 0.20/0.49    inference(avatar_split_clause,[],[f365,f356,f88,f64,f252])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    spl3_38 <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_11 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_orders_2(X1,X0,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    spl3_48 <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_5 | ~spl3_11 | ~spl3_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f363,f65])).
% 0.20/0.49  fof(f363,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_11 | ~spl3_48)),
% 0.20/0.49    inference(resolution,[],[f357,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) ) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | ~spl3_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f356])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    spl3_48 | ~spl3_38 | ~spl3_8 | ~spl3_46),
% 0.20/0.49    inference(avatar_split_clause,[],[f348,f341,f75,f252,f356])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_8 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    spl3_46 <=> ! [X0] : (~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | (~spl3_8 | ~spl3_46)),
% 0.20/0.49    inference(resolution,[],[f342,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    m1_orders_2(sK1,sK0,sK1) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1))) ) | ~spl3_46),
% 0.20/0.49    inference(avatar_component_clause,[],[f341])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    ~spl3_38 | spl3_46 | ~spl3_6 | spl3_7 | ~spl3_35 | ~spl3_45),
% 0.20/0.49    inference(avatar_split_clause,[],[f339,f333,f235,f72,f68,f341,f252])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    spl3_35 <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.49  fof(f333,plain,(
% 0.20/0.49    spl3_45 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))) ) | (~spl3_6 | spl3_7 | ~spl3_35 | ~spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f338,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1) ) | (~spl3_6 | ~spl3_35 | ~spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f337,f69])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl3_35 | ~spl3_45)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f336])).
% 0.20/0.49  fof(f336,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | r2_orders_2(sK0,sK2(sK0,sK1,X0),sK2(sK0,sK1,sK1)) | ~m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_35 | ~spl3_45)),
% 0.20/0.49    inference(superposition,[],[f334,f236])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | ~spl3_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f235])).
% 0.20/0.49  fof(f334,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1)) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f333])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    spl3_45 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41),
% 0.20/0.49    inference(avatar_split_clause,[],[f318,f307,f64,f60,f56,f52,f48,f333])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    spl3_41 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0) | ~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0)) | ~v3_orders_2(X2) | ~v4_orders_2(X2) | ~v5_orders_2(X2) | ~l1_orders_2(X2) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2))) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | v2_struct_0(X2) | ~m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f317,f49])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | v2_struct_0(sK0) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f316,f61])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | v2_struct_0(sK0) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f57])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | v2_struct_0(sK0) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))) ) | (~spl3_2 | ~spl3_5 | ~spl3_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f314,f53])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(sK2(sK0,k3_orders_2(sK0,X0,X1),X2),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | v2_struct_0(sK0) | ~m1_orders_2(X2,sK0,k3_orders_2(sK0,X0,X1))) ) | (~spl3_5 | ~spl3_41)),
% 0.20/0.49    inference(resolution,[],[f308,f65])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0) | ~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0)) | ~v3_orders_2(X2) | ~v4_orders_2(X2) | ~v5_orders_2(X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2))) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | v2_struct_0(X2) | ~m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0))) ) | ~spl3_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f307])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    spl3_41 | ~spl3_21 | ~spl3_29),
% 0.20/0.49    inference(avatar_split_clause,[],[f203,f195,f143,f307])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl3_21 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl3_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(X2,k3_orders_2(sK0,X1,X0),X3),X0) | ~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0),X3),u1_struct_0(sK0)) | ~v3_orders_2(X2) | ~v4_orders_2(X2) | ~v5_orders_2(X2) | ~l1_orders_2(X2) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(X2))) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | v2_struct_0(X2) | ~m1_orders_2(X3,X2,k3_orders_2(sK0,X1,X0))) ) | (~spl3_21 | ~spl3_29)),
% 0.20/0.49    inference(resolution,[],[f196,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    spl3_35 | spl3_7 | ~spl3_6 | ~spl3_8 | ~spl3_32),
% 0.20/0.49    inference(avatar_split_clause,[],[f288,f214,f75,f68,f72,f235])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    spl3_32 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | (~spl3_6 | ~spl3_8 | ~spl3_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f222,f69])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_8 | ~spl3_32)),
% 0.20/0.49    inference(resolution,[],[f215,f76])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f214])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_25 | spl3_38),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f271,f76])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ~m1_orders_2(sK1,sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f270,f49])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f269,f81])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f268,f69])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f267,f65])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f266,f61])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f265,f57])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_25 | spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f262,f53])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_25 | spl3_38)),
% 0.20/0.49    inference(resolution,[],[f253,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f165])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl3_25 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | spl3_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f252])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl3_32 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f212,f205,f64,f60,f56,f52,f48,f214])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    spl3_31 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_31)),
% 0.20/0.49    inference(subsumption_resolution,[],[f211,f49])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_31)),
% 0.20/0.49    inference(subsumption_resolution,[],[f210,f61])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_31)),
% 0.20/0.49    inference(subsumption_resolution,[],[f209,f57])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_5 | ~spl3_31)),
% 0.20/0.49    inference(subsumption_resolution,[],[f208,f53])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK2(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_5 | ~spl3_31)),
% 0.20/0.49    inference(resolution,[],[f206,f65])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f205])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    spl3_31 | ~spl3_13 | ~spl3_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f202,f199,f97,f205])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl3_13 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_30 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) ) | (~spl3_13 | ~spl3_30)),
% 0.20/0.49    inference(subsumption_resolution,[],[f200,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    spl3_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f199])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl3_29 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f179,f134,f64,f60,f56,f52,f48,f195])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl3_19 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f178,f49])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f177,f61])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f57])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_5 | ~spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f175,f53])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_5 | ~spl3_19)),
% 0.20/0.49    inference(resolution,[],[f135,f65])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) ) | ~spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl3_25 | ~spl3_13 | ~spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f159,f156,f97,f165])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl3_23 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) ) | (~spl3_13 | ~spl3_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f157,f98])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f156])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f156])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl3_21 | ~spl3_13 | ~spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f141,f138,f97,f143])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl3_20 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) ) | (~spl3_13 | ~spl3_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f139,f98])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f138])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f138])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f134])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f97])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f92])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | m1_orders_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 != X2 | m1_orders_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f88])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_orders_2(X1,X0,X0)) )),
% 0.20/0.49    inference(condensation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => ~r2_orders_2(X0,X1,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~spl3_9 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f72,f79])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.49    inference(inner_rewriting,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_7 | spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f75,f72])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f68])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f64])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f60])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f56])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f52])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f48])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22645)------------------------------
% 0.20/0.49  % (22645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22645)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22645)Memory used [KB]: 10874
% 0.20/0.49  % (22645)Time elapsed: 0.076 s
% 0.20/0.49  % (22645)------------------------------
% 0.20/0.49  % (22645)------------------------------
% 0.20/0.49  % (22648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (22634)Success in time 0.139 s
%------------------------------------------------------------------------------
