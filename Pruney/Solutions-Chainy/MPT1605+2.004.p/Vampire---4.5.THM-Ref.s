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
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 273 expanded)
%              Number of leaves         :   44 ( 125 expanded)
%              Depth                    :    7
%              Number of atoms          :  701 (1080 expanded)
%              Number of equality atoms :   67 ( 126 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f97,f105,f109,f113,f117,f121,f133,f138,f143,f147,f155,f191,f216,f228,f235,f247,f268,f272,f315,f342,f356,f374,f380,f417,f433,f451])).

fof(f451,plain,
    ( spl4_3
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl4_3
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f449,f108])).

fof(f108,plain,
    ( ! [X0] : l1_orders_2(k2_yellow_1(X0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_10
  <=> ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f449,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_3
    | ~ spl4_18
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f444,f80])).

fof(f80,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_3
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f444,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl4_18
    | ~ spl4_66 ),
    inference(superposition,[],[f142,f432])).

fof(f432,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl4_66
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f142,plain,
    ( ! [X0] :
        ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f433,plain,
    ( spl4_66
    | ~ spl4_17
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f424,f415,f136,f431])).

fof(f136,plain,
    ( spl4_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f415,plain,
    ( spl4_63
  <=> ! [X1] :
        ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1)
        | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f424,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl4_17
    | ~ spl4_63 ),
    inference(resolution,[],[f416,f137])).

fof(f137,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f416,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1) )
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f415])).

fof(f417,plain,
    ( spl4_63
    | ~ spl4_58
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_19
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f391,f369,f145,f111,f107,f372,f415])).

fof(f372,plain,
    ( spl4_58
  <=> m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f111,plain,
    ( spl4_11
  <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f145,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(sK1(X0,X1,X2),X1)
        | r2_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f369,plain,
    ( spl4_57
  <=> ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,sK0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1)
        | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1) )
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_19
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f390,f112])).

fof(f112,plain,
    ( ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f390,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1)
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
        | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1) )
    | ~ spl4_10
    | ~ spl4_19
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f386,f108])).

fof(f386,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1)
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
        | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1)
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_19
    | ~ spl4_57 ),
    inference(resolution,[],[f370,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(sK1(X0,X1,X2),X1)
        | ~ l1_orders_2(X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f369])).

fof(f380,plain,
    ( ~ spl4_2
    | ~ spl4_16
    | spl4_58 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_16
    | spl4_58 ),
    inference(subsumption_resolution,[],[f377,f76])).

fof(f76,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f377,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | ~ spl4_16
    | spl4_58 ),
    inference(resolution,[],[f373,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f373,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f372])).

fof(f374,plain,
    ( spl4_57
    | ~ spl4_58
    | ~ spl4_5
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f361,f354,f87,f372,f369])).

fof(f87,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f354,plain,
    ( spl4_54
  <=> ! [X1,X0] :
        ( k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl4_5
    | ~ spl4_54 ),
    inference(resolution,[],[f355,f88])).

fof(f88,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | k1_yellow_0(k2_yellow_1(sK0),X0) = X1 )
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f354])).

fof(f356,plain,
    ( spl4_54
    | spl4_1
    | ~ spl4_21
    | ~ spl4_40
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f348,f340,f266,f153,f71,f354])).

fof(f71,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f153,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X1,X2)
        | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f266,plain,
    ( spl4_40
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f340,plain,
    ( spl4_52
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1))
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) )
    | spl4_1
    | ~ spl4_21
    | ~ spl4_40
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f347,f267])).

fof(f267,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f266])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0) )
    | spl4_1
    | ~ spl4_21
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f346,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | v1_xboole_0(sK0)
        | ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0) )
    | ~ spl4_21
    | ~ spl4_52 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK0)
        | ~ r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0))
        | ~ m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0) )
    | ~ spl4_21
    | ~ spl4_52 ),
    inference(resolution,[],[f341,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( r3_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f341,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1))
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f340])).

fof(f342,plain,
    ( spl4_52
    | spl4_1
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f316,f313,f71,f340])).

fof(f313,plain,
    ( spl4_48
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X2,X0)
        | k1_yellow_0(k2_yellow_1(X0),X1) = X2
        | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1))
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0) )
    | spl4_1
    | ~ spl4_48 ),
    inference(resolution,[],[f314,f72])).

fof(f314,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X0)
        | k1_yellow_0(k2_yellow_1(X0),X1) = X2
        | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f313])).

fof(f315,plain,
    ( spl4_48
    | ~ spl4_38
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f277,f270,f266,f245,f313])).

fof(f245,plain,
    ( spl4_38
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(X2,X1)
        | r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f270,plain,
    ( spl4_41
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X2,X0)
        | k1_yellow_0(k2_yellow_1(X0),X1) = X2
        | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
        | v1_xboole_0(X0) )
    | ~ spl4_38
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f276,f267])).

fof(f276,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X2,X0)
        | k1_yellow_0(k2_yellow_1(X0),X1) = X2
        | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)
        | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
        | v1_xboole_0(X0) )
    | ~ spl4_38
    | ~ spl4_41 ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X2,X0)
        | k1_yellow_0(k2_yellow_1(X0),X1) = X2
        | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)
        | ~ m1_subset_1(X2,X0)
        | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
        | v1_xboole_0(X0) )
    | ~ spl4_38
    | ~ spl4_41 ),
    inference(resolution,[],[f271,f246])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ m1_subset_1(X2,X1)
        | ~ m1_subset_1(X0,X1)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | v1_xboole_0(X1) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f245])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2))
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ m1_subset_1(X1,X0)
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl4_41
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f238,f226,f111,f107,f103,f270])).

fof(f103,plain,
    ( spl4_9
  <=> ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f226,plain,
    ( spl4_35
  <=> ! [X1,X0,X2] :
        ( ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
        | k1_yellow_0(X0,X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f237,f112])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f236,f108])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(resolution,[],[f227,f104])).

fof(f104,plain,
    ( ! [X0] : v5_orders_2(k2_yellow_1(X0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
        | k1_yellow_0(X0,X2) = X1 )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f226])).

fof(f268,plain,
    ( spl4_40
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f231,f214,f111,f107,f103,f266])).

fof(f214,plain,
    ( spl4_32
  <=> ! [X1,X0,X2] :
        ( ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | k1_yellow_0(X0,X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f230,f104])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ v5_orders_2(k2_yellow_1(X0))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f229,f108])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
        | ~ l1_orders_2(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
        | ~ v5_orders_2(k2_yellow_1(X0))
        | k1_yellow_0(k2_yellow_1(X0),X2) = X1 )
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(superposition,[],[f215,f112])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | ~ v5_orders_2(X0)
        | k1_yellow_0(X0,X2) = X1 )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f247,plain,
    ( spl4_38
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f239,f233,f115,f245])).

fof(f115,plain,
    ( spl4_12
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f233,plain,
    ( spl4_36
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(X2,X1)
        | r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | v1_xboole_0(X1) )
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(resolution,[],[f234,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(k2_yellow_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,X0)
        | ~ m1_subset_1(X2,X0)
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f235,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f212,f189,f111,f107,f95,f233])).

fof(f95,plain,
    ( spl4_7
  <=> ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f189,plain,
    ( spl4_30
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f211,f112])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f210,f112])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f209,f96])).

fof(f96,plain,
    ( ! [X0] : v3_orders_2(k2_yellow_1(X0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(k2_yellow_1(X0))
        | v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(resolution,[],[f190,f108])).

fof(f190,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f189])).

fof(f228,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f57,f226])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f216,plain,(
    spl4_32 ),
    inference(avatar_split_clause,[],[f55,f214])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f191,plain,(
    spl4_30 ),
    inference(avatar_split_clause,[],[f63,f189])).

% (3132)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f155,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f69,f153])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f44,f40])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f147,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f49,f145])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f143,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f46,f141])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f138,plain,
    ( spl4_17
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f134,f119,f83,f136])).

fof(f83,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f120,f84])).

fof(f84,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f133,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f61,f131])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f121,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f60,f119])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f113,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f111])).

fof(f109,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f39,f107])).

fof(f39,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f105,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f37,f103])).

fof(f37,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f97,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f77,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:54:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3129)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (3137)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (3137)Refutation not found, incomplete strategy% (3137)------------------------------
% 0.21/0.48  % (3137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3137)Memory used [KB]: 1663
% 0.21/0.48  % (3137)Time elapsed: 0.059 s
% 0.21/0.48  % (3137)------------------------------
% 0.21/0.48  % (3137)------------------------------
% 0.21/0.48  % (3141)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (3133)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (3131)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3139)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (3139)Refutation not found, incomplete strategy% (3139)------------------------------
% 0.21/0.49  % (3139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3139)Memory used [KB]: 6140
% 0.21/0.49  % (3139)Time elapsed: 0.004 s
% 0.21/0.49  % (3139)------------------------------
% 0.21/0.49  % (3139)------------------------------
% 0.21/0.50  % (3125)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (3125)Refutation not found, incomplete strategy% (3125)------------------------------
% 0.21/0.50  % (3125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3125)Memory used [KB]: 10618
% 0.21/0.50  % (3125)Time elapsed: 0.079 s
% 0.21/0.50  % (3125)------------------------------
% 0.21/0.50  % (3125)------------------------------
% 0.21/0.50  % (3126)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (3128)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (3127)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3133)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f452,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f97,f105,f109,f113,f117,f121,f133,f138,f143,f147,f155,f191,f216,f228,f235,f247,f268,f272,f315,f342,f356,f374,f380,f417,f433,f451])).
% 0.21/0.51  fof(f451,plain,(
% 0.21/0.51    spl4_3 | ~spl4_10 | ~spl4_18 | ~spl4_66),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f450])).
% 0.21/0.51  fof(f450,plain,(
% 0.21/0.51    $false | (spl4_3 | ~spl4_10 | ~spl4_18 | ~spl4_66)),
% 0.21/0.51    inference(subsumption_resolution,[],[f449,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) ) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl4_10 <=> ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    ~l1_orders_2(k2_yellow_1(sK0)) | (spl4_3 | ~spl4_18 | ~spl4_66)),
% 0.21/0.51    inference(subsumption_resolution,[],[f444,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl4_3 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f444,plain,(
% 0.21/0.51    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | (~spl4_18 | ~spl4_66)),
% 0.21/0.51    inference(superposition,[],[f142,f432])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~spl4_66),
% 0.21/0.51    inference(avatar_component_clause,[],[f431])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    spl4_66 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) ) | ~spl4_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl4_18 <=> ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    spl4_66 | ~spl4_17 | ~spl4_63),
% 0.21/0.51    inference(avatar_split_clause,[],[f424,f415,f136,f431])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl4_17 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    spl4_63 <=> ! [X1] : (k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1) | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | (~spl4_17 | ~spl4_63)),
% 0.21/0.51    inference(resolution,[],[f416,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1)) ) | ~spl4_63),
% 0.21/0.51    inference(avatar_component_clause,[],[f415])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    spl4_63 | ~spl4_58 | ~spl4_10 | ~spl4_11 | ~spl4_19 | ~spl4_57),
% 0.21/0.51    inference(avatar_split_clause,[],[f391,f369,f145,f111,f107,f372,f415])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    spl4_58 <=> m1_subset_1(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl4_11 <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl4_19 <=> ! [X1,X0,X2] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    spl4_57 <=> ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1) | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1)) ) | (~spl4_10 | ~spl4_11 | ~spl4_19 | ~spl4_57)),
% 0.21/0.51    inference(forward_demodulation,[],[f390,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) ) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1)) ) | (~spl4_10 | ~spl4_19 | ~spl4_57)),
% 0.21/0.51    inference(subsumption_resolution,[],[f386,f108])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X1) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(sK1(k2_yellow_1(sK0),X1,k1_xboole_0),X1) | ~l1_orders_2(k2_yellow_1(sK0))) ) | (~spl4_19 | ~spl4_57)),
% 0.21/0.51    inference(resolution,[],[f370,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK1(X0,X1,X2),X1) | ~l1_orders_2(X0)) ) | ~spl4_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0)) ) | ~spl4_57),
% 0.21/0.51    inference(avatar_component_clause,[],[f369])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ~spl4_2 | ~spl4_16 | spl4_58),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f379])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    $false | (~spl4_2 | ~spl4_16 | spl4_58)),
% 0.21/0.51    inference(subsumption_resolution,[],[f377,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    r2_hidden(k1_xboole_0,sK0) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl4_2 <=> r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ~r2_hidden(k1_xboole_0,sK0) | (~spl4_16 | spl4_58)),
% 0.21/0.51    inference(resolution,[],[f373,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl4_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl4_16 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,sK0) | spl4_58),
% 0.21/0.51    inference(avatar_component_clause,[],[f372])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    spl4_57 | ~spl4_58 | ~spl4_5 | ~spl4_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f361,f354,f87,f372,f369])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl4_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    spl4_54 <=> ! [X1,X0] : (k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0)) ) | (~spl4_5 | ~spl4_54)),
% 0.21/0.51    inference(resolution,[],[f355,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | k1_yellow_0(k2_yellow_1(sK0),X0) = X1) ) | ~spl4_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f354])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    spl4_54 | spl4_1 | ~spl4_21 | ~spl4_40 | ~spl4_52),
% 0.21/0.51    inference(avatar_split_clause,[],[f348,f340,f266,f153,f71,f354])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl4_1 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl4_21 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl4_40 <=> ! [X1,X0,X2] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    spl4_52 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1)) | ~r2_lattice3(k2_yellow_1(sK0),X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0))) ) | (spl4_1 | ~spl4_21 | ~spl4_40 | ~spl4_52)),
% 0.21/0.51    inference(subsumption_resolution,[],[f347,f267])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | ~spl4_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f266])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0)) ) | (spl4_1 | ~spl4_21 | ~spl4_52)),
% 0.21/0.51    inference(subsumption_resolution,[],[f346,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | v1_xboole_0(sK0) | ~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0)) ) | (~spl4_21 | ~spl4_52)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f344])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | v1_xboole_0(sK0) | ~r1_tarski(X1,sK2(k2_yellow_1(sK0),X1,X0)) | ~m1_subset_1(sK2(k2_yellow_1(sK0),X1,X0),sK0)) ) | (~spl4_21 | ~spl4_52)),
% 0.21/0.51    inference(resolution,[],[f341,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) ) | ~spl4_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1)) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~m1_subset_1(X0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X1,X0)) ) | ~spl4_52),
% 0.21/0.51    inference(avatar_component_clause,[],[f340])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    spl4_52 | spl4_1 | ~spl4_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f316,f313,f71,f340])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    spl4_48 <=> ! [X1,X0,X2] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~r3_orders_2(k2_yellow_1(sK0),X0,sK2(k2_yellow_1(sK0),X0,X1)) | ~r2_lattice3(k2_yellow_1(sK0),X1,X0)) ) | (spl4_1 | ~spl4_48)),
% 0.21/0.51    inference(resolution,[],[f314,f72])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) | ~r2_lattice3(k2_yellow_1(X0),X1,X2)) ) | ~spl4_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f313])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    spl4_48 | ~spl4_38 | ~spl4_40 | ~spl4_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f277,f270,f266,f245,f313])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl4_38 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | v1_xboole_0(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl4_41 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) ) | (~spl4_38 | ~spl4_40 | ~spl4_41)),
% 0.21/0.51    inference(subsumption_resolution,[],[f276,f267])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) ) | (~spl4_38 | ~spl4_41)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) ) | (~spl4_38 | ~spl4_41)),
% 0.21/0.51    inference(resolution,[],[f271,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X1),X0,X2) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | v1_xboole_0(X1)) ) | ~spl4_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f245])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | ~spl4_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl4_41 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f238,f226,f111,f107,f103,f270])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl4_9 <=> ! [X0] : v5_orders_2(k2_yellow_1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    spl4_35 <=> ! [X1,X0,X2] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_35)),
% 0.21/0.51    inference(forward_demodulation,[],[f237,f112])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_9 | ~spl4_10 | ~spl4_35)),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f108])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK2(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_9 | ~spl4_35)),
% 0.21/0.51    inference(resolution,[],[f227,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) ) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1) ) | ~spl4_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f226])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    spl4_40 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f231,f214,f111,f107,f103,f266])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl4_32 <=> ! [X1,X0,X2] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f230,f104])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~v5_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_10 | ~spl4_11 | ~spl4_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f229,f108])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~v5_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) ) | (~spl4_11 | ~spl4_32)),
% 0.21/0.51    inference(superposition,[],[f215,f112])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~v5_orders_2(X0) | k1_yellow_0(X0,X2) = X1) ) | ~spl4_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f214])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl4_38 | ~spl4_12 | ~spl4_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f233,f115,f245])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl4_12 <=> ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    spl4_36 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | v1_xboole_0(X1)) ) | (~spl4_12 | ~spl4_36)),
% 0.21/0.51    inference(resolution,[],[f234,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) ) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | ~spl4_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f233])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    spl4_36 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f212,f189,f111,f107,f95,f233])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl4_7 <=> ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl4_30 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 0.21/0.51    inference(forward_demodulation,[],[f211,f112])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_30)),
% 0.21/0.51    inference(forward_demodulation,[],[f210,f112])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_7 | ~spl4_10 | ~spl4_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f209,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) ) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_10 | ~spl4_30)),
% 0.21/0.51    inference(resolution,[],[f190,f108])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) ) | ~spl4_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl4_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f226])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.51    inference(rectify,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f214])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl4_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f189])).
% 0.21/0.51  % (3132)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl4_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f69,f153])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f68,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f44,f40])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl4_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f145])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl4_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f141])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl4_17 | ~spl4_4 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f134,f119,f83,f136])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl4_13 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_4 | ~spl4_13)),
% 0.21/0.51    inference(resolution,[],[f120,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | ~spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl4_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f131])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f119])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f115])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f111])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f107])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f103])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl4_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f95])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f87])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f83])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f79])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f75])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3133)------------------------------
% 0.21/0.51  % (3133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3133)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3133)Memory used [KB]: 10874
% 0.21/0.51  % (3133)Time elapsed: 0.078 s
% 0.21/0.51  % (3133)------------------------------
% 0.21/0.51  % (3133)------------------------------
% 0.21/0.51  % (3127)Refutation not found, incomplete strategy% (3127)------------------------------
% 0.21/0.51  % (3127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3127)Memory used [KB]: 10618
% 0.21/0.51  % (3127)Time elapsed: 0.090 s
% 0.21/0.51  % (3127)------------------------------
% 0.21/0.51  % (3127)------------------------------
% 0.21/0.51  % (3140)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (3123)Success in time 0.152 s
%------------------------------------------------------------------------------
