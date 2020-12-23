%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 321 expanded)
%              Number of leaves         :   28 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  952 (1718 expanded)
%              Number of equality atoms :   66 ( 177 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f71,f76,f80,f88,f104,f108,f112,f125,f129,f135,f151,f158,f175,f211,f229,f239,f258,f279,f294])).

fof(f294,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_17
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f292,f70])).

fof(f70,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_8
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f292,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f291,f43])).

fof(f43,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f291,plain,
    ( v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f290,f75])).

fof(f75,plain,
    ( k1_xboole_0 != sK1
    | spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f290,plain,
    ( k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f289,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f289,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f288,f59])).

fof(f59,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f288,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f287,f55])).

fof(f55,plain,
    ( v5_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f287,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f286,f51])).

fof(f51,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f286,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_17
    | spl3_36 ),
    inference(subsumption_resolution,[],[f284,f47])).

fof(f47,plain,
    ( v3_orders_2(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f284,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_17
    | spl3_36 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_17
    | spl3_36 ),
    inference(resolution,[],[f278,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | v2_struct_0(X0)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_17
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
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f278,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl3_36
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f279,plain,
    ( ~ spl3_36
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_21
    | spl3_34 ),
    inference(avatar_split_clause,[],[f275,f256,f127,f69,f66,f62,f58,f54,f50,f46,f42,f277])).

fof(f127,plain,
    ( spl3_21
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
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f256,plain,
    ( spl3_34
  <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f275,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_8
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f274,f70])).

fof(f274,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f273,f43])).

fof(f273,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f272,f75])).

fof(f272,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f271,f63])).

fof(f271,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f270,f59])).

fof(f270,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f269,f55])).

fof(f269,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f268,f51])).

fof(f268,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_21
    | spl3_34 ),
    inference(subsumption_resolution,[],[f267,f47])).

fof(f267,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_21
    | spl3_34 ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_21
    | spl3_34 ),
    inference(superposition,[],[f257,f128])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | v2_struct_0(X0)
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f127])).

fof(f257,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( ~ spl3_34
    | ~ spl3_6
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f252,f237,f62,f256])).

fof(f237,plain,
    ( spl3_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f252,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | ~ spl3_6
    | ~ spl3_32 ),
    inference(resolution,[],[f238,f63])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl3_32
    | ~ spl3_24
    | spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f231,f227,f209,f149,f237])).

fof(f149,plain,
    ( spl3_24
  <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f209,plain,
    ( spl3_26
  <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f227,plain,
    ( spl3_30
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) )
    | ~ spl3_24
    | spl3_26
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f230,f150])).

fof(f150,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f149])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) )
    | spl3_26
    | ~ spl3_30 ),
    inference(resolution,[],[f228,f210])).

fof(f210,plain,
    ( ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f209])).

fof(f228,plain,
    ( ! [X4,X5] :
        ( r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl3_30
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f197,f149,f102,f58,f54,f50,f46,f42,f227])).

fof(f102,plain,
    ( spl3_16
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
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f197,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f196,f43])).

fof(f196,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f195,f59])).

fof(f195,plain,
    ( ! [X4,X5] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f194,f55])).

fof(f194,plain,
    ( ! [X4,X5] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f193,f51])).

fof(f193,plain,
    ( ! [X4,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f182,f47])).

fof(f182,plain,
    ( ! [X4,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)) )
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(resolution,[],[f150,f103])).

fof(f103,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_orders_2(X0,X1,X2)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f102])).

fof(f211,plain,
    ( ~ spl3_26
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f185,f149,f78,f58,f209])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_orders_2(X0,X2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f185,plain,
    ( ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f178,f59])).

fof(f178,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(resolution,[],[f150,f79])).

fof(f79,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ r2_orders_2(X0,X2,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f175,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f173,f74])).

fof(f74,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_9
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f173,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f172,f43])).

fof(f172,plain,
    ( v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f171,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f170,f55])).

fof(f170,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f169,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f161,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(resolution,[],[f157,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0)
        | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
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

fof(f157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_25
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f158,plain,
    ( spl3_25
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f152,f66,f62,f156])).

fof(f152,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f63,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f151,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f147,f133,f69,f62,f149])).

fof(f133,plain,
    ( spl3_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f147,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f146,f63])).

fof(f146,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(resolution,[],[f134,f70])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl3_22
    | ~ spl3_6
    | spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f131,f123,f66,f62,f133])).

fof(f123,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK1) )
    | ~ spl3_6
    | spl3_7
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f130,f75])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK1) )
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f124,f63])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f129,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f29,f127])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f125,plain,
    ( spl3_20
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f117,f110,f58,f54,f50,f46,f42,f123])).

fof(f110,plain,
    ( spl3_18
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
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f116,f59])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f113,f47])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(resolution,[],[f111,f55])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_orders_2(X2,X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f27,f110])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f108,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f28,f106])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f24,f102])).

fof(f24,plain,(
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
    inference(cnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f88,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 != X2
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f76,plain,
    ( ~ spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f40,f66,f73])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f71,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f13,f69,f66])).

fof(f13,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f15,f62])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f58])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (31007)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.42  % (31007)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f297,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f71,f76,f80,f88,f104,f108,f112,f125,f129,f135,f151,f158,f175,f211,f229,f239,f258,f279,f294])).
% 0.21/0.42  fof(f294,plain,(
% 0.21/0.42    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_17 | spl3_36),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.42  fof(f293,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f292,f70])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    m1_orders_2(sK1,sK0,sK1) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl3_8 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f292,plain,(
% 0.21/0.42    ~m1_orders_2(sK1,sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f291,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f291,plain,(
% 0.21/0.42    v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f290,f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    k1_xboole_0 != sK1 | spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl3_7 <=> k1_xboole_0 = sK1),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f290,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f289,f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f289,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f288,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    l1_orders_2(sK0) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl3_5 <=> l1_orders_2(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f288,plain,(
% 0.21/0.42    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f287,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    v5_orders_2(sK0) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl3_4 <=> v5_orders_2(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f287,plain,(
% 0.21/0.42    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f286,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    v4_orders_2(sK0) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl3_3 <=> v4_orders_2(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f286,plain,(
% 0.21/0.42    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_17 | spl3_36)),
% 0.21/0.42    inference(subsumption_resolution,[],[f284,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    v3_orders_2(sK0) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl3_2 <=> v3_orders_2(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f284,plain,(
% 0.21/0.42    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_17 | spl3_36)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.42  fof(f281,plain,(
% 0.21/0.42    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_17 | spl3_36)),
% 0.21/0.42    inference(resolution,[],[f278,f107])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f106])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    spl3_17 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f278,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl3_36),
% 0.21/0.42    inference(avatar_component_clause,[],[f277])).
% 0.21/0.42  fof(f277,plain,(
% 0.21/0.42    spl3_36 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.42  fof(f279,plain,(
% 0.21/0.42    ~spl3_36 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_21 | spl3_34),
% 0.21/0.42    inference(avatar_split_clause,[],[f275,f256,f127,f69,f66,f62,f58,f54,f50,f46,f42,f277])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    spl3_21 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.42  fof(f256,plain,(
% 0.21/0.42    spl3_34 <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.42  fof(f275,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_8 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f274,f70])).
% 0.21/0.42  fof(f274,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_orders_2(sK1,sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f273,f43])).
% 0.21/0.42  fof(f273,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f272,f75])).
% 0.21/0.42  fof(f272,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f271,f63])).
% 0.21/0.42  fof(f271,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f270,f59])).
% 0.21/0.42  fof(f270,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f269,f55])).
% 0.21/0.42  fof(f269,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f268,f51])).
% 0.21/0.42  fof(f268,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_21 | spl3_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f267,f47])).
% 0.21/0.42  fof(f267,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_21 | spl3_34)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f266])).
% 0.21/0.42  fof(f266,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK1,sK0,sK1) | (~spl3_21 | spl3_34)),
% 0.21/0.42    inference(superposition,[],[f257,f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f127])).
% 0.21/0.42  fof(f257,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | spl3_34),
% 0.21/0.42    inference(avatar_component_clause,[],[f256])).
% 0.21/0.42  fof(f258,plain,(
% 0.21/0.42    ~spl3_34 | ~spl3_6 | ~spl3_32),
% 0.21/0.42    inference(avatar_split_clause,[],[f252,f237,f62,f256])).
% 0.21/0.42  fof(f237,plain,(
% 0.21/0.42    spl3_32 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.42  fof(f252,plain,(
% 0.21/0.42    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | (~spl3_6 | ~spl3_32)),
% 0.21/0.42    inference(resolution,[],[f238,f63])).
% 0.21/0.42  fof(f238,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))) ) | ~spl3_32),
% 0.21/0.42    inference(avatar_component_clause,[],[f237])).
% 0.21/0.42  fof(f239,plain,(
% 0.21/0.42    spl3_32 | ~spl3_24 | spl3_26 | ~spl3_30),
% 0.21/0.42    inference(avatar_split_clause,[],[f231,f227,f209,f149,f237])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl3_24 <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.42  fof(f209,plain,(
% 0.21/0.42    spl3_26 <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.42  fof(f227,plain,(
% 0.21/0.42    spl3_30 <=> ! [X5,X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.42  fof(f231,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))) ) | (~spl3_24 | spl3_26 | ~spl3_30)),
% 0.21/0.42    inference(subsumption_resolution,[],[f230,f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~spl3_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f149])).
% 0.21/0.42  fof(f230,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))) ) | (spl3_26 | ~spl3_30)),
% 0.21/0.42    inference(resolution,[],[f228,f210])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | spl3_26),
% 0.21/0.42    inference(avatar_component_clause,[],[f209])).
% 0.21/0.42  fof(f228,plain,(
% 0.21/0.42    ( ! [X4,X5] : (r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | ~spl3_30),
% 0.21/0.42    inference(avatar_component_clause,[],[f227])).
% 0.21/0.42  fof(f229,plain,(
% 0.21/0.42    spl3_30 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_24),
% 0.21/0.42    inference(avatar_split_clause,[],[f197,f149,f102,f58,f54,f50,f46,f42,f227])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl3_16 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.42  fof(f197,plain,(
% 0.21/0.42    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f196,f43])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    ( ! [X4,X5] : (v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f195,f59])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    ( ! [X4,X5] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f194,f55])).
% 0.21/0.42  fof(f194,plain,(
% 0.21/0.42    ( ! [X4,X5] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (~spl3_2 | ~spl3_3 | ~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f193,f51])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    ( ! [X4,X5] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (~spl3_2 | ~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f182,f47])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    ( ! [X4,X5] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X5,X4))) ) | (~spl3_16 | ~spl3_24)),
% 0.21/0.42    inference(resolution,[],[f150,f103])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) ) | ~spl3_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f102])).
% 0.21/0.42  fof(f211,plain,(
% 0.21/0.42    ~spl3_26 | ~spl3_5 | ~spl3_10 | ~spl3_24),
% 0.21/0.42    inference(avatar_split_clause,[],[f185,f149,f78,f58,f209])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl3_10 <=> ! [X0,X2] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.42  fof(f185,plain,(
% 0.21/0.42    ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | (~spl3_5 | ~spl3_10 | ~spl3_24)),
% 0.21/0.42    inference(subsumption_resolution,[],[f178,f59])).
% 0.21/0.42  fof(f178,plain,(
% 0.21/0.42    ~l1_orders_2(sK0) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | (~spl3_10 | ~spl3_24)),
% 0.21/0.42    inference(resolution,[],[f150,f79])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_orders_2(X0,X2,X2)) ) | ~spl3_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_12 | ~spl3_25),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f173,f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    spl3_9 <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f172,f43])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f171,f59])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f170,f55])).
% 0.21/0.42  fof(f170,plain,(
% 0.21/0.42    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f169,f51])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_2 | ~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(subsumption_resolution,[],[f161,f47])).
% 0.21/0.42  fof(f161,plain,(
% 0.21/0.42    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_12 | ~spl3_25)),
% 0.21/0.42    inference(resolution,[],[f157,f87])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl3_12 <=> ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f157,plain,(
% 0.21/0.43    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f156])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    spl3_25 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.43  fof(f158,plain,(
% 0.21/0.43    spl3_25 | ~spl3_6 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f152,f66,f62,f156])).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_6 | ~spl3_7)),
% 0.21/0.43    inference(backward_demodulation,[],[f63,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f66])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    spl3_24 | ~spl3_6 | ~spl3_8 | ~spl3_22),
% 0.21/0.43    inference(avatar_split_clause,[],[f147,f133,f69,f62,f149])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    spl3_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_6 | ~spl3_8 | ~spl3_22)),
% 0.21/0.43    inference(subsumption_resolution,[],[f146,f63])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_8 | ~spl3_22)),
% 0.21/0.43    inference(resolution,[],[f134,f70])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f133])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    spl3_22 | ~spl3_6 | spl3_7 | ~spl3_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f131,f123,f66,f62,f133])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    spl3_20 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK1)) ) | (~spl3_6 | spl3_7 | ~spl3_20)),
% 0.21/0.43    inference(subsumption_resolution,[],[f130,f75])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK1)) ) | (~spl3_6 | ~spl3_20)),
% 0.21/0.43    inference(resolution,[],[f124,f63])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | ~spl3_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f123])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl3_21),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f127])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    spl3_20 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f117,f110,f58,f54,f50,f46,f42,f123])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    spl3_18 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f116,f59])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f115,f43])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f114,f51])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f113,f47])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,X0)) ) | (~spl3_4 | ~spl3_18)),
% 0.21/0.43    inference(resolution,[],[f111,f55])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) ) | ~spl3_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f110])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    spl3_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f110])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f106])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    spl3_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f102])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f86])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X2,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | m1_orders_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 != X2 | m1_orders_2(X2,X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f39,f78])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.43    inference(equality_resolution,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ~spl3_9 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f40,f66,f73])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 | ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.43    inference(inner_rewriting,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl3_7 | spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f69,f66])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f62])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f58])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    l1_orders_2(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v5_orders_2(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f50])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    v4_orders_2(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f46])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    v3_orders_2(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (31007)------------------------------
% 0.21/0.43  % (31007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (31007)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (31007)Memory used [KB]: 10746
% 0.21/0.43  % (31007)Time elapsed: 0.015 s
% 0.21/0.43  % (31007)------------------------------
% 0.21/0.43  % (31007)------------------------------
% 0.21/0.43  % (30997)Success in time 0.073 s
%------------------------------------------------------------------------------
