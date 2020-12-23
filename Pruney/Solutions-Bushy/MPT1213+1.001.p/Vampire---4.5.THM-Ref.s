%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:29 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 321 expanded)
%              Number of leaves         :   30 ( 136 expanded)
%              Depth                    :   11
%              Number of atoms          :  846 (1498 expanded)
%              Number of equality atoms :   93 ( 188 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f58,f62,f70,f74,f78,f82,f86,f90,f94,f99,f112,f116,f123,f127,f134,f142,f191,f198,f204,f249,f264])).

% (3657)Refutation not found, incomplete strategy% (3657)------------------------------
% (3657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f264,plain,
    ( ~ spl2_26
    | ~ spl2_17
    | ~ spl2_18
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f259,f247,f114,f56,f52,f48,f40,f36,f107,f104,f189])).

fof(f189,plain,
    ( spl2_26
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f104,plain,
    ( spl2_17
  <=> v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f107,plain,
    ( spl2_18
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f36,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,
    ( spl2_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f56,plain,
    ( spl2_6
  <=> sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f114,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_lattices(X0,X2,X1)
        | k7_lattices(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f247,plain,
    ( spl2_32
  <=> r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f259,plain,
    ( ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f258,f57])).

fof(f57,plain,
    ( sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f258,plain,
    ( ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f257,f53])).

fof(f53,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f257,plain,
    ( ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f256,f49])).

fof(f49,plain,
    ( l3_lattices(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f256,plain,
    ( ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f255,f41])).

fof(f41,plain,
    ( v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f255,plain,
    ( ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f250,f37])).

fof(f37,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f250,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ spl2_20
    | ~ spl2_32 ),
    inference(resolution,[],[f248,f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattices(X0,X2,X1)
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k7_lattices(X0,X1) = X2 )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f114])).

fof(f248,plain,
    ( r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl2_32
    | ~ spl2_26
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f212,f202,f186,f140,f125,f80,f76,f52,f48,f36,f189,f247])).

fof(f76,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k1_lattices(X0,X1,X2) = k6_lattices(X0)
        | ~ r2_lattices(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k6_lattices(X0) = k1_lattices(X0,X2,X1)
        | ~ r2_lattices(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f125,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k1_lattices(X0,X1,X2) != k6_lattices(X0)
        | k6_lattices(X0) != k1_lattices(X0,X2,X1)
        | k2_lattices(X0,X1,X2) != k5_lattices(X0)
        | k5_lattices(X0) != k2_lattices(X0,X2,X1)
        | r2_lattices(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f140,plain,
    ( spl2_22
  <=> r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f186,plain,
    ( spl2_25
  <=> k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f202,plain,
    ( spl2_27
  <=> k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f212,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f211,f159])).

fof(f159,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f158,f37])).

fof(f158,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f157,f53])).

fof(f157,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f147,f49])).

fof(f147,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(resolution,[],[f141,f77])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattices(X0,X1,X2)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k1_lattices(X0,X1,X2) = k6_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f141,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f211,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f210,f156])).

fof(f156,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f155,f37])).

fof(f155,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f154,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f146,f49])).

fof(f146,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(resolution,[],[f141,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattices(X0,X1,X2)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k6_lattices(X0) = k1_lattices(X0,X2,X1)
        | v2_struct_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f210,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f209,f37])).

fof(f209,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f208,f187])).

fof(f187,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f186])).

fof(f208,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f206,f49])).

fof(f206,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(superposition,[],[f126,f203])).

fof(f203,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f202])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( k5_lattices(X0) != k2_lattices(X0,X2,X1)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k1_lattices(X0,X1,X2) != k6_lattices(X0)
        | k6_lattices(X0) != k1_lattices(X0,X2,X1)
        | k2_lattices(X0,X1,X2) != k5_lattices(X0)
        | v2_struct_0(X0)
        | r2_lattices(X0,X1,X2) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f125])).

fof(f204,plain,
    ( spl2_27
    | ~ spl2_26
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f153,f140,f84,f52,f48,f36,f189,f202])).

fof(f84,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k2_lattices(X0,X1,X2) = k5_lattices(X0)
        | ~ r2_lattices(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f153,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f152,f37])).

fof(f152,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f151,f53])).

fof(f151,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f145,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(resolution,[],[f141,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattices(X0,X1,X2)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k2_lattices(X0,X1,X2) = k5_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f198,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10
    | spl2_26 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10
    | spl2_26 ),
    inference(subsumption_resolution,[],[f196,f37])).

fof(f196,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10
    | spl2_26 ),
    inference(subsumption_resolution,[],[f195,f53])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_10
    | spl2_26 ),
    inference(subsumption_resolution,[],[f193,f49])).

fof(f193,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_10
    | spl2_26 ),
    inference(resolution,[],[f190,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f190,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl2_25
    | ~ spl2_26
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f150,f140,f88,f52,f48,f36,f189,f186])).

fof(f88,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k5_lattices(X0) = k2_lattices(X0,X2,X1)
        | ~ r2_lattices(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f150,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f149,f37])).

fof(f149,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f148,f53])).

fof(f148,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f144,f49])).

fof(f144,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(resolution,[],[f141,f89])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattices(X0,X1,X2)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k5_lattices(X0) = k2_lattices(X0,X2,X1)
        | v2_struct_0(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f142,plain,
    ( spl2_22
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f135,f110,f52,f140])).

fof(f110,plain,
    ( spl2_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattices(sK0,k7_lattices(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f135,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(resolution,[],[f111,f53])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattices(sK0,k7_lattices(sK0,X0),X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f110])).

fof(f134,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | spl2_18 ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,
    ( ~ l3_lattices(sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_7
    | spl2_18 ),
    inference(subsumption_resolution,[],[f131,f45])).

fof(f45,plain,
    ( v17_lattices(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f131,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_1
    | ~ spl2_7
    | spl2_18 ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f129,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl2_7
    | spl2_18 ),
    inference(resolution,[],[f108,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( v11_lattices(X0)
        | v2_struct_0(X0)
        | ~ v17_lattices(X0)
        | ~ l3_lattices(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ l3_lattices(X0)
        | v2_struct_0(X0)
        | ~ v17_lattices(X0)
        | v11_lattices(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f108,plain,
    ( ~ v11_lattices(sK0)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f107])).

fof(f127,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f32,f125])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != k6_lattices(X0)
      | k6_lattices(X0) != k1_lattices(X0,X2,X1)
      | k2_lattices(X0,X1,X2) != k5_lattices(X0)
      | k5_lattices(X0) != k2_lattices(X0,X2,X1)
      | r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).

fof(f123,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9
    | spl2_17 ),
    inference(subsumption_resolution,[],[f121,f49])).

fof(f121,plain,
    ( ~ l3_lattices(sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_9
    | spl2_17 ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_1
    | ~ spl2_9
    | spl2_17 ),
    inference(subsumption_resolution,[],[f118,f37])).

fof(f118,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl2_9
    | spl2_17 ),
    inference(resolution,[],[f105,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( v16_lattices(X0)
        | v2_struct_0(X0)
        | ~ v17_lattices(X0)
        | ~ l3_lattices(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X0] :
        ( ~ l3_lattices(X0)
        | v2_struct_0(X0)
        | ~ v17_lattices(X0)
        | v16_lattices(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f105,plain,
    ( ~ v16_lattices(sK0)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f116,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f26,f114])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).

fof(f112,plain,
    ( ~ spl2_17
    | ~ spl2_18
    | spl2_19
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f102,f97,f48,f40,f36,f110,f107,f104])).

fof(f97,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | r2_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v11_lattices(sK0)
        | ~ v16_lattices(sK0)
        | r2_lattices(sK0,k7_lattices(sK0,X0),X0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v11_lattices(sK0)
        | ~ v16_lattices(sK0)
        | ~ l3_lattices(sK0)
        | r2_lattices(sK0,k7_lattices(sK0,X0),X0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f100,f37])).

fof(f100,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v11_lattices(sK0)
        | ~ v16_lattices(sK0)
        | ~ l3_lattices(sK0)
        | r2_lattices(sK0,k7_lattices(sK0,X0),X0) )
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(resolution,[],[f98,f41])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | r2_lattices(X0,k7_lattices(X0,X1),X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f95,f92,f72,f97])).

fof(f92,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
        | r2_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | r2_lattices(X0,k7_lattices(X0,X1),X1) )
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f93,f73])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v10_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
        | r2_lattices(X0,k7_lattices(X0,X1),X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | r2_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f31,f88])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f29,f80])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k6_lattices(X0)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f62,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f18,f56])).

fof(f18,plain,(
    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

% (3657)Termination reason: Refutation not found, incomplete strategy
fof(f5,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

% (3657)Memory used [KB]: 10618
fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f52])).

% (3657)Time elapsed: 0.045 s
fof(f17,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

% (3657)------------------------------
% (3657)------------------------------
fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
