%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  322 ( 635 expanded)
%              Number of leaves         :   71 ( 288 expanded)
%              Depth                    :   14
%              Number of atoms          : 1708 (3456 expanded)
%              Number of equality atoms :   69 ( 135 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21630)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f460,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f163,f168,f172,f176,f181,f185,f191,f195,f199,f205,f215,f219,f224,f228,f235,f239,f242,f258,f262,f269,f274,f280,f299,f313,f317,f329,f339,f344,f348,f363,f385,f404,f413,f430,f449,f457,f459])).

fof(f459,plain,
    ( spl4_32
    | ~ spl4_33
    | ~ spl4_22
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f458,f380,f161,f210,f207])).

fof(f207,plain,
    ( spl4_32
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f210,plain,
    ( spl4_33
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f161,plain,
    ( spl4_22
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f380,plain,
    ( spl4_57
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f458,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_22
    | ~ spl4_57 ),
    inference(resolution,[],[f381,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f381,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f380])).

fof(f457,plain,
    ( ~ spl4_33
    | ~ spl4_61
    | ~ spl4_8
    | ~ spl4_10
    | spl4_19
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f456,f447,f197,f193,f189,f149,f113,f105,f399,f210])).

fof(f399,plain,
    ( spl4_61
  <=> m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f105,plain,
    ( spl4_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( spl4_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f149,plain,
    ( spl4_19
  <=> r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f189,plain,
    ( spl4_28
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f193,plain,
    ( spl4_29
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f197,plain,
    ( spl4_30
  <=> ! [X1,X0,X2] :
        ( ~ v5_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f447,plain,
    ( spl4_65
  <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f456,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_8
    | ~ spl4_10
    | spl4_19
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f455,f194])).

fof(f194,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f193])).

fof(f455,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_10
    | spl4_19
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f454,f190])).

fof(f190,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f189])).

fof(f454,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_10
    | spl4_19
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f453,f194])).

fof(f453,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_10
    | spl4_19
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f452,f106])).

fof(f106,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f105])).

% (21639)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f452,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl4_10
    | spl4_19
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f451,f114])).

fof(f114,plain,
    ( v2_lattice3(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f451,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl4_19
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f450,f150])).

fof(f150,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f450,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl4_30
    | ~ spl4_65 ),
    inference(superposition,[],[f448,f198])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
        | ~ v2_lattice3(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_orders_2(X0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f197])).

fof(f448,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f447])).

fof(f449,plain,
    ( spl4_32
    | ~ spl4_33
    | spl4_65
    | spl4_1
    | ~ spl4_13
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f441,f428,f203,f193,f189,f125,f77,f447,f210,f207])).

fof(f77,plain,
    ( spl4_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f125,plain,
    ( spl4_13
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f203,plain,
    ( spl4_31
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f428,plain,
    ( spl4_64
  <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f441,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f440,f190])).

fof(f440,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_29
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f439,f194])).

fof(f439,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f438,f126])).

fof(f126,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f438,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f432,f78])).

fof(f78,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f432,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_31
    | ~ spl4_64 ),
    inference(superposition,[],[f429,f204])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f203])).

fof(f429,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f428])).

fof(f430,plain,
    ( ~ spl4_61
    | ~ spl4_48
    | spl4_64
    | ~ spl4_28
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f416,f402,f383,f189,f428,f302,f399])).

fof(f302,plain,
    ( spl4_48
  <=> v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f383,plain,
    ( spl4_58
  <=> ! [X3,X2] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f402,plain,
    ( spl4_62
  <=> r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f416,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_28
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f414,f190])).

fof(f414,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(superposition,[],[f403,f384])).

fof(f384,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f383])).

fof(f403,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f402])).

fof(f413,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(subsumption_resolution,[],[f411,f78])).

fof(f411,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(subsumption_resolution,[],[f410,f82])).

fof(f82,plain,
    ( v4_orders_2(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_2
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f410,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(subsumption_resolution,[],[f409,f86])).

fof(f86,plain,
    ( v7_waybel_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_3
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f409,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(subsumption_resolution,[],[f408,f122])).

fof(f122,plain,
    ( v3_yellow_6(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_12
  <=> v3_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f408,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_13
    | ~ spl4_42
    | spl4_61 ),
    inference(subsumption_resolution,[],[f406,f126])).

fof(f406,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_42
    | spl4_61 ),
    inference(resolution,[],[f400,f257])).

fof(f257,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_42
  <=> ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f400,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | spl4_61 ),
    inference(avatar_component_clause,[],[f399])).

fof(f404,plain,
    ( ~ spl4_61
    | ~ spl4_48
    | ~ spl4_33
    | spl4_32
    | spl4_62
    | ~ spl4_50
    | ~ spl4_51
    | ~ spl4_22
    | ~ spl4_29
    | ~ spl4_38
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f374,f361,f237,f193,f161,f311,f308,f402,f207,f210,f302,f399])).

fof(f308,plain,
    ( spl4_50
  <=> v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f311,plain,
    ( spl4_51
  <=> m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f237,plain,
    ( spl4_38
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | v2_struct_0(X1)
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        | ~ m1_subset_1(X3,X0)
        | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f361,plain,
    ( spl4_55
  <=> r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f374,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_22
    | ~ spl4_29
    | ~ spl4_38
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f373,f194])).

fof(f373,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_22
    | ~ spl4_29
    | ~ spl4_38
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f372,f194])).

fof(f372,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_22
    | ~ spl4_38
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f370,f162])).

fof(f370,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_38
    | ~ spl4_55 ),
    inference(superposition,[],[f362,f238])).

fof(f238,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
        | v2_struct_0(X1)
        | ~ l1_orders_2(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f237])).

fof(f362,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f361])).

fof(f385,plain,
    ( spl4_57
    | spl4_58
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f354,f346,f233,f226,f213,f383,f380])).

fof(f213,plain,
    ( spl4_34
  <=> ! [X1] :
        ( v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f226,plain,
    ( spl4_36
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f233,plain,
    ( spl4_37
  <=> ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f346,plain,
    ( spl4_54
  <=> ! [X1,X0] :
        ( k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f354,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f353,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f233])).

fof(f353,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | ~ m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_34
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f352,f214])).

fof(f214,plain,
    ( ! [X1] :
        ( v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k2_struct_0(sK0)) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f213])).

fof(f352,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | ~ v1_funct_2(k4_waybel_1(sK0,X2),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,k2_struct_0(sK0))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ v1_funct_1(k4_waybel_1(sK0,X2))
        | ~ v1_funct_2(k4_waybel_1(sK0,X2),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(superposition,[],[f347,f227])).

fof(f227,plain,
    ( ! [X2,X0,X3,X1] :
        ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f226])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k2_struct_0(sK0)) )
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f346])).

fof(f363,plain,
    ( spl4_55
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f359,f305,f125,f121,f85,f81,f77,f361])).

fof(f305,plain,
    ( spl4_49
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f359,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f358,f82])).

fof(f358,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v4_orders_2(sK1)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f357,f86])).

fof(f357,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f356,f122])).

fof(f356,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | spl4_1
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f355,f78])).

fof(f355,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(resolution,[],[f306,f126])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))
        | v2_struct_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f305])).

fof(f348,plain,
    ( spl4_32
    | spl4_54
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f324,f315,f193,f117,f346,f207])).

fof(f117,plain,
    ( spl4_11
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f315,plain,
    ( spl4_52
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2)
        | ~ l1_waybel_9(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f323,f194])).

fof(f323,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | v2_struct_0(sK0) )
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f322,f194])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | v2_struct_0(sK0) )
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f321,f194])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | v2_struct_0(sK0) )
    | ~ spl4_11
    | ~ spl4_52 ),
    inference(resolution,[],[f316,f118])).

fof(f118,plain,
    ( l1_waybel_9(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_9(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2)
        | v2_struct_0(X0) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f315])).

fof(f344,plain,
    ( ~ spl4_28
    | ~ spl4_37
    | spl4_51 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl4_28
    | ~ spl4_37
    | spl4_51 ),
    inference(subsumption_resolution,[],[f341,f190])).

fof(f341,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_37
    | spl4_51 ),
    inference(resolution,[],[f312,f234])).

fof(f312,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f311])).

fof(f339,plain,
    ( ~ spl4_28
    | ~ spl4_34
    | spl4_50 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl4_28
    | ~ spl4_34
    | spl4_50 ),
    inference(subsumption_resolution,[],[f336,f190])).

fof(f336,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_34
    | spl4_50 ),
    inference(resolution,[],[f309,f214])).

fof(f309,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f308])).

fof(f329,plain,
    ( spl4_32
    | ~ spl4_33
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_29
    | spl4_48 ),
    inference(avatar_split_clause,[],[f320,f302,f193,f189,f166,f210,f207])).

fof(f166,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v1_funct_1(k4_waybel_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f320,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_29
    | spl4_48 ),
    inference(subsumption_resolution,[],[f319,f190])).

fof(f319,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_23
    | ~ spl4_29
    | spl4_48 ),
    inference(forward_demodulation,[],[f318,f194])).

fof(f318,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_23
    | spl4_48 ),
    inference(resolution,[],[f303,f167])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k4_waybel_1(X0,X1))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f166])).

fof(f303,plain,
    ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f302])).

fof(f317,plain,
    ( spl4_52
    | ~ spl4_17
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f275,f267,f141,f315])).

fof(f141,plain,
    ( spl4_17
  <=> ! [X0] :
        ( ~ l1_waybel_9(X0)
        | l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f267,plain,
    ( spl4_44
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2)
        | ~ l1_waybel_9(X0) )
    | ~ spl4_17
    | ~ spl4_44 ),
    inference(resolution,[],[f268,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( l1_orders_2(X0)
        | ~ l1_waybel_9(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f268,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f267])).

fof(f313,plain,
    ( ~ spl4_48
    | spl4_49
    | ~ spl4_50
    | ~ spl4_51
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f300,f297,f133,f311,f308,f305,f302])).

fof(f133,plain,
    ( spl4_15
  <=> v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f297,plain,
    ( spl4_47
  <=> ! [X1,X0] :
        ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v5_pre_topc(X1,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) )
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(resolution,[],[f298,f134])).

fof(f134,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl4_47
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f295,f278,f193,f117,f113,f109,f105,f101,f97,f93,f89,f297])).

fof(f89,plain,
    ( spl4_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f93,plain,
    ( spl4_5
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( spl4_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( spl4_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f109,plain,
    ( spl4_9
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f278,plain,
    ( spl4_45
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_waybel_9(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X0,X0)
        | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v5_pre_topc(X1,sK0,sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f294,f194])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f293,f194])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_29
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f292,f194])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f291,f118])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f290,f114])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f289,f110])).

fof(f110,plain,
    ( v1_lattice3(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f288,f106])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f287,f102])).

fof(f102,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f286,f90])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f285,f94])).

% (21633)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f94,plain,
    ( v8_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X1,sK0,sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) )
    | ~ spl4_6
    | ~ spl4_45 ),
    inference(resolution,[],[f279,f98])).

fof(f98,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f279,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_waybel_9(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X0,X0)
        | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,(
    spl4_45 ),
    inference(avatar_split_clause,[],[f67,f278])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X0,X0)
      | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X0)
               => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).

fof(f274,plain,
    ( ~ spl4_11
    | ~ spl4_16
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_16
    | spl4_41 ),
    inference(subsumption_resolution,[],[f271,f118])).

fof(f271,plain,
    ( ~ l1_waybel_9(sK0)
    | ~ spl4_16
    | spl4_41 ),
    inference(resolution,[],[f254,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( l1_pre_topc(X0)
        | ~ l1_waybel_9(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ l1_waybel_9(X0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f254,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_41
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f269,plain,
    ( spl4_44
    | ~ spl4_23
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f265,f260,f179,f174,f166,f267])).

fof(f174,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f179,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f260,plain,
    ( spl4_43
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_funct_1(k4_waybel_1(X0,X1))
        | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f265,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) )
    | ~ spl4_23
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f264,f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f179])).

fof(f264,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) )
    | ~ spl4_23
    | ~ spl4_25
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f263,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f174])).

fof(f263,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) )
    | ~ spl4_23
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f261,f167])).

fof(f261,plain,
    ( ! [X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_funct_1(k4_waybel_1(X0,X1))
        | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f260])).

fof(f262,plain,(
    spl4_43 ),
    inference(avatar_split_clause,[],[f75,f260])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
      | k4_waybel_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).

fof(f258,plain,
    ( spl4_32
    | ~ spl4_41
    | spl4_42
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_29
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f231,f217,f193,f93,f89,f256,f253,f207])).

fof(f217,plain,
    ( spl4_35
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f231,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_29
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f230,f94])).

fof(f230,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ v8_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_29
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f229,f90])).

fof(f229,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_29
    | ~ spl4_35 ),
    inference(superposition,[],[f218,f194])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f217])).

fof(f242,plain,
    ( ~ spl4_33
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f241,f207,f153,f109,f210])).

fof(f153,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f241,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f240,f110])).

fof(f240,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl4_20
    | ~ spl4_32 ),
    inference(resolution,[],[f208,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ v1_lattice3(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f207])).

fof(f239,plain,(
    spl4_38 ),
    inference(avatar_split_clause,[],[f73,f237])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ m1_subset_1(X3,X0)
      | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        & v1_funct_2(X2,X0,u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(f235,plain,
    ( spl4_32
    | ~ spl4_33
    | spl4_37
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f200,f193,f179,f233,f210,f207])).

fof(f200,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(superposition,[],[f180,f194])).

fof(f228,plain,(
    spl4_36 ),
    inference(avatar_split_clause,[],[f74,f226])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f224,plain,
    ( ~ spl4_11
    | ~ spl4_17
    | spl4_33 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_17
    | spl4_33 ),
    inference(subsumption_resolution,[],[f221,f118])).

fof(f221,plain,
    ( ~ l1_waybel_9(sK0)
    | ~ spl4_17
    | spl4_33 ),
    inference(resolution,[],[f211,f142])).

fof(f211,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f219,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f68,f217])).

% (21631)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f68,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f215,plain,
    ( spl4_32
    | ~ spl4_33
    | spl4_34
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f201,f193,f174,f213,f210,f207])).

fof(f201,plain,
    ( ! [X1] :
        ( v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(superposition,[],[f175,f194])).

fof(f205,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f66,f203])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).

fof(f199,plain,(
    spl4_30 ),
    inference(avatar_split_clause,[],[f72,f197])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f195,plain,
    ( spl4_29
    | ~ spl4_11
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f186,f183,f117,f193])).

fof(f183,plain,
    ( spl4_27
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_waybel_9(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f186,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_11
    | ~ spl4_27 ),
    inference(resolution,[],[f184,f118])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ l1_waybel_9(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f183])).

fof(f191,plain,
    ( spl4_28
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f187,f183,f129,f117,f189])).

fof(f129,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f187,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f130,f186])).

fof(f130,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f185,plain,
    ( spl4_27
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f177,f170,f141,f183])).

fof(f170,plain,
    ( spl4_24
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f177,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_waybel_9(X0) )
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(resolution,[],[f171,f142])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f170])).

fof(f181,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f71,f179])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f176,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f70,f174])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,
    ( spl4_24
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f164,f157,f145,f170])).

fof(f145,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f157,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f164,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(resolution,[],[f158,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f168,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f69,f166])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_funct_1(k4_waybel_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f163,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f62,f161])).

fof(f62,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_0)).

fof(f159,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f57,f157])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f155,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f61,f153])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f151,plain,(
    ~ spl4_19 ),
    inference(avatar_split_clause,[],[f43,f149])).

fof(f43,plain,(
    ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                 => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
               => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).

fof(f147,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f60,f145])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f143,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f59,f141])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f139,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f42,f133])).

fof(f42,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f41,f129])).

fof(f41,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f127,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f48,f125])).

fof(f48,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f47,f121])).

fof(f47,plain,(
    v3_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f115,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f55,f113])).

fof(f55,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f52,f101])).

fof(f52,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f77])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21627)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (21626)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (21627)Refutation not found, incomplete strategy% (21627)------------------------------
% 0.22/0.49  % (21627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21627)Memory used [KB]: 10618
% 0.22/0.49  % (21627)Time elapsed: 0.060 s
% 0.22/0.49  % (21627)------------------------------
% 0.22/0.49  % (21627)------------------------------
% 0.22/0.49  % (21634)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (21635)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (21641)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (21629)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21635)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  % (21630)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f163,f168,f172,f176,f181,f185,f191,f195,f199,f205,f215,f219,f224,f228,f235,f239,f242,f258,f262,f269,f274,f280,f299,f313,f317,f329,f339,f344,f348,f363,f385,f404,f413,f430,f449,f457,f459])).
% 0.22/0.50  fof(f459,plain,(
% 0.22/0.50    spl4_32 | ~spl4_33 | ~spl4_22 | ~spl4_57),
% 0.22/0.50    inference(avatar_split_clause,[],[f458,f380,f161,f210,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    spl4_32 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl4_33 <=> l1_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl4_22 <=> ! [X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    spl4_57 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.22/0.50  fof(f458,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_22 | ~spl4_57)),
% 0.22/0.50    inference(resolution,[],[f381,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) ) | ~spl4_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f381,plain,(
% 0.22/0.50    v1_xboole_0(k2_struct_0(sK0)) | ~spl4_57),
% 0.22/0.50    inference(avatar_component_clause,[],[f380])).
% 0.22/0.50  fof(f457,plain,(
% 0.22/0.50    ~spl4_33 | ~spl4_61 | ~spl4_8 | ~spl4_10 | spl4_19 | ~spl4_28 | ~spl4_29 | ~spl4_30 | ~spl4_65),
% 0.22/0.50    inference(avatar_split_clause,[],[f456,f447,f197,f193,f189,f149,f113,f105,f399,f210])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    spl4_61 <=> m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl4_8 <=> v5_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl4_10 <=> v2_lattice3(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl4_19 <=> r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    spl4_28 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl4_29 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl4_30 <=> ! [X1,X0,X2] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.50  fof(f447,plain,(
% 0.22/0.50    spl4_65 <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.22/0.50  fof(f456,plain,(
% 0.22/0.50    ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl4_8 | ~spl4_10 | spl4_19 | ~spl4_28 | ~spl4_29 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(forward_demodulation,[],[f455,f194])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | (~spl4_8 | ~spl4_10 | spl4_19 | ~spl4_28 | ~spl4_29 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(subsumption_resolution,[],[f454,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    m1_subset_1(sK2,k2_struct_0(sK0)) | ~spl4_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f189])).
% 0.22/0.50  fof(f454,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | (~spl4_8 | ~spl4_10 | spl4_19 | ~spl4_29 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(forward_demodulation,[],[f453,f194])).
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | (~spl4_8 | ~spl4_10 | spl4_19 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(subsumption_resolution,[],[f452,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    v5_orders_2(sK0) | ~spl4_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  % (21639)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl4_10 | spl4_19 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(subsumption_resolution,[],[f451,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    v2_lattice3(sK0) | ~spl4_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (spl4_19 | ~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(subsumption_resolution,[],[f450,f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | spl4_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f149])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl4_30 | ~spl4_65)),
% 0.22/0.50    inference(superposition,[],[f448,f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0)) ) | ~spl4_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~spl4_65),
% 0.22/0.50    inference(avatar_component_clause,[],[f447])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    spl4_32 | ~spl4_33 | spl4_65 | spl4_1 | ~spl4_13 | ~spl4_28 | ~spl4_29 | ~spl4_31 | ~spl4_64),
% 0.22/0.50    inference(avatar_split_clause,[],[f441,f428,f203,f193,f189,f125,f77,f447,f210,f207])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl4_1 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl4_13 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    spl4_31 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    spl4_64 <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_13 | ~spl4_28 | ~spl4_29 | ~spl4_31 | ~spl4_64)),
% 0.22/0.50    inference(subsumption_resolution,[],[f440,f190])).
% 0.22/0.50  fof(f440,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | (spl4_1 | ~spl4_13 | ~spl4_29 | ~spl4_31 | ~spl4_64)),
% 0.22/0.50    inference(forward_demodulation,[],[f439,f194])).
% 0.22/0.50  fof(f439,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_13 | ~spl4_31 | ~spl4_64)),
% 0.22/0.50    inference(subsumption_resolution,[],[f438,f126])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    l1_waybel_0(sK1,sK0) | ~spl4_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f438,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_31 | ~spl4_64)),
% 0.22/0.50    inference(subsumption_resolution,[],[f432,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~v2_struct_0(sK1) | spl4_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f432,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_31 | ~spl4_64)),
% 0.22/0.50    inference(superposition,[],[f429,f204])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~l1_orders_2(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl4_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f203])).
% 0.22/0.50  fof(f429,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~spl4_64),
% 0.22/0.50    inference(avatar_component_clause,[],[f428])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ~spl4_61 | ~spl4_48 | spl4_64 | ~spl4_28 | ~spl4_58 | ~spl4_62),
% 0.22/0.50    inference(avatar_split_clause,[],[f416,f402,f383,f189,f428,f302,f399])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    spl4_48 <=> v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    spl4_58 <=> ! [X3,X2] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.22/0.50  fof(f402,plain,(
% 0.22/0.50    spl4_62 <=> r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.22/0.50  fof(f416,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | (~spl4_28 | ~spl4_58 | ~spl4_62)),
% 0.22/0.50    inference(subsumption_resolution,[],[f414,f190])).
% 0.22/0.50  fof(f414,plain,(
% 0.22/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_58 | ~spl4_62)),
% 0.22/0.50    inference(superposition,[],[f403,f384])).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0))) ) | ~spl4_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f383])).
% 0.22/0.50  fof(f403,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~spl4_62),
% 0.22/0.50    inference(avatar_component_clause,[],[f402])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_42 | spl4_61),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f412])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_42 | spl4_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f411,f78])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    v2_struct_0(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_42 | spl4_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f410,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    v4_orders_2(sK1) | ~spl4_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl4_2 <=> v4_orders_2(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    ~v4_orders_2(sK1) | v2_struct_0(sK1) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_42 | spl4_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f409,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    v7_waybel_0(sK1) | ~spl4_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl4_3 <=> v7_waybel_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | (~spl4_12 | ~spl4_13 | ~spl4_42 | spl4_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f408,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    v3_yellow_6(sK1,sK0) | ~spl4_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl4_12 <=> v3_yellow_6(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | (~spl4_13 | ~spl4_42 | spl4_61)),
% 0.22/0.50    inference(subsumption_resolution,[],[f406,f126])).
% 0.22/0.50  fof(f406,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | (~spl4_42 | spl4_61)),
% 0.22/0.50    inference(resolution,[],[f400,f257])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) ) | ~spl4_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    spl4_42 <=> ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | spl4_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f399])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    ~spl4_61 | ~spl4_48 | ~spl4_33 | spl4_32 | spl4_62 | ~spl4_50 | ~spl4_51 | ~spl4_22 | ~spl4_29 | ~spl4_38 | ~spl4_55),
% 0.22/0.50    inference(avatar_split_clause,[],[f374,f361,f237,f193,f161,f311,f308,f402,f207,f210,f302,f399])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    spl4_50 <=> v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    spl4_51 <=> m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    spl4_38 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~m1_subset_1(X3,X0) | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    spl4_55 <=> r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | (~spl4_22 | ~spl4_29 | ~spl4_38 | ~spl4_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f373,f194])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | (~spl4_22 | ~spl4_29 | ~spl4_38 | ~spl4_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f372,f194])).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | (~spl4_22 | ~spl4_38 | ~spl4_55)),
% 0.22/0.50    inference(subsumption_resolution,[],[f370,f162])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_38 | ~spl4_55)),
% 0.22/0.50    inference(superposition,[],[f362,f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) ) | ~spl4_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f237])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~spl4_55),
% 0.22/0.50    inference(avatar_component_clause,[],[f361])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    spl4_57 | spl4_58 | ~spl4_34 | ~spl4_36 | ~spl4_37 | ~spl4_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f354,f346,f233,f226,f213,f383,f380])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    spl4_34 <=> ! [X1] : (v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl4_36 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    spl4_37 <=> ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.50  fof(f346,plain,(
% 0.22/0.50    spl4_54 <=> ! [X1,X0] : (k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_34 | ~spl4_36 | ~spl4_37 | ~spl4_54)),
% 0.22/0.50    inference(subsumption_resolution,[],[f353,f234])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl4_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f233])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | ~m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_34 | ~spl4_36 | ~spl4_54)),
% 0.22/0.50    inference(subsumption_resolution,[],[f352,f214])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X1] : (v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0))) ) | ~spl4_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f213])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | ~v1_funct_2(k4_waybel_1(sK0,X2),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_36 | ~spl4_54)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f349])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_funct_1(k4_waybel_1(sK0,X2),X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,X2)) | ~v1_funct_2(k4_waybel_1(sK0,X2),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X3,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))) ) | (~spl4_36 | ~spl4_54)),
% 0.22/0.50    inference(superposition,[],[f347,f227])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) ) | ~spl4_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f226])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0))) ) | ~spl4_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f346])).
% 0.22/0.50  fof(f363,plain,(
% 0.22/0.50    spl4_55 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_49),
% 0.22/0.50    inference(avatar_split_clause,[],[f359,f305,f125,f121,f85,f81,f77,f361])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    spl4_49 <=> ! [X0] : (v2_struct_0(X0) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) | ~l1_waybel_0(X0,sK0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_49)),
% 0.22/0.50    inference(subsumption_resolution,[],[f358,f82])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v4_orders_2(sK1) | (spl4_1 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_49)),
% 0.22/0.50    inference(subsumption_resolution,[],[f357,f86])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (spl4_1 | ~spl4_12 | ~spl4_13 | ~spl4_49)),
% 0.22/0.50    inference(subsumption_resolution,[],[f356,f122])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (spl4_1 | ~spl4_13 | ~spl4_49)),
% 0.22/0.50    inference(subsumption_resolution,[],[f355,f78])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (~spl4_13 | ~spl4_49)),
% 0.22/0.50    inference(resolution,[],[f306,f126])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_waybel_0(X0,sK0) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) | v2_struct_0(X0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0)) ) | ~spl4_49),
% 0.22/0.50    inference(avatar_component_clause,[],[f305])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    spl4_32 | spl4_54 | ~spl4_11 | ~spl4_29 | ~spl4_52),
% 0.22/0.50    inference(avatar_split_clause,[],[f324,f315,f193,f117,f346,f207])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl4_11 <=> l1_waybel_9(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    spl4_52 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) | ~l1_waybel_9(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl4_11 | ~spl4_29 | ~spl4_52)),
% 0.22/0.50    inference(forward_demodulation,[],[f323,f194])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | v2_struct_0(sK0)) ) | (~spl4_11 | ~spl4_29 | ~spl4_52)),
% 0.22/0.50    inference(forward_demodulation,[],[f322,f194])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | v2_struct_0(sK0)) ) | (~spl4_11 | ~spl4_29 | ~spl4_52)),
% 0.22/0.50    inference(forward_demodulation,[],[f321,f194])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | v2_struct_0(sK0)) ) | (~spl4_11 | ~spl4_52)),
% 0.22/0.50    inference(resolution,[],[f316,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    l1_waybel_9(sK0) | ~spl4_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) | v2_struct_0(X0)) ) | ~spl4_52),
% 0.22/0.50    inference(avatar_component_clause,[],[f315])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    ~spl4_28 | ~spl4_37 | spl4_51),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f343])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    $false | (~spl4_28 | ~spl4_37 | spl4_51)),
% 0.22/0.50    inference(subsumption_resolution,[],[f341,f190])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_37 | spl4_51)),
% 0.22/0.50    inference(resolution,[],[f312,f234])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | spl4_51),
% 0.22/0.50    inference(avatar_component_clause,[],[f311])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    ~spl4_28 | ~spl4_34 | spl4_50),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f338])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    $false | (~spl4_28 | ~spl4_34 | spl4_50)),
% 0.22/0.50    inference(subsumption_resolution,[],[f336,f190])).
% 0.22/0.50  fof(f336,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_34 | spl4_50)),
% 0.22/0.50    inference(resolution,[],[f309,f214])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | spl4_50),
% 0.22/0.50    inference(avatar_component_clause,[],[f308])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    spl4_32 | ~spl4_33 | ~spl4_23 | ~spl4_28 | ~spl4_29 | spl4_48),
% 0.22/0.50    inference(avatar_split_clause,[],[f320,f302,f193,f189,f166,f210,f207])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl4_23 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_1(k4_waybel_1(X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_23 | ~spl4_28 | ~spl4_29 | spl4_48)),
% 0.22/0.50    inference(subsumption_resolution,[],[f319,f190])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_23 | ~spl4_29 | spl4_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f318,f194])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_23 | spl4_48)),
% 0.22/0.50    inference(resolution,[],[f303,f167])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl4_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f166])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ~v1_funct_1(k4_waybel_1(sK0,sK2)) | spl4_48),
% 0.22/0.50    inference(avatar_component_clause,[],[f302])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    spl4_52 | ~spl4_17 | ~spl4_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f275,f267,f141,f315])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl4_17 <=> ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    spl4_44 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) | ~l1_waybel_9(X0)) ) | (~spl4_17 | ~spl4_44)),
% 0.22/0.50    inference(resolution,[],[f268,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) ) | ~spl4_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) ) | ~spl4_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f267])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ~spl4_48 | spl4_49 | ~spl4_50 | ~spl4_51 | ~spl4_15 | ~spl4_47),
% 0.22/0.50    inference(avatar_split_clause,[],[f300,f297,f133,f311,f308,f305,f302])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl4_15 <=> v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    spl4_47 <=> ! [X1,X0] : (r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v5_pre_topc(X1,sK0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))) ) | (~spl4_15 | ~spl4_47)),
% 0.22/0.50    inference(resolution,[],[f298,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) | ~spl4_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v5_pre_topc(X1,sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | ~spl4_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f297])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    spl4_47 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_29 | ~spl4_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f295,f278,f193,f117,f113,f109,f105,f101,f97,f93,f89,f297])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl4_4 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl4_5 <=> v8_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl4_6 <=> v3_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl4_7 <=> v4_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl4_9 <=> v1_lattice3(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    spl4_45 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v5_pre_topc(X1,sK0,sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_29 | ~spl4_45)),
% 0.22/0.50    inference(forward_demodulation,[],[f294,f194])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_29 | ~spl4_45)),
% 0.22/0.50    inference(forward_demodulation,[],[f293,f194])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_29 | ~spl4_45)),
% 0.22/0.50    inference(forward_demodulation,[],[f292,f194])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f291,f118])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f290,f114])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f289,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    v1_lattice3(sK0) | ~spl4_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f288,f106])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f287,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v4_orders_2(sK0) | ~spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f286,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl4_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_5 | ~spl4_6 | ~spl4_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f285,f94])).
% 0.22/0.50  % (21633)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    v8_pre_topc(sK0) | ~spl4_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X1,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X1,k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X1,X0)))) ) | (~spl4_6 | ~spl4_45)),
% 0.22/0.50    inference(resolution,[],[f279,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    v3_orders_2(sK0) | ~spl4_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))) ) | ~spl4_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f278])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    spl4_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f278])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    ~spl4_11 | ~spl4_16 | spl4_41),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    $false | (~spl4_11 | ~spl4_16 | spl4_41)),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f118])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ~l1_waybel_9(sK0) | (~spl4_16 | spl4_41)),
% 0.22/0.50    inference(resolution,[],[f254,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) ) | ~spl4_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl4_16 <=> ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl4_41),
% 0.22/0.50    inference(avatar_component_clause,[],[f253])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    spl4_41 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    spl4_44 | ~spl4_23 | ~spl4_25 | ~spl4_26 | ~spl4_43),
% 0.22/0.50    inference(avatar_split_clause,[],[f265,f260,f179,f174,f166,f267])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    spl4_25 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    spl4_26 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    spl4_43 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) ) | (~spl4_23 | ~spl4_25 | ~spl4_26 | ~spl4_43)),
% 0.22/0.50    inference(subsumption_resolution,[],[f264,f180])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl4_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f179])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) ) | (~spl4_23 | ~spl4_25 | ~spl4_43)),
% 0.22/0.50    inference(subsumption_resolution,[],[f263,f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl4_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f174])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) ) | (~spl4_23 | ~spl4_43)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f167])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) ) | ~spl4_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f260])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    spl4_43),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f260])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) )),
% 0.22/0.50    inference(equality_resolution,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | k4_waybel_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    spl4_32 | ~spl4_41 | spl4_42 | ~spl4_4 | ~spl4_5 | ~spl4_29 | ~spl4_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f231,f217,f193,f93,f89,f256,f253,f207])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl4_35 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_29 | ~spl4_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f230,f94])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_29 | ~spl4_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f229,f90])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_29 | ~spl4_35)),
% 0.22/0.50    inference(superposition,[],[f218,f194])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) ) | ~spl4_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~spl4_33 | ~spl4_9 | ~spl4_20 | ~spl4_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f241,f207,f153,f109,f210])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl4_20 <=> ! [X0] : (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v2_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | (~spl4_9 | ~spl4_20 | ~spl4_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f240,f110])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | (~spl4_20 | ~spl4_32)),
% 0.22/0.50    inference(resolution,[],[f208,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) ) | ~spl4_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~spl4_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f207])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    spl4_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f73,f237])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~m1_subset_1(X3,X0) | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    spl4_32 | ~spl4_33 | spl4_37 | ~spl4_26 | ~spl4_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f200,f193,f179,f233,f210,f207])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl4_26 | ~spl4_29)),
% 0.22/0.50    inference(superposition,[],[f180,f194])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl4_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f74,f226])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ~spl4_11 | ~spl4_17 | spl4_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    $false | (~spl4_11 | ~spl4_17 | spl4_33)),
% 0.22/0.50    inference(subsumption_resolution,[],[f221,f118])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ~l1_waybel_9(sK0) | (~spl4_17 | spl4_33)),
% 0.22/0.50    inference(resolution,[],[f211,f142])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | spl4_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f210])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl4_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f68,f217])).
% 0.22/0.50  % (21631)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    spl4_32 | ~spl4_33 | spl4_34 | ~spl4_25 | ~spl4_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f201,f193,f174,f213,f210,f207])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X1] : (v1_funct_2(k4_waybel_1(sK0,X1),k2_struct_0(sK0),k2_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl4_25 | ~spl4_29)),
% 0.22/0.51    inference(superposition,[],[f175,f194])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl4_31),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f203])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl4_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f197])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    spl4_29 | ~spl4_11 | ~spl4_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f186,f183,f117,f193])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl4_27 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_waybel_9(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl4_11 | ~spl4_27)),
% 0.22/0.51    inference(resolution,[],[f184,f118])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_9(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f183])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl4_28 | ~spl4_11 | ~spl4_14 | ~spl4_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f187,f183,f129,f117,f189])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl4_14 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_11 | ~spl4_14 | ~spl4_27)),
% 0.22/0.51    inference(backward_demodulation,[],[f130,f186])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl4_27 | ~spl4_17 | ~spl4_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f177,f170,f141,f183])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl4_24 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_waybel_9(X0)) ) | (~spl4_17 | ~spl4_24)),
% 0.22/0.51    inference(resolution,[],[f171,f142])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f170])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl4_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f179])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    spl4_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f174])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl4_24 | ~spl4_18 | ~spl4_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f164,f157,f145,f170])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl4_18 <=> ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    spl4_21 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_orders_2(X0)) ) | (~spl4_18 | ~spl4_21)),
% 0.22/0.51    inference(resolution,[],[f158,f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) ) | ~spl4_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f157])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    spl4_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f166])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_1(k4_waybel_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl4_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f161])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_0)).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    spl4_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f157])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl4_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f153])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ~spl4_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f149])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl4_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f60,f145])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl4_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f141])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl4_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f58,f137])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl4_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f133])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl4_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f129])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f125])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    l1_waybel_0(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl4_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f121])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v3_yellow_6(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl4_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f117])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    l1_waybel_9(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f113])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v2_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f109])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    v1_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f105])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    v5_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f101])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v4_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f97])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v3_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f93])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v8_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f89])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f85])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    v7_waybel_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f81])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v4_orders_2(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f77])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21635)------------------------------
% 0.22/0.51  % (21635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21635)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21635)Memory used [KB]: 10874
% 0.22/0.51  % (21635)Time elapsed: 0.082 s
% 0.22/0.51  % (21635)------------------------------
% 0.22/0.51  % (21635)------------------------------
% 0.22/0.51  % (21628)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (21625)Success in time 0.141 s
%------------------------------------------------------------------------------
