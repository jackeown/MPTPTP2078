%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  273 ( 933 expanded)
%              Number of leaves         :   68 ( 463 expanded)
%              Depth                    :   12
%              Number of atoms          : 1998 (7565 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f625,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f119,f133,f138,f148,f153,f158,f163,f172,f176,f182,f194,f195,f207,f211,f215,f219,f227,f241,f245,f249,f253,f257,f267,f271,f276,f304,f309,f327,f331,f404,f409,f414,f419,f425,f431,f444,f496,f501,f506,f511,f523,f550,f568,f576,f584,f598,f611,f624])).

fof(f624,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_29
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | ~ spl6_70
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75
    | ~ spl6_77
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_29
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | ~ spl6_70
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75
    | ~ spl6_77
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f606,f613])).

fof(f613,plain,
    ( r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | spl6_1
    | ~ spl6_20
    | ~ spl6_29
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_51
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f89,f193,f403,f408,f413,f418,f424,f610,f240])).

fof(f240,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_waybel_0(X0,X2,X1)
        | ~ m2_yellow_6(X3,X0,X2)
        | r1_waybel_0(X0,X3,X1)
        | ~ l1_waybel_0(X2,X0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl6_29
  <=> ! [X1,X3,X0,X2] :
        ( r1_waybel_0(X0,X3,X1)
        | ~ m2_yellow_6(X3,X0,X2)
        | ~ r1_waybel_0(X0,X2,X1)
        | ~ l1_waybel_0(X2,X0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f610,plain,
    ( m2_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0,sK4(sK0,sK1,sK2))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl6_78
  <=> m2_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f424,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl6_51
  <=> r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f418,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl6_50
  <=> l1_waybel_0(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f413,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK2))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl6_49
  <=> v7_waybel_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f408,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK2))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl6_48
  <=> v4_orders_2(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f403,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK2))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl6_47
  <=> v2_struct_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f193,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_20
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f606,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | ~ spl6_70
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75
    | ~ spl6_77 ),
    inference(subsumption_resolution,[],[f587,f601])).

fof(f601,plain,
    ( v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_70
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75
    | ~ spl6_77 ),
    inference(unit_resulting_resolution,[],[f94,f89,f99,f104,f408,f413,f403,f418,f430,f567,f575,f583,f597,f549])).

fof(f549,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(sK5(X0,X1,X2),X0)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ v7_waybel_0(sK5(X0,X1,X2))
        | ~ v4_orders_2(sK5(X0,X1,X2))
        | v2_struct_0(sK5(X0,X1,X2)) )
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl6_70
  <=> ! [X1,X0,X2] :
        ( ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(sK5(X0,X1,X2),X0)
        | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ v7_waybel_0(sK5(X0,X1,X2))
        | ~ v4_orders_2(sK5(X0,X1,X2))
        | v2_struct_0(sK5(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f597,plain,
    ( l1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl6_77
  <=> l1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f583,plain,
    ( v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f581])).

fof(f581,plain,
    ( spl6_75
  <=> v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f575,plain,
    ( v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl6_74
  <=> v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f567,plain,
    ( ~ v2_struct_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_73 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl6_73
  <=> v2_struct_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f430,plain,
    ( r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f428])).

% (21169)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (21165)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (21173)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (21176)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (21160)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f428,plain,
    ( spl6_52
  <=> r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f104,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f94,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f587,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | ~ v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f579,f583])).

fof(f579,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | ~ v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | spl6_73
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f571,f575])).

fof(f571,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | ~ v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67
    | spl6_73 ),
    inference(subsumption_resolution,[],[f534,f567])).

fof(f534,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | ~ v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | v2_struct_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f526,f531])).

fof(f531,plain,
    ( l1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_67 ),
    inference(unit_resulting_resolution,[],[f193,f99,f89,f94,f413,f403,f408,f418,f430,f104,f522])).

fof(f522,plain,
    ( ! [X2,X0,X1] :
        ( l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ l1_struct_0(X0) )
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl6_67
  <=> ! [X1,X0,X2] :
        ( ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f526,plain,
    ( ~ r1_waybel_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK1)
    | ~ l1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ v3_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | v2_struct_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | ~ spl6_18
    | ~ spl6_63 ),
    inference(resolution,[],[f500,f181])).

fof(f181,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
        | ~ r1_waybel_0(sK0,X3,sK1)
        | ~ l1_waybel_0(X3,sK0)
        | ~ v3_yellow_6(X3,sK0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_18
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
        | ~ r1_waybel_0(sK0,X3,sK1)
        | ~ l1_waybel_0(X3,sK0)
        | ~ v3_yellow_6(X3,sK0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f500,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2)))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl6_63
  <=> r2_hidden(sK2,k10_yellow_6(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f611,plain,
    ( spl6_78
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_38
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f434,f428,f416,f411,f406,f401,f302,f102,f97,f92,f87,f608])).

fof(f302,plain,
    ( spl6_38
  <=> ! [X1,X0,X2] :
        ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f434,plain,
    ( m2_yellow_6(sK5(sK0,sK4(sK0,sK1,sK2),sK2),sK0,sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_38
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f403,f408,f413,f418,f430,f303])).

% (21170)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f303,plain,
    ( ! [X2,X0,X1] :
        ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f302])).

fof(f598,plain,
    ( spl6_77
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f531,f521,f428,f416,f411,f406,f401,f191,f102,f97,f92,f87,f595])).

fof(f584,plain,
    ( spl6_75
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f512,f509,f428,f416,f411,f406,f401,f191,f102,f97,f92,f87,f581])).

fof(f509,plain,
    ( spl6_65
  <=> ! [X3,X5,X4] :
        ( ~ r3_waybel_9(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ l1_waybel_0(X4,X3)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | v7_waybel_0(sK5(X3,X4,X5))
        | ~ l1_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f512,plain,
    ( v7_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_65 ),
    inference(unit_resulting_resolution,[],[f193,f99,f89,f94,f413,f403,f408,f418,f430,f104,f510])).

fof(f510,plain,
    ( ! [X4,X5,X3] :
        ( v7_waybel_0(sK5(X3,X4,X5))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ l1_waybel_0(X4,X3)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ r3_waybel_9(X3,X4,X5)
        | ~ l1_struct_0(X3) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f509])).

fof(f576,plain,
    ( spl6_74
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f507,f504,f428,f416,f411,f406,f401,f191,f102,f97,f92,f87,f573])).

fof(f504,plain,
    ( spl6_64
  <=> ! [X7,X8,X6] :
        ( ~ r3_waybel_9(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_waybel_0(X7,X6)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | v4_orders_2(sK5(X6,X7,X8))
        | ~ l1_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f507,plain,
    ( v4_orders_2(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f193,f99,f89,f94,f413,f403,f408,f418,f430,f104,f505])).

fof(f505,plain,
    ( ! [X6,X8,X7] :
        ( v4_orders_2(sK5(X6,X7,X8))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_waybel_0(X7,X6)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ r3_waybel_9(X6,X7,X8)
        | ~ l1_struct_0(X6) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f504])).

fof(f568,plain,
    ( ~ spl6_73
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f502,f494,f428,f416,f411,f406,f401,f191,f102,f97,f92,f87,f565])).

fof(f494,plain,
    ( spl6_62
  <=> ! [X9,X11,X10] :
        ( ~ r3_waybel_9(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_waybel_0(X10,X9)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9)
        | ~ v2_struct_0(sK5(X9,X10,X11))
        | ~ l1_struct_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f502,plain,
    ( ~ v2_struct_0(sK5(sK0,sK4(sK0,sK1,sK2),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f193,f99,f89,f94,f413,f403,f408,f418,f430,f104,f495])).

fof(f495,plain,
    ( ! [X10,X11,X9] :
        ( ~ v2_struct_0(sK5(X9,X10,X11))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_waybel_0(X10,X9)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9)
        | ~ r3_waybel_9(X9,X10,X11)
        | ~ l1_struct_0(X9) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f494])).

fof(f550,plain,
    ( spl6_70
    | ~ spl6_27
    | ~ spl6_39
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f445,f442,f307,f225,f548])).

fof(f225,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( v3_yellow_6(X1,X0)
        | k10_yellow_6(X0,X1) = k1_xboole_0
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f307,plain,
    ( spl6_39
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f442,plain,
    ( spl6_54
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f445,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(sK5(X0,X1,X2),X0)
        | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ v7_waybel_0(sK5(X0,X1,X2))
        | ~ v4_orders_2(sK5(X0,X1,X2))
        | v2_struct_0(sK5(X0,X1,X2)) )
    | ~ spl6_27
    | ~ spl6_39
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f322,f443])).

fof(f443,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f442])).

fof(f322,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(sK5(X0,X1,X2),X0)
        | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ v7_waybel_0(sK5(X0,X1,X2))
        | ~ v4_orders_2(sK5(X0,X1,X2))
        | v2_struct_0(sK5(X0,X1,X2)) )
    | ~ spl6_27
    | ~ spl6_39 ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(sK5(X0,X1,X2),X0)
        | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ v7_waybel_0(sK5(X0,X1,X2))
        | ~ v4_orders_2(sK5(X0,X1,X2))
        | v2_struct_0(sK5(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_27
    | ~ spl6_39 ),
    inference(superposition,[],[f308,f226])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( k10_yellow_6(X0,X1) = k1_xboole_0
        | v3_yellow_6(X1,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f225])).

fof(f308,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        | ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f307])).

fof(f523,plain,
    ( spl6_67
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f317,f302,f217,f521])).

fof(f217,plain,
    ( spl6_25
  <=> ! [X1,X0,X2] :
        ( l1_waybel_0(X2,X0)
        | ~ m2_yellow_6(X2,X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ l1_struct_0(X0) )
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | l1_waybel_0(sK5(X0,X1,X2),X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(resolution,[],[f303,f218])).

fof(f218,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_yellow_6(X2,X0,X1)
        | l1_waybel_0(X2,X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f511,plain,
    ( spl6_65
    | ~ spl6_24
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f316,f302,f213,f509])).

fof(f213,plain,
    ( spl6_24
  <=> ! [X1,X0,X2] :
        ( v7_waybel_0(X2)
        | ~ m2_yellow_6(X2,X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f316,plain,
    ( ! [X4,X5,X3] :
        ( ~ r3_waybel_9(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ l1_waybel_0(X4,X3)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | v7_waybel_0(sK5(X3,X4,X5))
        | ~ l1_struct_0(X3) )
    | ~ spl6_24
    | ~ spl6_38 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X4,X5,X3] :
        ( ~ r3_waybel_9(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ l1_waybel_0(X4,X3)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | v7_waybel_0(sK5(X3,X4,X5))
        | ~ l1_waybel_0(X4,X3)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_struct_0(X3)
        | v2_struct_0(X3) )
    | ~ spl6_24
    | ~ spl6_38 ),
    inference(resolution,[],[f303,f214])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_yellow_6(X2,X0,X1)
        | v7_waybel_0(X2)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f506,plain,
    ( spl6_64
    | ~ spl6_23
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f315,f302,f209,f504])).

fof(f209,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( v4_orders_2(X2)
        | ~ m2_yellow_6(X2,X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f315,plain,
    ( ! [X6,X8,X7] :
        ( ~ r3_waybel_9(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_waybel_0(X7,X6)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | v4_orders_2(sK5(X6,X7,X8))
        | ~ l1_struct_0(X6) )
    | ~ spl6_23
    | ~ spl6_38 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ! [X6,X8,X7] :
        ( ~ r3_waybel_9(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_waybel_0(X7,X6)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | v4_orders_2(sK5(X6,X7,X8))
        | ~ l1_waybel_0(X7,X6)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X6)
        | v2_struct_0(X6) )
    | ~ spl6_23
    | ~ spl6_38 ),
    inference(resolution,[],[f303,f210])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_yellow_6(X2,X0,X1)
        | v4_orders_2(X2)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f501,plain,
    ( spl6_63
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_39
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f433,f428,f416,f411,f406,f401,f307,f102,f97,f92,f87,f498])).

fof(f433,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK2)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_39
    | spl6_47
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f403,f408,f413,f418,f430,f308])).

fof(f496,plain,
    ( spl6_62
    | ~ spl6_22
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f314,f302,f205,f494])).

fof(f205,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( ~ v2_struct_0(X2)
        | ~ m2_yellow_6(X2,X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f314,plain,
    ( ! [X10,X11,X9] :
        ( ~ r3_waybel_9(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_waybel_0(X10,X9)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9)
        | ~ v2_struct_0(sK5(X9,X10,X11))
        | ~ l1_struct_0(X9) )
    | ~ spl6_22
    | ~ spl6_38 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ! [X10,X11,X9] :
        ( ~ r3_waybel_9(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_waybel_0(X10,X9)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | v2_struct_0(X9)
        | ~ v2_struct_0(sK5(X9,X10,X11))
        | ~ l1_waybel_0(X10,X9)
        | ~ v7_waybel_0(X10)
        | ~ v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X9)
        | v2_struct_0(X9) )
    | ~ spl6_22
    | ~ spl6_38 ),
    inference(resolution,[],[f303,f206])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_yellow_6(X2,X0,X1)
        | ~ v2_struct_0(X2)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f444,plain,
    ( spl6_54
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f187,f174,f150,f442])).

fof(f150,plain,
    ( spl6_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f174,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f187,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f152,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f152,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f431,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f280,f269,f112,f107,f102,f97,f92,f87,f428])).

fof(f107,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f112,plain,
    ( spl6_6
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f269,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f280,plain,
    ( r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f270])).

fof(f270,plain,
    ( ! [X2,X0,X1] :
        ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f269])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f425,plain,
    ( spl6_51
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f277,f265,f112,f107,f102,f97,f92,f87,f422])).

fof(f265,plain,
    ( spl6_34
  <=> ! [X1,X0,X2] :
        ( r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f277,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f266])).

fof(f266,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f265])).

fof(f419,plain,
    ( spl6_50
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f272,f255,f112,f107,f102,f97,f92,f87,f416])).

fof(f255,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( l1_waybel_0(sK4(X0,X1,X2),X0)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f272,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f256])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( l1_waybel_0(sK4(X0,X1,X2),X0)
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f255])).

fof(f414,plain,
    ( spl6_49
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f262,f251,f112,f107,f102,f97,f92,f87,f411])).

fof(f251,plain,
    ( spl6_32
  <=> ! [X1,X0,X2] :
        ( v7_waybel_0(sK4(X0,X1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f262,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f252])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v7_waybel_0(sK4(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f251])).

fof(f409,plain,
    ( spl6_48
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f260,f247,f112,f107,f102,f97,f92,f87,f406])).

fof(f247,plain,
    ( spl6_31
  <=> ! [X1,X0,X2] :
        ( v4_orders_2(sK4(X0,X1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f260,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f248])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v4_orders_2(sK4(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f247])).

fof(f404,plain,
    ( ~ spl6_47
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f258,f243,f112,f107,f102,f97,f92,f87,f401])).

fof(f243,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( ~ v2_struct_0(sK4(X0,X1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f258,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f104,f114,f109,f244])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v2_struct_0(sK4(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f331,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f297,f328])).

fof(f328,plain,
    ( ~ r3_waybel_9(sK0,sK3,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f137,f129,f118,f147,f157,f104,f113,f109,f326])).

fof(f326,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r3_waybel_9(X0,X3,X2)
        | ~ r1_waybel_0(X0,X3,X1)
        | ~ l1_waybel_0(X3,X0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl6_40
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X2,k2_pre_topc(X0,X1))
        | ~ r3_waybel_9(X0,X3,X2)
        | ~ r1_waybel_0(X0,X3,X1)
        | ~ l1_waybel_0(X3,X0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f113,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f157,plain,
    ( r1_waybel_0(sK0,sK3,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_13
  <=> r1_waybel_0(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f147,plain,
    ( l1_waybel_0(sK3,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_11
  <=> l1_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f118,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f129,plain,
    ( v4_orders_2(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_8
  <=> v4_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f137,plain,
    ( v7_waybel_0(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_9
  <=> v7_waybel_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f297,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f89,f94,f99,f118,f129,f137,f147,f104,f162,f275])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
        | r3_waybel_9(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl6_36
  <=> ! [X1,X0,X2] :
        ( r3_waybel_9(X0,X1,X2)
        | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f162,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_14
  <=> r2_hidden(sK2,k10_yellow_6(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f327,plain,(
    spl6_40 ),
    inference(avatar_split_clause,[],[f72,f325])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
                    & l1_waybel_0(sK4(X0,X1,X2),X0)
                    & v7_waybel_0(sK4(X0,X1,X2))
                    & v4_orders_2(sK4(X0,X1,X2))
                    & ~ v2_struct_0(sK4(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        & l1_waybel_0(sK4(X0,X1,X2),X0)
        & v7_waybel_0(sK4(X0,X1,X2))
        & v4_orders_2(sK4(X0,X1,X2))
        & ~ v2_struct_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

fof(f309,plain,(
    spl6_39 ),
    inference(avatar_split_clause,[],[f77,f307])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
                & m2_yellow_6(sK5(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f304,plain,(
    spl6_38 ),
    inference(avatar_split_clause,[],[f76,f302])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f276,plain,(
    spl6_36 ),
    inference(avatar_split_clause,[],[f75,f274])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f271,plain,(
    spl6_35 ),
    inference(avatar_split_clause,[],[f71,f269])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f267,plain,(
    spl6_34 ),
    inference(avatar_split_clause,[],[f70,f265])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f257,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f69,f255])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f253,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f68,f251])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f249,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f67,f247])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f245,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f66,f243])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f241,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f65,f239])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X3,X1)
      | ~ m2_yellow_6(X3,X0,X2)
      | ~ r1_waybel_0(X0,X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_waybel_0(X0,X3,X1)
              | ~ m2_yellow_6(X3,X0,X2) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_waybel_0(X0,X3,X1)
              | ~ m2_yellow_6(X3,X0,X2) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
         => ( r1_waybel_0(X0,X2,X1)
           => ! [X3] :
                ( m2_yellow_6(X3,X0,X2)
               => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow19)).

fof(f227,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f74,f225])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k10_yellow_6(X0,X1) = k1_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k10_yellow_6(X0,X1) = k1_xboole_0 )
            & ( k10_yellow_6(X0,X1) != k1_xboole_0
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f219,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f83,f217])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f215,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f82,f213])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f211,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f81,f209])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f207,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f80,f205])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f195,plain,
    ( ~ spl6_6
    | spl6_18 ),
    inference(avatar_split_clause,[],[f61,f180,f112])).

fof(f61,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
      | ~ r1_waybel_0(sK0,X3,sK1)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v3_yellow_6(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
          | ~ r1_waybel_0(sK0,X3,sK1)
          | ~ l1_waybel_0(X3,sK0)
          | ~ v3_yellow_6(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
        & r1_waybel_0(sK0,sK3,sK1)
        & l1_waybel_0(sK3,sK0)
        & v3_yellow_6(sK3,sK0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v3_yellow_6(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(sK0,X3))
                    | ~ r1_waybel_0(sK0,X3,X1)
                    | ~ l1_waybel_0(X3,sK0)
                    | ~ v3_yellow_6(X3,sK0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                    & r1_waybel_0(sK0,X4,X1)
                    & l1_waybel_0(X4,sK0)
                    & v3_yellow_6(X4,sK0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,k10_yellow_6(sK0,X3))
                  | ~ r1_waybel_0(sK0,X3,X1)
                  | ~ l1_waybel_0(X3,sK0)
                  | ~ v3_yellow_6(X3,sK0)
                  | ~ v7_waybel_0(X3)
                  | ~ v4_orders_2(X3)
                  | v2_struct_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ? [X4] :
                  ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                  & r1_waybel_0(sK0,X4,X1)
                  & l1_waybel_0(X4,sK0)
                  & v3_yellow_6(X4,sK0)
                  & v7_waybel_0(X4)
                  & v4_orders_2(X4)
                  & ~ v2_struct_0(X4) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X2,k10_yellow_6(sK0,X3))
                | ~ r1_waybel_0(sK0,X3,sK1)
                | ~ l1_waybel_0(X3,sK0)
                | ~ v3_yellow_6(X3,sK0)
                | ~ v7_waybel_0(X3)
                | ~ v4_orders_2(X3)
                | v2_struct_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ? [X4] :
                ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                & r1_waybel_0(sK0,X4,sK1)
                & l1_waybel_0(X4,sK0)
                & v3_yellow_6(X4,sK0)
                & v7_waybel_0(X4)
                & v4_orders_2(X4)
                & ~ v2_struct_0(X4) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X2,k10_yellow_6(sK0,X3))
              | ~ r1_waybel_0(sK0,X3,sK1)
              | ~ l1_waybel_0(X3,sK0)
              | ~ v3_yellow_6(X3,sK0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ? [X4] :
              ( r2_hidden(X2,k10_yellow_6(sK0,X4))
              & r1_waybel_0(sK0,X4,sK1)
              & l1_waybel_0(X4,sK0)
              & v3_yellow_6(X4,sK0)
              & v7_waybel_0(X4)
              & v4_orders_2(X4)
              & ~ v2_struct_0(X4) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
            | ~ r1_waybel_0(sK0,X3,sK1)
            | ~ l1_waybel_0(X3,sK0)
            | ~ v3_yellow_6(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ? [X4] :
            ( r2_hidden(sK2,k10_yellow_6(sK0,X4))
            & r1_waybel_0(sK0,X4,sK1)
            & l1_waybel_0(X4,sK0)
            & v3_yellow_6(X4,sK0)
            & v7_waybel_0(X4)
            & v4_orders_2(X4)
            & ~ v2_struct_0(X4) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X4] :
        ( r2_hidden(sK2,k10_yellow_6(sK0,X4))
        & r1_waybel_0(sK0,X4,sK1)
        & l1_waybel_0(X4,sK0)
        & v3_yellow_6(X4,sK0)
        & v7_waybel_0(X4)
        & v4_orders_2(X4)
        & ~ v2_struct_0(X4) )
   => ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
      & r1_waybel_0(sK0,sK3,sK1)
      & l1_waybel_0(sK3,sK0)
      & v3_yellow_6(sK3,sK0)
      & v7_waybel_0(sK3)
      & v4_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X4))
                    & r1_waybel_0(X0,X4,X1)
                    & l1_waybel_0(X4,X0)
                    & v3_yellow_6(X4,X0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X3))
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v3_yellow_6(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

fof(f194,plain,
    ( spl6_20
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f177,f170,f97,f191])).

fof(f170,plain,
    ( spl6_16
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f177,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f99,f171])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f182,plain,
    ( spl6_18
    | spl6_8 ),
    inference(avatar_split_clause,[],[f132,f127,f180])).

fof(f132,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
        | ~ r1_waybel_0(sK0,X3,sK1)
        | ~ l1_waybel_0(X3,sK0)
        | ~ v3_yellow_6(X3,sK0)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | spl6_8 ),
    inference(subsumption_resolution,[],[f61,f131])).

fof(f131,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl6_8 ),
    inference(subsumption_resolution,[],[f55,f128])).

fof(f128,plain,
    ( ~ v4_orders_2(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f55,plain,
    ( v4_orders_2(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f176,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f84,f174])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f172,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f64,f170])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f163,plain,
    ( spl6_6
    | spl6_14 ),
    inference(avatar_split_clause,[],[f60,f160,f112])).

fof(f60,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f158,plain,
    ( spl6_6
    | spl6_13 ),
    inference(avatar_split_clause,[],[f59,f155,f112])).

fof(f59,plain,
    ( r1_waybel_0(sK0,sK3,sK1)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f153,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f85,f150])).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f63,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f148,plain,
    ( spl6_6
    | spl6_11 ),
    inference(avatar_split_clause,[],[f58,f145,f112])).

fof(f58,plain,
    ( l1_waybel_0(sK3,sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f138,plain,
    ( spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f56,f135,f112])).

fof(f56,plain,
    ( v7_waybel_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( spl6_6
    | spl6_8 ),
    inference(avatar_split_clause,[],[f131,f127,f112])).

fof(f119,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f54,f116,f112])).

fof(f54,plain,
    ( ~ v2_struct_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f107])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f50,f92])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f87])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
