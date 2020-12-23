%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t36_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 47.24s
% Output     : Refutation 47.24s
% Verified   : 
% Statistics : Number of formulae       :  309 (1114 expanded)
%              Number of leaves         :   86 ( 592 expanded)
%              Depth                    :   11
%              Number of atoms          : 2282 (9802 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f187,f194,f201,f208,f215,f222,f229,f236,f243,f256,f264,f271,f285,f313,f320,f351,f367,f392,f421,f441,f526,f530,f534,f553,f557,f563,f567,f571,f577,f581,f599,f603,f607,f611,f615,f619,f623,f627,f676,f1115,f1137,f1164,f1650,f1666,f1673,f1680,f1709,f1766,f2111,f3394,f3476,f3491,f3498,f3505,f3580,f3631,f3821,f4431,f6356,f6361,f6549])).

fof(f6549,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | spl10_23
    | ~ spl10_24
    | ~ spl10_26
    | spl10_31
    | ~ spl10_38
    | ~ spl10_40
    | spl10_77
    | ~ spl10_142 ),
    inference(avatar_contradiction_clause,[],[f6548])).

fof(f6548,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_31
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_77
    | ~ spl10_142 ),
    inference(subsumption_resolution,[],[f319,f6520])).

fof(f6520,plain,
    ( ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK3))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_23
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_31
    | ~ spl10_38
    | ~ spl10_77
    | ~ spl10_142 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f228,f255,f284,f235,f246,f242,f263,f270,f312,f622])).

fof(f622,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
        | r2_hidden(X1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X3,X0)
        | ~ v1_waybel_0(X3,X0)
        | v1_xboole_0(X3)
        | ~ r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_142 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl10_142
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X1,X3)
        | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X3,X0)
        | ~ v1_waybel_0(X3,X0)
        | v1_xboole_0(X3)
        | ~ r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f312,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl10_38
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f270,plain,
    ( v12_waybel_0(sK3,sK0)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl10_26
  <=> v12_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f263,plain,
    ( v1_waybel_0(sK3,sK0)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl10_24
  <=> v1_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f242,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl10_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f246,plain,
    ( r1_waybel_3(sK0,sK1,sK2)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl10_20
  <=> r1_waybel_3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f235,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl10_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f284,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl10_31
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f255,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl10_23
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f228,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl10_14
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f186,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f179,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl10_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f420,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl10_77
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f319,plain,
    ( r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK3))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl10_40
  <=> r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f6361,plain,
    ( ~ spl10_0
    | ~ spl10_14
    | ~ spl10_18
    | spl10_77
    | ~ spl10_106
    | ~ spl10_150
    | ~ spl10_612
    | ~ spl10_652
    | spl10_917 ),
    inference(avatar_contradiction_clause,[],[f6360])).

fof(f6360,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_14
    | ~ spl10_18
    | ~ spl10_77
    | ~ spl10_106
    | ~ spl10_150
    | ~ spl10_612
    | ~ spl10_652
    | ~ spl10_917 ),
    inference(subsumption_resolution,[],[f6357,f4435])).

fof(f4435,plain,
    ( r1_orders_2(sK0,sK2,k1_yellow_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK1)))
    | ~ spl10_150
    | ~ spl10_612
    | ~ spl10_652 ),
    inference(unit_resulting_resolution,[],[f675,f3630,f4430])).

fof(f4430,plain,
    ( ! [X13] :
        ( ~ r1_tarski(sK4(sK0,sK1,sK2),X13)
        | r1_orders_2(sK0,sK2,k1_yellow_0(sK0,X13))
        | ~ m1_subset_1(k1_yellow_0(sK0,X13),u1_struct_0(sK0)) )
    | ~ spl10_652 ),
    inference(avatar_component_clause,[],[f4429])).

fof(f4429,plain,
    ( spl10_652
  <=> ! [X13] :
        ( ~ r1_tarski(sK4(sK0,sK1,sK2),X13)
        | r1_orders_2(sK0,sK2,k1_yellow_0(sK0,X13))
        | ~ m1_subset_1(k1_yellow_0(sK0,X13),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_652])])).

fof(f3630,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_612 ),
    inference(avatar_component_clause,[],[f3629])).

fof(f3629,plain,
    ( spl10_612
  <=> r1_tarski(sK4(sK0,sK1,sK2),sK5(sK0,sK4(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_612])])).

fof(f675,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl10_150 ),
    inference(avatar_component_clause,[],[f674])).

fof(f674,plain,
    ( spl10_150
  <=> ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f6357,plain,
    ( ~ r1_orders_2(sK0,sK2,k1_yellow_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK1)))
    | ~ spl10_0
    | ~ spl10_14
    | ~ spl10_18
    | ~ spl10_77
    | ~ spl10_106
    | ~ spl10_150
    | ~ spl10_917 ),
    inference(unit_resulting_resolution,[],[f420,f179,f228,f242,f675,f6355,f529])).

fof(f529,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(X0,X1,X2)
        | r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_106 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl10_106
  <=> ! [X1,X0,X2] :
        ( r3_orders_2(X0,X1,X2)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f6355,plain,
    ( ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK1)))
    | ~ spl10_917 ),
    inference(avatar_component_clause,[],[f6354])).

fof(f6354,plain,
    ( spl10_917
  <=> ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_917])])).

fof(f6356,plain,
    ( ~ spl10_917
    | ~ spl10_58
    | spl10_575
    | ~ spl10_586
    | ~ spl10_590
    | ~ spl10_592
    | spl10_595
    | ~ spl10_606 ),
    inference(avatar_split_clause,[],[f3581,f3578,f3503,f3496,f3489,f3474,f3392,f365,f6354])).

fof(f365,plain,
    ( spl10_58
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X4,sK0)
        | ~ v12_waybel_0(X4,sK0)
        | ~ v1_waybel_0(X4,sK0)
        | v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f3392,plain,
    ( spl10_575
  <=> ~ v1_xboole_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_575])])).

fof(f3474,plain,
    ( spl10_586
  <=> v1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_586])])).

fof(f3489,plain,
    ( spl10_590
  <=> v12_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_590])])).

fof(f3496,plain,
    ( spl10_592
  <=> v1_waybel_7(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_592])])).

fof(f3503,plain,
    ( spl10_595
  <=> ~ r2_hidden(sK1,sK5(sK0,sK4(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_595])])).

fof(f3578,plain,
    ( spl10_606
  <=> m1_subset_1(sK5(sK0,sK4(sK0,sK1,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_606])])).

fof(f3581,plain,
    ( ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK5(sK0,sK4(sK0,sK1,sK2),sK1)))
    | ~ spl10_58
    | ~ spl10_575
    | ~ spl10_586
    | ~ spl10_590
    | ~ spl10_592
    | ~ spl10_595
    | ~ spl10_606 ),
    inference(unit_resulting_resolution,[],[f3393,f3475,f3490,f3497,f3504,f3579,f366])).

fof(f366,plain,
    ( ! [X4] :
        ( ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,X4))
        | r2_hidden(sK1,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X4,sK0)
        | ~ v12_waybel_0(X4,sK0)
        | ~ v1_waybel_0(X4,sK0)
        | v1_xboole_0(X4) )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f365])).

fof(f3579,plain,
    ( m1_subset_1(sK5(sK0,sK4(sK0,sK1,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_606 ),
    inference(avatar_component_clause,[],[f3578])).

fof(f3504,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_595 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f3497,plain,
    ( v1_waybel_7(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_592 ),
    inference(avatar_component_clause,[],[f3496])).

fof(f3490,plain,
    ( v12_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_590 ),
    inference(avatar_component_clause,[],[f3489])).

fof(f3475,plain,
    ( v1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_586 ),
    inference(avatar_component_clause,[],[f3474])).

fof(f3393,plain,
    ( ~ v1_xboole_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_575 ),
    inference(avatar_component_clause,[],[f3392])).

fof(f4431,plain,
    ( ~ spl10_19
    | spl10_76
    | ~ spl10_631
    | spl10_652
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_344
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f3830,f2109,f1764,f227,f217,f210,f203,f189,f182,f175,f4429,f3784,f416,f238])).

fof(f238,plain,
    ( spl10_19
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f416,plain,
    ( spl10_76
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f3784,plain,
    ( spl10_631
  <=> ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_631])])).

fof(f175,plain,
    ( spl10_1
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f182,plain,
    ( spl10_3
  <=> ~ v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f189,plain,
    ( spl10_5
  <=> ~ v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f203,plain,
    ( spl10_9
  <=> ~ v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f210,plain,
    ( spl10_11
  <=> ~ v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f217,plain,
    ( spl10_13
  <=> ~ v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1764,plain,
    ( spl10_344
  <=> r1_orders_2(sK0,sK2,k1_yellow_0(sK0,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_344])])).

fof(f2109,plain,
    ( spl10_410
  <=> ! [X1,X3,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
        | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | v2_struct_0(X0)
        | r1_orders_2(X0,X3,k1_yellow_0(X0,X2))
        | ~ r1_orders_2(X0,X3,k1_yellow_0(X0,X1))
        | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_410])])).

fof(f3830,plain,
    ( ! [X13] :
        ( ~ v3_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ r1_tarski(sK4(sK0,sK1,sK2),X13)
        | ~ m1_subset_1(k1_yellow_0(sK0,X13),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,sK2,k1_yellow_0(sK0,X13))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl10_14
    | ~ spl10_344
    | ~ spl10_410 ),
    inference(subsumption_resolution,[],[f2122,f228])).

fof(f2122,plain,
    ( ! [X13] :
        ( ~ v3_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ r1_tarski(sK4(sK0,sK1,sK2),X13)
        | ~ m1_subset_1(k1_yellow_0(sK0,X13),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,sK2,k1_yellow_0(sK0,X13))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl10_344
    | ~ spl10_410 ),
    inference(resolution,[],[f2110,f1765])).

fof(f1765,plain,
    ( r1_orders_2(sK0,sK2,k1_yellow_0(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl10_344 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f2110,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(X0,X3,k1_yellow_0(X0,X1))
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
        | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | v2_struct_0(X0)
        | r1_orders_2(X0,X3,k1_yellow_0(X0,X2))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
    | ~ spl10_410 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f3821,plain,
    ( ~ spl10_14
    | ~ spl10_68
    | spl10_631 ),
    inference(avatar_contradiction_clause,[],[f3820])).

fof(f3820,plain,
    ( $false
    | ~ spl10_14
    | ~ spl10_68
    | ~ spl10_631 ),
    inference(subsumption_resolution,[],[f228,f3791])).

fof(f3791,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_68
    | ~ spl10_631 ),
    inference(unit_resulting_resolution,[],[f3785,f391])).

fof(f391,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl10_68
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f3785,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl10_631 ),
    inference(avatar_component_clause,[],[f3784])).

fof(f3631,plain,
    ( spl10_612
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_138
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2591,f1707,f1678,f1671,f1664,f1648,f613,f234,f227,f213,f206,f199,f192,f185,f178,f3629])).

fof(f192,plain,
    ( spl10_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f199,plain,
    ( spl10_6
  <=> v2_waybel_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f206,plain,
    ( spl10_8
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f213,plain,
    ( spl10_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f613,plain,
    ( spl10_138
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f1648,plain,
    ( spl10_321
  <=> ~ v1_xboole_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_321])])).

fof(f1664,plain,
    ( spl10_324
  <=> v1_waybel_0(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_324])])).

fof(f1671,plain,
    ( spl10_326
  <=> v12_waybel_0(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_326])])).

fof(f1678,plain,
    ( spl10_329
  <=> ~ r2_hidden(sK1,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_329])])).

fof(f1707,plain,
    ( spl10_332
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_332])])).

fof(f2591,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_138
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f614])).

fof(f614,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_138 ),
    inference(avatar_component_clause,[],[f613])).

fof(f1708,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_332 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f1672,plain,
    ( v12_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_326 ),
    inference(avatar_component_clause,[],[f1671])).

fof(f1665,plain,
    ( v1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_324 ),
    inference(avatar_component_clause,[],[f1664])).

fof(f1679,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl10_329 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f1649,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl10_321 ),
    inference(avatar_component_clause,[],[f1648])).

fof(f214,plain,
    ( v2_lattice3(sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f213])).

fof(f207,plain,
    ( v1_lattice3(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f200,plain,
    ( v2_waybel_1(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f193,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f192])).

fof(f3580,plain,
    ( spl10_606
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_144
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2596,f1707,f1678,f1671,f1664,f1648,f625,f234,f227,f213,f206,f199,f192,f185,f178,f3578])).

fof(f625,plain,
    ( spl10_144
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f2596,plain,
    ( m1_subset_1(sK5(sK0,sK4(sK0,sK1,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_144
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f626])).

fof(f626,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_144 ),
    inference(avatar_component_clause,[],[f625])).

fof(f3505,plain,
    ( ~ spl10_595
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_140
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2592,f1707,f1678,f1671,f1664,f1648,f617,f234,f227,f213,f206,f199,f192,f185,f178,f3503])).

fof(f617,plain,
    ( spl10_140
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f2592,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_140
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f618])).

fof(f618,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_140 ),
    inference(avatar_component_clause,[],[f617])).

fof(f3498,plain,
    ( spl10_592
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_136
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2590,f1707,f1678,f1671,f1664,f1648,f609,f234,f227,f213,f206,f199,f192,f185,f178,f3496])).

fof(f609,plain,
    ( spl10_136
  <=> ! [X1,X0,X2] :
        ( v1_waybel_7(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f2590,plain,
    ( v1_waybel_7(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_136
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f610])).

fof(f610,plain,
    ( ! [X2,X0,X1] :
        ( v1_waybel_7(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_136 ),
    inference(avatar_component_clause,[],[f609])).

fof(f3491,plain,
    ( spl10_590
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_134
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2589,f1707,f1678,f1671,f1664,f1648,f605,f234,f227,f213,f206,f199,f192,f185,f178,f3489])).

fof(f605,plain,
    ( spl10_134
  <=> ! [X1,X0,X2] :
        ( v12_waybel_0(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f2589,plain,
    ( v12_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_134
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f606])).

fof(f606,plain,
    ( ! [X2,X0,X1] :
        ( v12_waybel_0(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f605])).

fof(f3476,plain,
    ( spl10_586
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_132
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2588,f1707,f1678,f1671,f1664,f1648,f601,f234,f227,f213,f206,f199,f192,f185,f178,f3474])).

fof(f601,plain,
    ( spl10_132
  <=> ! [X1,X0,X2] :
        ( v1_waybel_0(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f2588,plain,
    ( v1_waybel_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1),sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_132
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f602])).

fof(f602,plain,
    ( ! [X2,X0,X1] :
        ( v1_waybel_0(sK5(X0,X1,X2),X0)
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_132 ),
    inference(avatar_component_clause,[],[f601])).

fof(f3394,plain,
    ( ~ spl10_575
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_130
    | spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | spl10_329
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f2587,f1707,f1678,f1671,f1664,f1648,f597,f234,f227,f213,f206,f199,f192,f185,f178,f3392])).

fof(f597,plain,
    ( spl10_130
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f2587,plain,
    ( ~ v1_xboole_0(sK5(sK0,sK4(sK0,sK1,sK2),sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_130
    | ~ spl10_321
    | ~ spl10_324
    | ~ spl10_326
    | ~ spl10_329
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f179,f186,f193,f200,f207,f214,f228,f235,f1649,f1679,f1665,f1672,f1708,f598])).

fof(f598,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(sK5(X0,X1,X2))
        | r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_waybel_1(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_130 ),
    inference(avatar_component_clause,[],[f597])).

fof(f2111,plain,
    ( spl10_410
    | ~ spl10_114
    | ~ spl10_246 ),
    inference(avatar_split_clause,[],[f1120,f1113,f551,f2109])).

fof(f551,plain,
    ( spl10_114
  <=> ! [X1,X3,X0,X2] :
        ( r1_orders_2(X0,X1,X3)
        | ~ r1_orders_2(X0,X2,X3)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f1113,plain,
    ( spl10_246
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ l1_orders_2(X2)
        | ~ v3_lattice3(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | r1_orders_2(X2,k1_yellow_0(X2,X0),k1_yellow_0(X2,X1))
        | ~ m1_subset_1(k1_yellow_0(X2,X1),u1_struct_0(X2))
        | ~ m1_subset_1(k1_yellow_0(X2,X0),u1_struct_0(X2))
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_246])])).

fof(f1120,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
        | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | v2_struct_0(X0)
        | r1_orders_2(X0,X3,k1_yellow_0(X0,X2))
        | ~ r1_orders_2(X0,X3,k1_yellow_0(X0,X1))
        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
    | ~ spl10_114
    | ~ spl10_246 ),
    inference(duplicate_literal_removal,[],[f1117])).

fof(f1117,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
        | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | v2_struct_0(X0)
        | r1_orders_2(X0,X3,k1_yellow_0(X0,X2))
        | ~ r1_orders_2(X0,X3,k1_yellow_0(X0,X1))
        | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
        | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl10_114
    | ~ spl10_246 ),
    inference(resolution,[],[f1114,f552])).

fof(f552,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(X0,X2,X3)
        | r1_orders_2(X0,X1,X3)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl10_114 ),
    inference(avatar_component_clause,[],[f551])).

fof(f1114,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(X2,k1_yellow_0(X2,X0),k1_yellow_0(X2,X1))
        | ~ l1_orders_2(X2)
        | ~ v3_lattice3(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(X2,X1),u1_struct_0(X2))
        | ~ m1_subset_1(k1_yellow_0(X2,X0),u1_struct_0(X2))
        | v2_struct_0(X2) )
    | ~ spl10_246 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1766,plain,
    ( spl10_344
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_150
    | ~ spl10_220
    | ~ spl10_252 ),
    inference(avatar_split_clause,[],[f1174,f1135,f1015,f674,f419,f248,f241,f234,f227,f192,f185,f178,f1764])).

fof(f248,plain,
    ( spl10_21
  <=> ~ r1_waybel_3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f1015,plain,
    ( spl10_220
  <=> v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).

fof(f1135,plain,
    ( spl10_252
  <=> ! [X1,X3,X2] :
        ( r1_waybel_3(X1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v24_waybel_0(X1)
        | ~ v5_orders_2(X1)
        | ~ v4_orders_2(X1)
        | ~ v3_orders_2(X1)
        | v2_struct_0(X1)
        | r1_orders_2(X1,X3,k1_yellow_0(X1,sK4(X1,X2,X3)))
        | ~ m1_subset_1(k1_yellow_0(X1,sK4(X1,X2,X3)),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_252])])).

fof(f1174,plain,
    ( r1_orders_2(sK0,sK2,k1_yellow_0(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_150
    | ~ spl10_220
    | ~ spl10_252 ),
    inference(unit_resulting_resolution,[],[f193,f228,f420,f179,f186,f249,f235,f242,f675,f1016,f1136])).

fof(f1136,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(k1_yellow_0(X1,sK4(X1,X2,X3)),u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v24_waybel_0(X1)
        | ~ v5_orders_2(X1)
        | ~ v4_orders_2(X1)
        | ~ v3_orders_2(X1)
        | v2_struct_0(X1)
        | r1_orders_2(X1,X3,k1_yellow_0(X1,sK4(X1,X2,X3)))
        | r1_waybel_3(X1,X2,X3) )
    | ~ spl10_252 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1016,plain,
    ( v24_waybel_0(sK0)
    | ~ spl10_220 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f249,plain,
    ( ~ r1_waybel_3(sK0,sK1,sK2)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f248])).

fof(f1709,plain,
    ( spl10_332
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_124
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1171,f1015,f575,f419,f248,f241,f234,f227,f192,f185,f178,f1707])).

fof(f575,plain,
    ( spl10_124
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f1171,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_124
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f193,f228,f249,f235,f242,f1016,f576])).

fof(f576,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1680,plain,
    ( ~ spl10_329
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_122
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1170,f1015,f569,f419,f248,f241,f234,f227,f192,f185,f178,f1678])).

fof(f569,plain,
    ( spl10_122
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | ~ r2_hidden(X1,sK4(X0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f1170,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_122
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f193,f228,f249,f235,f242,f1016,f570])).

fof(f570,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,sK4(X0,X1,X2))
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_122 ),
    inference(avatar_component_clause,[],[f569])).

fof(f1673,plain,
    ( spl10_326
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_120
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1169,f1015,f565,f419,f248,f241,f234,f227,f192,f185,f178,f1671])).

fof(f565,plain,
    ( spl10_120
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | v12_waybel_0(sK4(X0,X1,X2),X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f1169,plain,
    ( v12_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_120
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f193,f228,f249,f235,f242,f1016,f566])).

fof(f566,plain,
    ( ! [X2,X0,X1] :
        ( v12_waybel_0(sK4(X0,X1,X2),X0)
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_120 ),
    inference(avatar_component_clause,[],[f565])).

fof(f1666,plain,
    ( spl10_324
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_118
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1168,f1015,f561,f419,f248,f241,f234,f227,f192,f185,f178,f1664])).

fof(f561,plain,
    ( spl10_118
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | v1_waybel_0(sK4(X0,X1,X2),X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f1168,plain,
    ( v1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_118
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f193,f228,f249,f235,f242,f1016,f562])).

fof(f562,plain,
    ( ! [X2,X0,X1] :
        ( v1_waybel_0(sK4(X0,X1,X2),X0)
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_118 ),
    inference(avatar_component_clause,[],[f561])).

fof(f1650,plain,
    ( ~ spl10_321
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | spl10_21
    | spl10_77
    | ~ spl10_116
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1167,f1015,f555,f419,f248,f241,f234,f227,f192,f185,f178,f1648])).

fof(f555,plain,
    ( spl10_116
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | ~ v1_xboole_0(sK4(X0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f1167,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_77
    | ~ spl10_116
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f420,f179,f186,f193,f228,f249,f235,f242,f1016,f556])).

fof(f556,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(sK4(X0,X1,X2))
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f555])).

fof(f1164,plain,
    ( spl10_220
    | ~ spl10_0
    | ~ spl10_12
    | ~ spl10_14
    | spl10_77
    | ~ spl10_82 ),
    inference(avatar_split_clause,[],[f453,f439,f419,f227,f220,f178,f1015])).

fof(f220,plain,
    ( spl10_12
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f439,plain,
    ( spl10_82
  <=> ! [X0] :
        ( v24_waybel_0(X0)
        | ~ v3_lattice3(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f453,plain,
    ( v24_waybel_0(sK0)
    | ~ spl10_0
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_77
    | ~ spl10_82 ),
    inference(unit_resulting_resolution,[],[f420,f179,f221,f228,f440])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | v24_waybel_0(X0) )
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f439])).

fof(f221,plain,
    ( v3_lattice3(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f1137,plain,
    ( spl10_252
    | ~ spl10_104
    | ~ spl10_126 ),
    inference(avatar_split_clause,[],[f588,f579,f524,f1135])).

fof(f524,plain,
    ( spl10_104
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f579,plain,
    ( spl10_126
  <=> ! [X1,X0,X2] :
        ( r1_waybel_3(X0,X1,X2)
        | r3_orders_2(X0,X2,k1_yellow_0(X0,sK4(X0,X1,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f588,plain,
    ( ! [X2,X3,X1] :
        ( r1_waybel_3(X1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v24_waybel_0(X1)
        | ~ v5_orders_2(X1)
        | ~ v4_orders_2(X1)
        | ~ v3_orders_2(X1)
        | v2_struct_0(X1)
        | r1_orders_2(X1,X3,k1_yellow_0(X1,sK4(X1,X2,X3)))
        | ~ m1_subset_1(k1_yellow_0(X1,sK4(X1,X2,X3)),u1_struct_0(X1)) )
    | ~ spl10_104
    | ~ spl10_126 ),
    inference(duplicate_literal_removal,[],[f587])).

fof(f587,plain,
    ( ! [X2,X3,X1] :
        ( r1_waybel_3(X1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v24_waybel_0(X1)
        | ~ v5_orders_2(X1)
        | ~ v4_orders_2(X1)
        | ~ v3_orders_2(X1)
        | v2_struct_0(X1)
        | r1_orders_2(X1,X3,k1_yellow_0(X1,sK4(X1,X2,X3)))
        | ~ m1_subset_1(k1_yellow_0(X1,sK4(X1,X2,X3)),u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ v3_orders_2(X1)
        | v2_struct_0(X1) )
    | ~ spl10_104
    | ~ spl10_126 ),
    inference(resolution,[],[f580,f525])).

fof(f525,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_orders_2(X0,X1,X2)
        | r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f524])).

fof(f580,plain,
    ( ! [X2,X0,X1] :
        ( r3_orders_2(X0,X2,k1_yellow_0(X0,sK4(X0,X1,X2)))
        | r1_waybel_3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v24_waybel_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl10_126 ),
    inference(avatar_component_clause,[],[f579])).

fof(f1115,plain,
    ( spl10_246
    | ~ spl10_104
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f547,f532,f524,f1113])).

fof(f532,plain,
    ( spl10_108
  <=> ! [X1,X0,X2] :
        ( r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f547,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ l1_orders_2(X2)
        | ~ v3_lattice3(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | r1_orders_2(X2,k1_yellow_0(X2,X0),k1_yellow_0(X2,X1))
        | ~ m1_subset_1(k1_yellow_0(X2,X1),u1_struct_0(X2))
        | ~ m1_subset_1(k1_yellow_0(X2,X0),u1_struct_0(X2))
        | v2_struct_0(X2) )
    | ~ spl10_104
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ l1_orders_2(X2)
        | ~ v3_lattice3(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | r1_orders_2(X2,k1_yellow_0(X2,X0),k1_yellow_0(X2,X1))
        | ~ m1_subset_1(k1_yellow_0(X2,X1),u1_struct_0(X2))
        | ~ m1_subset_1(k1_yellow_0(X2,X0),u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | ~ v3_orders_2(X2)
        | v2_struct_0(X2) )
    | ~ spl10_104
    | ~ spl10_108 ),
    inference(resolution,[],[f533,f525])).

fof(f533,plain,
    ( ! [X2,X0,X1] :
        ( r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl10_108 ),
    inference(avatar_component_clause,[],[f532])).

fof(f676,plain,
    ( spl10_150
    | ~ spl10_14
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f411,f390,f227,f674])).

fof(f411,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl10_14
    | ~ spl10_68 ),
    inference(unit_resulting_resolution,[],[f228,f391])).

fof(f627,plain,(
    spl10_144 ),
    inference(avatar_split_clause,[],[f145,f625])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r2_hidden(X2,sK5(X0,X1,X2))
                & r1_tarski(X1,sK5(X0,X1,X2))
                & v1_waybel_7(sK5(X0,X1,X2),X0)
                & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK5(X0,X1,X2),X0)
                & v1_waybel_0(sK5(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK5(X0,X1,X2)) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X2,sK5(X0,X1,X2))
        & r1_tarski(X1,sK5(X0,X1,X2))
        & v1_waybel_7(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK5(X0,X1,X2),X0)
        & v1_waybel_0(sK5(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ~ r2_hidden(X2,X3)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & ~ r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t28_waybel_7)).

fof(f623,plain,(
    spl10_142 ),
    inference(avatar_split_clause,[],[f140,f621])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X3,X0)
      | ~ v1_waybel_0(X3,X0)
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t20_waybel_3)).

fof(f619,plain,(
    spl10_140 ),
    inference(avatar_split_clause,[],[f148,f617])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK5(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f615,plain,(
    spl10_138 ),
    inference(avatar_split_clause,[],[f147,f613])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK5(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f611,plain,(
    spl10_136 ),
    inference(avatar_split_clause,[],[f146,f609])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK5(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f607,plain,(
    spl10_134 ),
    inference(avatar_split_clause,[],[f144,f605])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK5(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f603,plain,(
    spl10_132 ),
    inference(avatar_split_clause,[],[f143,f601])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK5(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f599,plain,(
    spl10_130 ),
    inference(avatar_split_clause,[],[f142,f597])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK5(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f581,plain,(
    spl10_126 ),
    inference(avatar_split_clause,[],[f138,f579])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | r3_orders_2(X0,X2,k1_yellow_0(X0,sK4(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ( ~ r2_hidden(X1,sK4(X0,X1,X2))
                & r3_orders_2(X0,X2,k1_yellow_0(X0,sK4(X0,X1,X2)))
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK4(X0,X1,X2),X0)
                & v1_waybel_0(sK4(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK4(X0,X1,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f84])).

fof(f84,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK4(X0,X1,X2))
        & r3_orders_2(X0,X2,k1_yellow_0(X0,sK4(X0,X1,X2)))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK4(X0,X1,X2),X0)
        & v1_waybel_0(sK4(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v24_waybel_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) )
               => r1_waybel_3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t21_waybel_3)).

fof(f577,plain,(
    spl10_124 ),
    inference(avatar_split_clause,[],[f137,f575])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f571,plain,(
    spl10_122 ),
    inference(avatar_split_clause,[],[f139,f569])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | ~ r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f567,plain,(
    spl10_120 ),
    inference(avatar_split_clause,[],[f136,f565])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | v12_waybel_0(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f563,plain,(
    spl10_118 ),
    inference(avatar_split_clause,[],[f135,f561])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | v1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f557,plain,(
    spl10_116 ),
    inference(avatar_split_clause,[],[f134,f555])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | ~ v1_xboole_0(sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f553,plain,(
    spl10_114 ),
    inference(avatar_split_clause,[],[f141,f551])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t26_orders_2)).

fof(f534,plain,(
    spl10_108 ),
    inference(avatar_split_clause,[],[f149,f532])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t3_waybel_7)).

fof(f530,plain,(
    spl10_106 ),
    inference(avatar_split_clause,[],[f168,f528])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',redefinition_r3_orders_2)).

fof(f526,plain,(
    spl10_104 ),
    inference(avatar_split_clause,[],[f167,f524])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f441,plain,(
    spl10_82 ),
    inference(avatar_split_clause,[],[f126,f439])).

fof(f126,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',cc11_waybel_0)).

fof(f421,plain,
    ( ~ spl10_77
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f387,f349,f227,f213,f419])).

fof(f349,plain,
    ( spl10_52
  <=> ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f387,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_52 ),
    inference(unit_resulting_resolution,[],[f228,f214,f350])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ v2_lattice3(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f349])).

fof(f392,plain,(
    spl10_68 ),
    inference(avatar_split_clause,[],[f157,f390])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',dt_k1_yellow_0)).

fof(f367,plain,
    ( spl10_58
    | spl10_21 ),
    inference(avatar_split_clause,[],[f257,f248,f365])).

fof(f257,plain,
    ( ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X4,sK0)
        | ~ v12_waybel_0(X4,sK0)
        | ~ v1_waybel_0(X4,sK0)
        | v1_xboole_0(X4) )
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f108,f249])).

fof(f108,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_7(X4,sK0)
      | ~ v12_waybel_0(X4,sK0)
      | ~ v1_waybel_0(X4,sK0)
      | v1_xboole_0(X4)
      | r1_waybel_3(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_waybel_7(sK3,sK0)
        & v12_waybel_0(sK3,sK0)
        & v1_waybel_0(sK3,sK0)
        & ~ v1_xboole_0(sK3) )
      | ~ r1_waybel_3(sK0,sK1,sK2) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r3_orders_2(sK0,sK2,k1_yellow_0(sK0,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v1_waybel_7(X4,sK0)
          | ~ v12_waybel_0(X4,sK0)
          | ~ v1_waybel_0(X4,sK0)
          | v1_xboole_0(X4) )
      | r1_waybel_3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v2_waybel_1(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f78,f82,f81,f80,f79])).

fof(f79,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                  | ~ r1_waybel_3(X0,X1,X2) )
                & ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v1_waybel_7(X4,X0)
                      | ~ v12_waybel_0(X4,X0)
                      | ~ v1_waybel_0(X4,X0)
                      | v1_xboole_0(X4) )
                  | r1_waybel_3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(sK0,X2,k1_yellow_0(sK0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                    & v1_waybel_7(X3,sK0)
                    & v12_waybel_0(X3,sK0)
                    & v1_waybel_0(X3,sK0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(sK0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(sK0,X2,k1_yellow_0(sK0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                    | ~ v1_waybel_7(X4,sK0)
                    | ~ v12_waybel_0(X4,sK0)
                    | ~ v1_waybel_0(X4,sK0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v2_waybel_1(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X4,X0)
                    | ~ v12_waybel_0(X4,X0)
                    | ~ v1_waybel_0(X4,X0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(sK1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,sK1,X2) )
            & ( ! [X4] :
                  ( r2_hidden(sK1,X4)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X4,X0)
                  | ~ v12_waybel_0(X4,X0)
                  | ~ v1_waybel_0(X4,X0)
                  | v1_xboole_0(X4) )
              | r1_waybel_3(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X1,X3)
                & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X3,X0)
                & v12_waybel_0(X3,X0)
                & v1_waybel_0(X3,X0)
                & ~ v1_xboole_0(X3) )
            | ~ r1_waybel_3(X0,X1,X2) )
          & ( ! [X4] :
                ( r2_hidden(X1,X4)
                | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_waybel_7(X4,X0)
                | ~ v12_waybel_0(X4,X0)
                | ~ v1_waybel_0(X4,X0)
                | v1_xboole_0(X4) )
            | r1_waybel_3(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r3_orders_2(X0,sK2,k1_yellow_0(X0,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X3,X0)
              & v12_waybel_0(X3,X0)
              & v1_waybel_0(X3,X0)
              & ~ v1_xboole_0(X3) )
          | ~ r1_waybel_3(X0,X1,sK2) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r3_orders_2(X0,sK2,k1_yellow_0(X0,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X4,X0)
              | ~ v12_waybel_0(X4,X0)
              | ~ v1_waybel_0(X4,X0)
              | v1_xboole_0(X4) )
          | r1_waybel_3(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK3)
        & r3_orders_2(X0,X2,k1_yellow_0(X0,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK3,X0)
        & v12_waybel_0(sK3,X0)
        & v1_waybel_0(sK3,X0)
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X4,X0)
                    | ~ v12_waybel_0(X4,X0)
                    | ~ v1_waybel_0(X4,X0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_waybel_3(X0,X1,X2)
                <=> ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v1_waybel_7(X3,X0)
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
              <=> ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',t36_waybel_7)).

fof(f351,plain,(
    spl10_52 ),
    inference(avatar_split_clause,[],[f119,f349])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t36_waybel_7.p',cc2_lattice3)).

fof(f320,plain,
    ( ~ spl10_21
    | spl10_40 ),
    inference(avatar_split_clause,[],[f114,f318,f248])).

fof(f114,plain,
    ( r3_orders_2(sK0,sK2,k1_yellow_0(sK0,sK3))
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f313,plain,
    ( ~ spl10_21
    | spl10_38 ),
    inference(avatar_split_clause,[],[f113,f311,f248])).

fof(f113,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f285,plain,
    ( ~ spl10_21
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f115,f283,f248])).

fof(f115,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f271,plain,
    ( ~ spl10_21
    | spl10_26 ),
    inference(avatar_split_clause,[],[f111,f269,f248])).

fof(f111,plain,
    ( v12_waybel_0(sK3,sK0)
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f264,plain,
    ( ~ spl10_21
    | spl10_24 ),
    inference(avatar_split_clause,[],[f110,f262,f248])).

fof(f110,plain,
    ( v1_waybel_0(sK3,sK0)
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f256,plain,
    ( ~ spl10_21
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f109,f254,f248])).

fof(f109,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ r1_waybel_3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

fof(f243,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f107,f241])).

fof(f107,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f236,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f106,f234])).

fof(f106,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f229,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f105,f227])).

fof(f105,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f222,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f104,f220])).

fof(f104,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f215,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f103,f213])).

fof(f103,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f208,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f102,f206])).

fof(f102,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f201,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f101,f199])).

fof(f101,plain,(
    v2_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f194,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f100,f192])).

fof(f100,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f187,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f99,f185])).

fof(f99,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f180,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f98,f178])).

fof(f98,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------
